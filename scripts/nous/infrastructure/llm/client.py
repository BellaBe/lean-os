"""
LLM Client Infrastructure

Handles LLM interactions for:
1. Schema generation (one-time cost for SERP extraction)
2. Idea extraction from content

Supports Groq API with adaptive rate limiting.
"""

import asyncio
import json
import os
import time
from dataclasses import dataclass, field
from typing import Any

from ..crawlers.schema_manager import SchemaConfig, SchemaGenerator

# Groq model presets with known rate limits (free tier)
GROQ_MODEL_LIMITS = {
    "llama-3.1-8b-instant": {"rpm": 30, "rpd": 14400, "tpm": 6000, "tpd": 500000},
    "llama-3.3-70b-versatile": {"rpm": 30, "rpd": 1000, "tpm": 12000, "tpd": 100000},
    "llama-3.1-70b-versatile": {"rpm": 30, "rpd": 1000, "tpm": 6000, "tpd": 100000},
    "llama3-8b-8192": {"rpm": 30, "rpd": 14400, "tpm": 6000, "tpd": 500000},
    "llama3-70b-8192": {"rpm": 30, "rpd": 14400, "tpm": 6000, "tpd": 100000},
    "gemma2-9b-it": {"rpm": 30, "rpd": 14400, "tpm": 15000, "tpd": 500000},
    "mixtral-8x7b-32768": {"rpm": 30, "rpd": 14400, "tpm": 5000, "tpd": 500000},
}


@dataclass
class RateLimitState:
    """Tracks rate limit state from API response headers."""

    # Request limits
    limit_requests: int = 30  # RPM default
    remaining_requests: int = 30
    reset_requests_at: float = 0.0  # Unix timestamp

    # Token limits
    limit_tokens: int = 6000  # TPM default
    remaining_tokens: int = 6000
    reset_tokens_at: float = 0.0  # Unix timestamp

    # Tracking
    last_updated: float = field(default_factory=time.time)


class RateLimiter:
    """
    Adaptive rate limiter using Groq API response headers.

    Features:
    - Parses x-ratelimit-* headers from responses
    - Proactively throttles when approaching limits
    - Exponential backoff on 429 errors
    """

    def __init__(
        self,
        min_remaining_requests: int = 3,
        min_remaining_tokens: int = 500,
        max_retries: int = 5,
        base_backoff: float = 1.0,
    ):
        """
        Args:
            min_remaining_requests: Throttle when remaining requests below this
            min_remaining_tokens: Throttle when remaining tokens below this
            max_retries: Maximum retry attempts on 429
            base_backoff: Base delay for exponential backoff (seconds)
        """
        self.min_remaining_requests = min_remaining_requests
        self.min_remaining_tokens = min_remaining_tokens
        self.max_retries = max_retries
        self.base_backoff = base_backoff
        self.state = RateLimitState()
        self._lock = asyncio.Lock()

    def update_from_headers(self, headers: dict[str, str]) -> None:
        """
        Update rate limit state from API response headers.

        Headers parsed:
        - x-ratelimit-limit-requests
        - x-ratelimit-remaining-requests
        - x-ratelimit-reset-requests
        - x-ratelimit-limit-tokens
        - x-ratelimit-remaining-tokens
        - x-ratelimit-reset-tokens
        """
        now = time.time()

        if "x-ratelimit-limit-requests" in headers:
            self.state.limit_requests = int(headers["x-ratelimit-limit-requests"])
        if "x-ratelimit-remaining-requests" in headers:
            self.state.remaining_requests = int(headers["x-ratelimit-remaining-requests"])
        if "x-ratelimit-reset-requests" in headers:
            # Parse reset time (could be duration or timestamp)
            reset_val = headers["x-ratelimit-reset-requests"]
            self.state.reset_requests_at = self._parse_reset_time(reset_val, now)

        if "x-ratelimit-limit-tokens" in headers:
            self.state.limit_tokens = int(headers["x-ratelimit-limit-tokens"])
        if "x-ratelimit-remaining-tokens" in headers:
            self.state.remaining_tokens = int(headers["x-ratelimit-remaining-tokens"])
        if "x-ratelimit-reset-tokens" in headers:
            reset_val = headers["x-ratelimit-reset-tokens"]
            self.state.reset_tokens_at = self._parse_reset_time(reset_val, now)

        self.state.last_updated = now

    def _parse_reset_time(self, value: str, now: float) -> float:
        """Parse reset time from header (handles duration strings like '1m30s')."""
        try:
            # Try as numeric seconds first
            return now + float(value)
        except ValueError:
            pass

        # Parse duration string (e.g., "1m30s", "45s", "2m")
        total_seconds = 0.0
        current_num = ""

        for char in value:
            if char.isdigit() or char == ".":
                current_num += char
            elif char == "h" and current_num:
                total_seconds += float(current_num) * 3600
                current_num = ""
            elif char == "m" and current_num:
                total_seconds += float(current_num) * 60
                current_num = ""
            elif char == "s" and current_num:
                total_seconds += float(current_num)
                current_num = ""
            elif char == "m" and not current_num:
                # Milliseconds suffix (ms)
                pass

        return now + total_seconds if total_seconds > 0 else now + 60

    async def wait_if_needed(self) -> None:
        """
        Proactively wait if approaching rate limits.

        Called before making a request to avoid hitting limits.
        """
        async with self._lock:
            now = time.time()

            # Check if we need to wait for request limit reset
            if self.state.remaining_requests <= self.min_remaining_requests:
                if self.state.reset_requests_at > now:
                    wait_time = self.state.reset_requests_at - now
                    await asyncio.sleep(min(wait_time, 60))  # Cap at 60s
                    return

            # Check if we need to wait for token limit reset
            if self.state.remaining_tokens <= self.min_remaining_tokens:
                if self.state.reset_tokens_at > now:
                    wait_time = self.state.reset_tokens_at - now
                    await asyncio.sleep(min(wait_time, 60))  # Cap at 60s
                    return

    async def handle_rate_limit_error(
        self,
        attempt: int,
        retry_after: float | None = None,
    ) -> bool:
        """
        Handle 429 rate limit error with exponential backoff.

        Args:
            attempt: Current retry attempt (0-indexed)
            retry_after: Value from retry-after header (seconds)

        Returns:
            True if should retry, False if max retries exceeded
        """
        if attempt >= self.max_retries:
            return False

        if retry_after is not None:
            wait_time = retry_after
        else:
            # Exponential backoff: 1s, 2s, 4s, 8s, 16s...
            wait_time = self.base_backoff * (2**attempt)

        # Add jitter to prevent thundering herd
        jitter = wait_time * 0.1 * (hash(time.time()) % 10) / 10
        wait_time += jitter

        await asyncio.sleep(min(wait_time, 120))  # Cap at 2 minutes
        return True

    def estimate_tokens(self, text: str) -> int:
        """Rough token estimation (~4 chars per token for English)."""
        return len(text) // 4


@dataclass
class LLMConfig:
    """Configuration for LLM client."""

    provider: str = "groq/llama-3.1-8b-instant"  # Default to Groq free tier
    api_key: str | None = None
    base_url: str | None = None
    temperature: float = 0.0
    max_tokens: int = 4000

    # Rate limiting
    enable_rate_limiting: bool = True
    min_remaining_requests: int = 3
    min_remaining_tokens: int = 500

    @classmethod
    def from_env(cls, provider: str | None = None) -> "LLMConfig":
        """Create config from environment variables."""
        return cls(
            provider=provider or os.getenv("LLM_PROVIDER", "groq/llama-3.1-8b-instant"),
            api_key=os.getenv("GROQ_API_KEY") or os.getenv("LLM_API_KEY"),
            base_url=os.getenv("LLM_BASE_URL"),
        )

    @classmethod
    def groq(cls, model: str = "llama-3.1-8b-instant") -> "LLMConfig":
        """Create Groq-specific config."""
        return cls(
            provider=f"groq/{model}",
            api_key=os.getenv("GROQ_API_KEY"),
            enable_rate_limiting=True,
        )

    @classmethod
    def groq_fast(cls) -> "LLMConfig":
        """Groq config optimized for speed (smaller model)."""
        return cls.groq("llama-3.1-8b-instant")

    @classmethod
    def groq_quality(cls) -> "LLMConfig":
        """Groq config optimized for quality (larger model)."""
        return cls.groq("llama-3.3-70b-versatile")


class Crawl4AISchemaGenerator(SchemaGenerator):
    """
    Schema generator using Crawl4AI's built-in LLM schema generation.

    This uses LLM ONCE to create CSS extraction schemas that can then
    be reused for fast, LLM-free extractions.
    """

    def __init__(self, config: LLMConfig):
        self.config = config

    async def generate(
        self,
        html: str,
        config: SchemaConfig,
    ) -> dict[str, Any]:
        """
        Generate CSS extraction schema from HTML sample.

        Args:
            html: Sample HTML containing the pattern to extract
            config: Schema configuration with target structure

        Returns:
            CSS extraction schema for JsonCssExtractionStrategy
        """
        try:
            from crawl4ai import JsonCssExtractionStrategy
            from crawl4ai import LLMConfig as C4ALLMConfig

            llm_config = C4ALLMConfig(
                provider=self.config.provider,
                api_token=self.config.api_key,
            )

            schema = JsonCssExtractionStrategy.generate_schema(
                html,
                llm_config=llm_config,
                query=config.query,
                target_json=config.target_json_example,
            )

            return schema

        except ImportError:
            raise ImportError("crawl4ai not installed. Run: pip install crawl4ai")
        except Exception as e:
            raise RuntimeError(f"Schema generation failed: {e}")


class RateLimitError(Exception):
    """Raised when rate limit is exceeded and retries exhausted."""

    def __init__(self, message: str, retry_after: float | None = None):
        super().__init__(message)
        self.retry_after = retry_after


class DirectLLMClient:
    """
    Direct LLM client for custom prompts (e.g., idea extraction).

    Uses LiteLLM under the hood for provider abstraction.
    Includes adaptive rate limiting for Groq API.
    """

    def __init__(self, config: LLMConfig):
        self.config = config
        self._rate_limiter: RateLimiter | None = None

        if config.enable_rate_limiting:
            self._rate_limiter = RateLimiter(
                min_remaining_requests=config.min_remaining_requests,
                min_remaining_tokens=config.min_remaining_tokens,
            )

    async def complete(
        self,
        prompt: str,
        system_prompt: str | None = None,
    ) -> str:
        """
        Get completion from LLM with rate limiting and retry logic.

        Args:
            prompt: User prompt
            system_prompt: Optional system prompt

        Returns:
            LLM response text

        Raises:
            RateLimitError: If rate limit exceeded and retries exhausted
            ImportError: If litellm not installed
        """
        try:
            import litellm
        except ImportError:
            raise ImportError("litellm not installed. Run: pip install litellm")

        messages: list[dict[str, str]] = []
        if system_prompt:
            messages.append({"role": "system", "content": system_prompt})
        messages.append({"role": "user", "content": prompt})

        # Retry loop with rate limiting
        max_attempts = self._rate_limiter.max_retries + 1 if self._rate_limiter else 1

        for attempt in range(max_attempts):
            try:
                # Proactive throttling
                if self._rate_limiter:
                    await self._rate_limiter.wait_if_needed()

                response = await litellm.acompletion(
                    model=self.config.provider,
                    messages=messages,
                    api_key=self.config.api_key,
                    temperature=self.config.temperature,
                    max_tokens=self.config.max_tokens,
                )

                # Update rate limiter from response headers
                if self._rate_limiter and hasattr(response, "_hidden_params"):
                    headers = response._hidden_params.get("additional_headers", {})
                    if headers:
                        self._rate_limiter.update_from_headers(headers)

                # LiteLLM response has choices[0].message.content (type: ignore for union type)
                content = response.choices[0].message.content  # type: ignore[union-attr]
                return content if content is not None else ""

            except Exception as e:
                error_str = str(e).lower()

                # Check for rate limit error (429)
                if "429" in error_str or "rate limit" in error_str:
                    if self._rate_limiter:
                        # Extract retry-after if available
                        retry_after = self._extract_retry_after(e)

                        should_retry = await self._rate_limiter.handle_rate_limit_error(
                            attempt, retry_after
                        )

                        if should_retry:
                            continue

                    raise RateLimitError(
                        f"Rate limit exceeded after {attempt + 1} attempts: {e}",
                        retry_after=self._extract_retry_after(e),
                    )

                # Re-raise non-rate-limit errors
                raise

        raise RateLimitError(f"Rate limit exceeded after {max_attempts} attempts")

    def _extract_retry_after(self, error: Exception) -> float | None:
        """Extract retry-after value from error if available."""
        error_str = str(error)

        # Try to find retry-after in error message
        if "retry-after" in error_str.lower():
            import re

            match = re.search(r"retry-after[:\s]+(\d+(?:\.\d+)?)", error_str.lower())
            if match:
                return float(match.group(1))

        # Check for error attributes (some SDKs include headers)
        if hasattr(error, "headers"):
            headers = getattr(error, "headers", {})
            if "retry-after" in headers:
                try:
                    return float(headers["retry-after"])
                except (ValueError, TypeError):
                    pass

        return None

    async def extract_json(
        self,
        prompt: str,
        system_prompt: str | None = None,
    ) -> Any:
        """
        Get JSON response from LLM.

        Args:
            prompt: User prompt (should request JSON output)
            system_prompt: Optional system prompt

        Returns:
            Parsed JSON response (dict or list)
        """
        response = await self.complete(prompt, system_prompt)

        # Try to extract JSON from response
        try:
            # Handle markdown code blocks
            if "```json" in response:
                start = response.find("```json") + 7
                end = response.find("```", start)
                response = response[start:end]
            elif "```" in response:
                start = response.find("```") + 3
                end = response.find("```", start)
                response = response[start:end]

            return json.loads(response.strip())
        except json.JSONDecodeError as e:
            raise ValueError(
                f"Failed to parse LLM response as JSON: {e}\nResponse: {response[:500]}"
            )


# Idea extraction prompts
IDEA_EXTRACTION_SYSTEM_PROMPT = """You are an expert at extracting key ideas, claims, and arguments from text.

Your task is to identify distinct IDEAS from the content. An idea is:
- A specific claim or argument
- A position or stance on a topic
- A prediction or forecast
- A recommendation or suggestion

For each idea, identify:
1. The core claim (1-2 sentences)
2. The stance (support, oppose, neutral) toward the main topic
3. Evidence or reasoning cited
4. Confidence level (how strongly the source asserts this)

Output as JSON array of ideas."""

IDEA_EXTRACTION_PROMPT_TEMPLATE = """Topic: {topic}

Content to analyze:
{content}

Extract all distinct ideas/claims from this content related to the topic.

Return JSON array:
[
  {{
    "claim": "The specific claim or argument",
    "stance": "support" | "oppose" | "neutral",
    "evidence": "Any supporting evidence cited",
    "confidence": 0.0 to 1.0,
    "behavioral_triggers": ["any action-oriented implications"]
  }}
]

Only include ideas directly relevant to the topic. Be specific, not vague."""


class IdeaExtractor:
    """Extracts ideas from content using LLM."""

    def __init__(self, llm_client: DirectLLMClient):
        self.llm = llm_client

    async def extract(
        self,
        content: str,
        topic: str,
        max_ideas: int = 10,
    ) -> list[dict[str, Any]]:
        """
        Extract ideas from content.

        Args:
            content: Text content to analyze
            topic: Topic context for extraction
            max_ideas: Maximum number of ideas to extract

        Returns:
            List of extracted ideas
        """
        # Truncate content if too long
        if len(content) > 8000:
            content = content[:8000] + "..."

        prompt = IDEA_EXTRACTION_PROMPT_TEMPLATE.format(
            topic=topic,
            content=content,
        )

        try:
            ideas = await self.llm.extract_json(
                prompt,
                IDEA_EXTRACTION_SYSTEM_PROMPT,
            )

            if isinstance(ideas, list):
                return ideas[:max_ideas]
            return []

        except Exception as e:
            print(f"Idea extraction failed: {e}")
            return []
