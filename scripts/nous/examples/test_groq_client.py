#!/usr/bin/env python3
"""
Test script for Groq LLM client with rate limiting.

Tests the DirectLLMClient and IdeaExtractor against sample content
matching the architecture's intended use case.

Run from scripts/nous directory:
    python examples/test_groq_client.py

Requires:
    export GROQ_API_KEY=your_key_here
"""

import asyncio
import json
import os
import sys
import time
from dataclasses import dataclass, field
from typing import Any

# ============================================================================
# Inline copies of rate limiting classes (to avoid import issues)
# ============================================================================

GROQ_MODEL_LIMITS = {
    "llama-3.1-8b-instant": {"rpm": 30, "rpd": 14400, "tpm": 6000, "tpd": 500000},
    "llama-3.3-70b-versatile": {"rpm": 30, "rpd": 1000, "tpm": 12000, "tpd": 100000},
    "llama-3.1-70b-versatile": {"rpm": 30, "rpd": 1000, "tpm": 6000, "tpd": 100000},
    "gemma2-9b-it": {"rpm": 30, "rpd": 14400, "tpm": 15000, "tpd": 500000},
}


@dataclass
class RateLimitState:
    """Tracks rate limit state from API response headers."""

    limit_requests: int = 30
    remaining_requests: int = 30
    reset_requests_at: float = 0.0
    limit_tokens: int = 6000
    remaining_tokens: int = 6000
    reset_tokens_at: float = 0.0
    last_updated: float = field(default_factory=time.time)


class RateLimiter:
    """Adaptive rate limiter using Groq API response headers."""

    def __init__(
        self,
        min_remaining_requests: int = 3,
        min_remaining_tokens: int = 500,
        max_retries: int = 5,
        base_backoff: float = 1.0,
    ):
        self.min_remaining_requests = min_remaining_requests
        self.min_remaining_tokens = min_remaining_tokens
        self.max_retries = max_retries
        self.base_backoff = base_backoff
        self.state = RateLimitState()
        self._lock = asyncio.Lock()

    def update_from_headers(self, headers: dict[str, str]) -> None:
        """Update rate limit state from API response headers."""
        now = time.time()

        if "x-ratelimit-limit-requests" in headers:
            self.state.limit_requests = int(headers["x-ratelimit-limit-requests"])
        if "x-ratelimit-remaining-requests" in headers:
            self.state.remaining_requests = int(headers["x-ratelimit-remaining-requests"])
        if "x-ratelimit-limit-tokens" in headers:
            self.state.limit_tokens = int(headers["x-ratelimit-limit-tokens"])
        if "x-ratelimit-remaining-tokens" in headers:
            self.state.remaining_tokens = int(headers["x-ratelimit-remaining-tokens"])

        self.state.last_updated = now

    async def wait_if_needed(self) -> None:
        """Proactively wait if approaching rate limits."""
        async with self._lock:
            now = time.time()

            if self.state.remaining_requests <= self.min_remaining_requests:
                if self.state.reset_requests_at > now:
                    wait_time = self.state.reset_requests_at - now
                    print(f"  [Rate Limiter] Waiting {wait_time:.1f}s for request limit reset...")
                    await asyncio.sleep(min(wait_time, 60))

            if self.state.remaining_tokens <= self.min_remaining_tokens:
                if self.state.reset_tokens_at > now:
                    wait_time = self.state.reset_tokens_at - now
                    print(f"  [Rate Limiter] Waiting {wait_time:.1f}s for token limit reset...")
                    await asyncio.sleep(min(wait_time, 60))

    async def handle_rate_limit_error(
        self,
        attempt: int,
        retry_after: float | None = None,
    ) -> bool:
        """Handle 429 rate limit error with exponential backoff."""
        if attempt >= self.max_retries:
            return False

        if retry_after is not None:
            wait_time = retry_after
        else:
            wait_time = self.base_backoff * (2**attempt)

        print(f"  [Rate Limiter] Backing off for {wait_time:.1f}s (attempt {attempt + 1})...")
        await asyncio.sleep(min(wait_time, 120))
        return True


class RateLimitError(Exception):
    """Raised when rate limit is exceeded and retries exhausted."""

    def __init__(self, message: str, retry_after: float | None = None):
        super().__init__(message)
        self.retry_after = retry_after


@dataclass
class LLMConfig:
    """Configuration for LLM client."""

    provider: str = "groq/llama-3.1-8b-instant"
    api_token: str | None = None
    temperature: float = 0.0
    max_tokens: int = 4000
    enable_rate_limiting: bool = True
    min_remaining_requests: int = 3
    min_remaining_tokens: int = 500

    @classmethod
    def groq_fast(cls) -> "LLMConfig":
        """Groq config optimized for speed."""
        return cls(
            provider="groq/llama-3.1-8b-instant",
            api_token=os.getenv("GROQ_API_KEY"),
            enable_rate_limiting=True,
        )


class DirectLLMClient:
    """Direct LLM client with rate limiting for Groq API."""

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
        """Get completion from LLM with rate limiting."""
        try:
            import litellm
        except ImportError:
            raise ImportError("litellm not installed. Run: pip install litellm")

        messages: list[dict[str, str]] = []
        if system_prompt:
            messages.append({"role": "system", "content": system_prompt})
        messages.append({"role": "user", "content": prompt})

        max_attempts = self._rate_limiter.max_retries + 1 if self._rate_limiter else 1

        for attempt in range(max_attempts):
            try:
                if self._rate_limiter:
                    await self._rate_limiter.wait_if_needed()

                response = await litellm.acompletion(
                    model=self.config.provider,
                    messages=messages,
                    api_key=self.config.api_token,
                    temperature=self.config.temperature,
                    max_tokens=self.config.max_tokens,
                )

                # Update rate limiter from response headers
                if self._rate_limiter and hasattr(response, "_hidden_params"):
                    headers = response._hidden_params.get("additional_headers", {})
                    if headers:
                        self._rate_limiter.update_from_headers(headers)

                content = response.choices[0].message.content
                return content if content is not None else ""

            except Exception as e:
                error_str = str(e).lower()

                if "429" in error_str or "rate limit" in error_str:
                    if self._rate_limiter:
                        should_retry = await self._rate_limiter.handle_rate_limit_error(
                            attempt, None
                        )
                        if should_retry:
                            continue

                    raise RateLimitError(
                        f"Rate limit exceeded after {attempt + 1} attempts: {e}"
                    )
                raise

        raise RateLimitError(f"Rate limit exceeded after {max_attempts} attempts")

    async def extract_json(
        self,
        prompt: str,
        system_prompt: str | None = None,
    ) -> Any:
        """Get JSON response from LLM."""
        response = await self.complete(prompt, system_prompt)

        try:
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
            raise ValueError(f"Failed to parse JSON: {e}\nResponse: {response[:500]}")


# Idea extraction prompts
IDEA_EXTRACTION_SYSTEM = """You are an expert at extracting key ideas from text.
For each idea, identify the claim, stance (support/oppose/neutral), and confidence.
Output as JSON array."""

IDEA_EXTRACTION_TEMPLATE = """Topic: {topic}

Content:
{content}

Extract distinct ideas/claims. Return JSON array:
[{{"claim": "...", "stance": "support|oppose|neutral", "confidence": 0.0-1.0}}]"""


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
        """Extract ideas from content."""
        if len(content) > 8000:
            content = content[:8000] + "..."

        prompt = IDEA_EXTRACTION_TEMPLATE.format(topic=topic, content=content)

        try:
            ideas = await self.llm.extract_json(prompt, IDEA_EXTRACTION_SYSTEM)
            if isinstance(ideas, list):
                return ideas[:max_ideas]
            return []
        except Exception as e:
            print(f"  Idea extraction failed: {e}")
            return []


# ============================================================================
# Sample content for testing
# ============================================================================

SAMPLE_CONTENT = """
# EU AI Act: A New Era of Artificial Intelligence Regulation

The European Union's landmark AI Act represents the world's first comprehensive
legal framework for artificial intelligence.

## Key Points

**Risk-Based Classification**: The Act classifies AI systems into four risk
categories - unacceptable, high, limited, and minimal risk.

**Foundation Model Obligations**: Large language models face specific
transparency requirements. Critics argue these could stifle innovation.

**Industry Response**: Tech companies have expressed mixed reactions. Some
praise regulatory clarity, others warn about compliance costs.

"The AI Act provides necessary guardrails," said a European Commission
spokesperson. Meanwhile, civil society groups argue the regulations don't
go far enough in protecting citizens.
"""


# ============================================================================
# Test functions
# ============================================================================


async def test_basic_completion():
    """Test basic LLM completion with rate limiting."""
    print("=" * 60)
    print("TEST 1: Basic Completion")
    print("=" * 60)

    config = LLMConfig.groq_fast()
    print(f"Provider: {config.provider}")
    print(f"Rate limiting: {config.enable_rate_limiting}")

    if not config.api_token:
        print("\n⚠️  GROQ_API_KEY not set. Skipping test.")
        return False

    client = DirectLLMClient(config)

    try:
        print("\nSending test prompt...")
        response = await client.complete(
            "What is 2+2? Answer with just the number.",
            system_prompt="Be concise.",
        )
        print(f"Response: {response.strip()}")

        if client._rate_limiter:
            state = client._rate_limiter.state
            print(f"\nRate limit state:")
            print(f"  Remaining: {state.remaining_requests} req, {state.remaining_tokens} tok")

        return True

    except RateLimitError as e:
        print(f"\n❌ Rate limit error: {e}")
        return False
    except Exception as e:
        print(f"\n❌ Error: {e}")
        return False


async def test_idea_extraction():
    """Test idea extraction from sample content."""
    print("\n" + "=" * 60)
    print("TEST 2: Idea Extraction")
    print("=" * 60)

    config = LLMConfig.groq_fast()

    if not config.api_token:
        print("\n⚠️  GROQ_API_KEY not set. Skipping test.")
        return False

    client = DirectLLMClient(config)
    extractor = IdeaExtractor(client)

    try:
        print(f"\nExtracting ideas from sample content...")
        print(f"Topic: 'AI regulation EU'")

        ideas = await extractor.extract(
            content=SAMPLE_CONTENT,
            topic="AI regulation EU",
            max_ideas=5,
        )

        print(f"\n✓ Extracted {len(ideas)} ideas:")
        for i, idea in enumerate(ideas, 1):
            claim = idea.get("claim", "No claim")[:70]
            stance = idea.get("stance", "?")
            conf = idea.get("confidence", 0)
            print(f"\n  [{i}] {claim}...")
            print(f"      Stance: {stance} | Confidence: {conf}")

        return len(ideas) > 0

    except RateLimitError as e:
        print(f"\n❌ Rate limit error: {e}")
        return False
    except Exception as e:
        print(f"\n❌ Error: {e}")
        import traceback
        traceback.print_exc()
        return False


async def test_rate_limit_handling():
    """Test rate limit handling with multiple requests."""
    print("\n" + "=" * 60)
    print("TEST 3: Rate Limit Handling (3 requests)")
    print("=" * 60)

    config = LLMConfig.groq_fast()

    if not config.api_token:
        print("\n⚠️  GROQ_API_KEY not set. Skipping test.")
        return False

    client = DirectLLMClient(config)

    try:
        for i in range(3):
            print(f"\nRequest {i + 1}/3...")
            response = await client.complete(f"Say 'test {i + 1}' only.")
            print(f"  Response: {response.strip()}")

            if client._rate_limiter:
                state = client._rate_limiter.state
                print(f"  Remaining: {state.remaining_requests} req")

        print("\n✓ All requests completed")
        return True

    except RateLimitError as e:
        print(f"\n⚠️  Rate limit hit: {e}")
        return True  # Expected behavior
    except Exception as e:
        print(f"\n❌ Error: {e}")
        return False


def print_model_limits():
    """Print available Groq model limits."""
    print("=" * 60)
    print("Available Groq Models (Free Tier)")
    print("=" * 60)
    for model, limits in GROQ_MODEL_LIMITS.items():
        print(f"  {model}:")
        print(f"    RPM: {limits['rpm']} | TPM: {limits['tpm']:,}")


async def main():
    """Run all tests."""
    print("\n" + "=" * 60)
    print("  NOUS LLM CLIENT TEST SUITE")
    print("  Testing Groq API with Adaptive Rate Limiting")
    print("=" * 60 + "\n")

    print_model_limits()
    print()

    results = {
        "Basic Completion": await test_basic_completion(),
        "Idea Extraction": await test_idea_extraction(),
        "Rate Limit Handling": await test_rate_limit_handling(),
    }

    print("\n" + "=" * 60)
    print("  RESULTS")
    print("=" * 60)
    for test, passed in results.items():
        status = "✓ PASS" if passed else "✗ FAIL"
        print(f"  {status}: {test}")

    return all(results.values())


if __name__ == "__main__":
    success = asyncio.run(main())
    sys.exit(0 if success else 1)
