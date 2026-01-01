#!/usr/bin/env python3
"""
Real-world test of Nous LLM client.

Fetches actual content from the web and extracts ideas using Groq API.
This tests the full pipeline as described in architecture.md.
"""

import asyncio
import json
import os
import sys
import time
from dataclasses import dataclass, field
from typing import Any
from urllib.request import urlopen, Request
from html.parser import HTMLParser


# ============================================================================
# Simple HTML to text converter
# ============================================================================

class HTMLTextExtractor(HTMLParser):
    """Extract text from HTML."""

    def __init__(self):
        super().__init__()
        self.text_parts = []
        self.skip_tags = {'script', 'style', 'nav', 'footer', 'header'}
        self.current_skip = 0

    def handle_starttag(self, tag, attrs):
        if tag in self.skip_tags:
            self.current_skip += 1

    def handle_endtag(self, tag):
        if tag in self.skip_tags and self.current_skip > 0:
            self.current_skip -= 1

    def handle_data(self, data):
        if self.current_skip == 0:
            text = data.strip()
            if text:
                self.text_parts.append(text)

    def get_text(self) -> str:
        return ' '.join(self.text_parts)


def html_to_text(html: str) -> str:
    """Convert HTML to plain text."""
    parser = HTMLTextExtractor()
    parser.feed(html)
    return parser.get_text()


def fetch_url(url: str) -> str:
    """Fetch URL content."""
    headers = {
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
    }
    req = Request(url, headers=headers)
    with urlopen(req, timeout=15) as response:
        return response.read().decode('utf-8', errors='ignore')


# ============================================================================
# Rate limiting classes (from client.py)
# ============================================================================

@dataclass
class RateLimitState:
    limit_requests: int = 30
    remaining_requests: int = 30
    reset_requests_at: float = 0.0
    limit_tokens: int = 6000
    remaining_tokens: int = 6000
    reset_tokens_at: float = 0.0
    last_updated: float = field(default_factory=time.time)


class RateLimiter:
    def __init__(self, min_remaining_requests: int = 3, min_remaining_tokens: int = 500,
                 max_retries: int = 5, base_backoff: float = 1.0):
        self.min_remaining_requests = min_remaining_requests
        self.min_remaining_tokens = min_remaining_tokens
        self.max_retries = max_retries
        self.base_backoff = base_backoff
        self.state = RateLimitState()
        self._lock = asyncio.Lock()

    def update_from_headers(self, headers: dict[str, str]) -> None:
        now = time.time()
        if "x-ratelimit-remaining-requests" in headers:
            self.state.remaining_requests = int(headers["x-ratelimit-remaining-requests"])
        if "x-ratelimit-remaining-tokens" in headers:
            self.state.remaining_tokens = int(headers["x-ratelimit-remaining-tokens"])
        self.state.last_updated = now

    async def wait_if_needed(self) -> None:
        async with self._lock:
            now = time.time()
            if self.state.remaining_requests <= self.min_remaining_requests:
                if self.state.reset_requests_at > now:
                    wait_time = min(self.state.reset_requests_at - now, 60)
                    print(f"  ⏳ Rate limit: waiting {wait_time:.1f}s...")
                    await asyncio.sleep(wait_time)

    async def handle_rate_limit_error(self, attempt: int, retry_after: float | None = None) -> bool:
        if attempt >= self.max_retries:
            return False
        wait_time = retry_after if retry_after else self.base_backoff * (2 ** attempt)
        print(f"  ⏳ Backing off {wait_time:.1f}s (attempt {attempt + 1})...")
        await asyncio.sleep(min(wait_time, 120))
        return True


class RateLimitError(Exception):
    def __init__(self, message: str, retry_after: float | None = None):
        super().__init__(message)
        self.retry_after = retry_after


@dataclass
class LLMConfig:
    provider: str = "groq/llama-3.1-8b-instant"
    api_token: str | None = None
    temperature: float = 0.0
    max_tokens: int = 4000
    enable_rate_limiting: bool = True

    @classmethod
    def groq(cls) -> "LLMConfig":
        return cls(
            provider="groq/llama-3.1-8b-instant",
            api_token=os.getenv("GROQ_API_KEY"),
        )


class DirectLLMClient:
    def __init__(self, config: LLMConfig):
        self.config = config
        self._rate_limiter = RateLimiter() if config.enable_rate_limiting else None

    async def complete(self, prompt: str, system_prompt: str | None = None) -> str:
        import litellm

        messages = []
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

                if self._rate_limiter and hasattr(response, "_hidden_params"):
                    headers = response._hidden_params.get("additional_headers", {})
                    if headers:
                        self._rate_limiter.update_from_headers(headers)

                content = response.choices[0].message.content
                return content if content else ""

            except Exception as e:
                if "429" in str(e).lower() or "rate limit" in str(e).lower():
                    if self._rate_limiter and await self._rate_limiter.handle_rate_limit_error(attempt):
                        continue
                    raise RateLimitError(f"Rate limit exceeded: {e}")
                raise

        raise RateLimitError(f"Rate limit exceeded after {max_attempts} attempts")

    async def extract_json(self, prompt: str, system_prompt: str | None = None) -> Any:
        response = await self.complete(prompt, system_prompt)

        # Extract JSON from response
        if "```json" in response:
            start = response.find("```json") + 7
            end = response.find("```", start)
            response = response[start:end]
        elif "```" in response:
            start = response.find("```") + 3
            end = response.find("```", start)
            response = response[start:end]

        return json.loads(response.strip())


# ============================================================================
# Real-world test
# ============================================================================

# Real URLs to test with
TEST_URLS = [
    {
        "url": "https://www.europarl.europa.eu/news/en/headlines/society/20230601STO93804/eu-ai-act-first-regulation-on-artificial-intelligence",
        "topic": "EU AI Act regulation",
        "source": "European Parliament",
    },
    {
        "url": "https://www.brookings.edu/articles/the-eu-ai-act-will-have-global-impact-but-a-limited-brussels-effect/",
        "topic": "EU AI Act global impact",
        "source": "Brookings Institution",
    },
]

IDEA_EXTRACTION_SYSTEM = """You are an expert at extracting key ideas, claims, and arguments from text.

For each distinct idea, identify:
1. The core claim (1-2 sentences)
2. The stance toward the topic (support, oppose, or neutral)
3. Confidence level (0.0 to 1.0)

Output ONLY a valid JSON array."""

IDEA_EXTRACTION_PROMPT = """Topic: {topic}

Content from {source}:
{content}

Extract 3-5 distinct ideas/claims from this content. Return JSON array:
[
  {{"claim": "specific claim text", "stance": "support|oppose|neutral", "confidence": 0.0-1.0, "evidence": "brief supporting evidence"}}
]"""


async def test_real_content():
    """Fetch real content and extract ideas."""

    print("=" * 70)
    print("  NOUS REAL-WORLD TEST")
    print("  Fetching live content and extracting ideas with Groq LLM")
    print("=" * 70)

    config = LLMConfig.groq()

    if not config.api_token:
        print("\n❌ GROQ_API_KEY not set")
        return False

    client = DirectLLMClient(config)
    all_ideas = []

    for i, test_case in enumerate(TEST_URLS, 1):
        url = test_case["url"]
        topic = test_case["topic"]
        source = test_case["source"]

        print(f"\n{'─' * 70}")
        print(f"[{i}/{len(TEST_URLS)}] Source: {source}")
        print(f"    URL: {url[:60]}...")
        print(f"    Topic: {topic}")
        print("─" * 70)

        # Stage 1: Fetch content
        print("\n  📥 Fetching content...")
        try:
            html = fetch_url(url)
            text = html_to_text(html)

            # Truncate to reasonable size
            if len(text) > 6000:
                text = text[:6000] + "..."

            print(f"     Retrieved {len(text):,} characters")

        except Exception as e:
            print(f"     ❌ Failed to fetch: {e}")
            continue

        # Stage 2: Extract ideas with LLM
        print("\n  🧠 Extracting ideas with LLM...")
        try:
            prompt = IDEA_EXTRACTION_PROMPT.format(
                topic=topic,
                source=source,
                content=text[:5000],
            )

            ideas = await client.extract_json(prompt, IDEA_EXTRACTION_SYSTEM)

            if isinstance(ideas, list):
                print(f"     ✓ Extracted {len(ideas)} ideas:\n")

                for j, idea in enumerate(ideas, 1):
                    claim = idea.get("claim", "No claim")
                    stance = idea.get("stance", "?")
                    confidence = idea.get("confidence", 0)
                    evidence = idea.get("evidence", "")

                    # Stance emoji
                    stance_emoji = {"support": "👍", "oppose": "👎", "neutral": "➖"}.get(stance, "❓")

                    print(f"     [{j}] {stance_emoji} {claim[:75]}{'...' if len(claim) > 75 else ''}")
                    print(f"         Stance: {stance} | Confidence: {confidence}")
                    if evidence:
                        print(f"         Evidence: {evidence[:60]}...")
                    print()

                    all_ideas.append({
                        "source": source,
                        "url": url,
                        **idea
                    })
            else:
                print(f"     ⚠️  Unexpected response format: {type(ideas)}")

        except json.JSONDecodeError as e:
            print(f"     ❌ JSON parse error: {e}")
        except RateLimitError as e:
            print(f"     ⚠️  Rate limited: {e}")
        except Exception as e:
            print(f"     ❌ Extraction failed: {e}")
            import traceback
            traceback.print_exc()

    # Summary
    print("\n" + "=" * 70)
    print("  SUMMARY")
    print("=" * 70)
    print(f"  Sources processed: {len(TEST_URLS)}")
    print(f"  Total ideas extracted: {len(all_ideas)}")

    if all_ideas:
        # Count stances
        stances = {}
        for idea in all_ideas:
            stance = idea.get("stance", "unknown")
            stances[stance] = stances.get(stance, 0) + 1

        print(f"\n  Stance distribution:")
        for stance, count in sorted(stances.items()):
            emoji = {"support": "👍", "oppose": "👎", "neutral": "➖"}.get(stance, "❓")
            print(f"    {emoji} {stance}: {count}")

        # Average confidence
        confidences = [idea.get("confidence", 0) for idea in all_ideas if isinstance(idea.get("confidence"), (int, float))]
        if confidences:
            avg_conf = sum(confidences) / len(confidences)
            print(f"\n  Average confidence: {avg_conf:.2f}")

    print("\n" + "=" * 70)
    return len(all_ideas) > 0


async def main():
    success = await test_real_content()
    print(f"\n{'✓ Test passed!' if success else '✗ Test failed!'}")
    return success


if __name__ == "__main__":
    success = asyncio.run(main())
    sys.exit(0 if success else 1)
