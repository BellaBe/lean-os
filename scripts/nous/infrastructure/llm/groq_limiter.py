"""
Groq Rate Limiter - Smart token budget management for Groq's free tier.

Groq free tier limits:
- 6,000 tokens per minute (TPM)
- 30 requests per minute (RPM)

Strategy:
1. Track token usage with sliding window
2. Pre-calculate wait time BEFORE requests
3. Parse Groq's retry-after for accurate waits
4. Limit content size to control token usage
"""

import asyncio
import logging
import re
import time
from dataclasses import dataclass, field

log = logging.getLogger("nous.rate")


@dataclass
class GroqRateLimiter:
    """
    Global rate limiter for Groq API.

    Usage:
        limiter = GroqRateLimiter()

        # Before each request
        await limiter.wait_if_needed(estimated_tokens=1500)

        # After request (or on error)
        limiter.record_usage(actual_tokens=1200)

        # On rate limit error
        wait_time = limiter.parse_retry_after(error_message)
        await asyncio.sleep(wait_time)
    """

    # Groq free tier limits
    tokens_per_minute: int = 6000
    requests_per_minute: int = 30

    # Safety margins
    token_buffer: int = 500  # Keep this many tokens in reserve
    request_buffer: int = 5  # Keep this many requests in reserve

    # Minimum wait between requests (seconds)
    min_request_gap: float = 2.0

    # Tracking
    _token_usage: list = field(default_factory=list)  # [(timestamp, tokens), ...]
    _request_times: list = field(default_factory=list)  # [timestamp, ...]
    _last_request: float = 0.0
    _lock: asyncio.Lock = field(default_factory=asyncio.Lock)

    def __post_init__(self):
        self._token_usage = []
        self._request_times = []
        self._last_request = 0.0
        self._lock = asyncio.Lock()

    def _cleanup_old_entries(self) -> None:
        """Remove entries older than 1 minute."""
        cutoff = time.time() - 60
        self._token_usage = [(t, tokens) for t, tokens in self._token_usage if t > cutoff]
        self._request_times = [t for t in self._request_times if t > cutoff]

    def _current_usage(self) -> tuple[int, int]:
        """Get current token and request usage in the last minute."""
        self._cleanup_old_entries()
        total_tokens = sum(tokens for _, tokens in self._token_usage)
        total_requests = len(self._request_times)
        return total_tokens, total_requests

    def available_tokens(self) -> int:
        """Get available tokens for the next request."""
        used_tokens, _ = self._current_usage()
        return max(0, self.tokens_per_minute - self.token_buffer - used_tokens)

    async def wait_if_needed(self, estimated_tokens: int) -> None:
        """
        Wait if needed before making a request.

        Args:
            estimated_tokens: Estimated total tokens for the request
        """
        async with self._lock:
            now = time.time()

            # Always wait minimum gap between requests
            time_since_last = now - self._last_request
            if time_since_last < self.min_request_gap:
                gap_wait = self.min_request_gap - time_since_last
                log.debug(f"Waiting {gap_wait:.1f}s for min request gap")
                await asyncio.sleep(gap_wait)

            # Check token budget
            available = self.available_tokens()
            log.debug(f"Token budget: available={available}, estimated={estimated_tokens}")

            if estimated_tokens > available:
                # Need to wait for tokens to free up
                # Calculate how long based on token recovery rate
                tokens_needed = estimated_tokens - available
                # Tokens recover at rate of tokens_per_minute / 60 per second
                recovery_rate = self.tokens_per_minute / 60
                wait_time = tokens_needed / recovery_rate

                # Add buffer and cap at 60 seconds
                wait_time = min(wait_time + 2, 60)

                log.info(f"Rate limit wait: {wait_time:.1f}s (need {tokens_needed} more tokens)")
                print(f"      [Rate Limit] Waiting {wait_time:.1f}s for token budget...")
                await asyncio.sleep(wait_time)

            self._last_request = time.time()

    def record_usage(self, actual_tokens: int) -> None:
        """Record actual token usage after a request."""
        now = time.time()
        self._token_usage.append((now, actual_tokens))
        self._request_times.append(now)
        used, reqs = self._current_usage()
        log.debug(f"Recorded {actual_tokens} tokens. Total last minute: {used} tokens, {reqs} requests")

    @staticmethod
    def parse_retry_after(error_message: str) -> float:
        """
        Parse Groq's retry-after from error message.

        Example: "Please try again in 7.56s" -> 7.56
        """
        # Try to find "in X.XXs" or "in XXXms" pattern
        match = re.search(r'try again in (\d+\.?\d*)s', str(error_message))
        if match:
            return float(match.group(1)) + 1  # Add 1s buffer

        match = re.search(r'try again in (\d+)ms', str(error_message))
        if match:
            return float(match.group(1)) / 1000 + 1

        # Default to 10 seconds if can't parse
        return 10.0

    @staticmethod
    def estimate_tokens(text: str) -> int:
        """Estimate token count for text (~4 chars per token)."""
        return len(text) // 4

    @staticmethod
    def truncate_for_budget(content: str, max_tokens: int = 2000) -> str:
        """
        Truncate content to fit within token budget.

        Args:
            content: Text content
            max_tokens: Maximum tokens for content (excluding system prompt)

        Returns:
            Truncated content
        """
        # ~4 chars per token, leave room for response
        max_chars = max_tokens * 4

        if len(content) <= max_chars:
            return content

        # Truncate at word boundary
        truncated = content[:max_chars]
        last_space = truncated.rfind(' ')
        if last_space > max_chars * 0.8:  # Don't cut too much
            truncated = truncated[:last_space]

        return truncated + "\n\n[Content truncated for processing]"


# Global instance
_groq_limiter: GroqRateLimiter | None = None


def get_groq_limiter() -> GroqRateLimiter:
    """Get or create the global Groq rate limiter."""
    global _groq_limiter
    if _groq_limiter is None:
        _groq_limiter = GroqRateLimiter()
    return _groq_limiter


async def groq_safe_call(
    func,
    estimated_tokens: int,
    max_retries: int = 3,
) -> any:
    """
    Wrapper for Groq API calls with smart rate limiting.

    Args:
        func: Async function to call
        estimated_tokens: Estimated tokens for the request
        max_retries: Maximum retry attempts

    Returns:
        Result from func

    Raises:
        Exception: If all retries fail
    """
    limiter = get_groq_limiter()

    for attempt in range(max_retries):
        # Wait for rate limit budget
        await limiter.wait_if_needed(estimated_tokens)

        try:
            result = await func()

            # Try to record actual usage
            if hasattr(result, 'usage') and hasattr(result.usage, 'total_tokens'):
                limiter.record_usage(result.usage.total_tokens)
            else:
                limiter.record_usage(estimated_tokens)

            return result

        except Exception as e:
            error_str = str(e).lower()

            if 'rate' in error_str and 'limit' in error_str:
                wait_time = limiter.parse_retry_after(str(e))
                print(f"      [Rate Limit] Groq limit hit, waiting {wait_time:.1f}s...")
                await asyncio.sleep(wait_time)
            else:
                # Non-rate-limit error
                if attempt == max_retries - 1:
                    raise
                await asyncio.sleep(2)

    raise Exception("Max retries exceeded")
