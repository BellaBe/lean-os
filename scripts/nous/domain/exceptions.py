"""
Nous Domain Exceptions

Hierarchical exception system for clear error handling across all layers.
Each exception type corresponds to a specific failure domain.
"""

from __future__ import annotations


class NousError(Exception):
    """Base exception for all Nous errors."""

    def __init__(self, message: str, *, context: dict | None = None) -> None:
        self.message = message
        self.context = context or {}
        super().__init__(message)

    def __str__(self) -> str:
        if self.context:
            ctx = ", ".join(f"{k}={v}" for k, v in self.context.items())
            return f"{self.message} [{ctx}]"
        return self.message


# ============================================================================
# Discovery Layer Exceptions
# ============================================================================


class DiscoveryError(NousError):
    """URL discovery failed."""


class SearchAPIError(DiscoveryError):
    """Search API request failed."""

    def __init__(
        self,
        provider: str,
        message: str,
        *,
        status_code: int | None = None,
    ) -> None:
        self.provider = provider
        self.status_code = status_code
        super().__init__(message, context={"provider": provider})


class NoResultsError(DiscoveryError):
    """No URLs found for topic."""

    def __init__(self, topic: str) -> None:
        self.topic = topic
        super().__init__(f"No URLs found for topic: {topic}", context={"topic": topic})


# ============================================================================
# Crawling Layer Exceptions
# ============================================================================


class CrawlError(NousError):
    """Content crawling failed."""


class PageLoadError(CrawlError):
    """Page failed to load."""

    def __init__(self, url: str, reason: str) -> None:
        self.url = url
        self.reason = reason
        super().__init__(f"Failed to load: {reason}", context={"url": url})


class ContentTooShortError(CrawlError):
    """Extracted content below minimum threshold."""

    def __init__(self, url: str, char_count: int, min_required: int) -> None:
        self.url = url
        self.char_count = char_count
        self.min_required = min_required
        super().__init__(
            f"Content too short: {char_count} chars (min: {min_required})",
            context={"url": url},
        )


class BlockedByProtectionError(CrawlError):
    """Site blocked crawler (Cloudflare, DataDome, etc.)."""

    def __init__(self, url: str, protection_type: str) -> None:
        self.url = url
        self.protection_type = protection_type
        super().__init__(
            f"Blocked by {protection_type}",
            context={"url": url, "protection": protection_type},
        )


# ============================================================================
# Extraction Layer Exceptions
# ============================================================================


class ExtractionError(NousError):
    """Idea extraction failed."""


class LLMResponseError(ExtractionError):
    """LLM returned invalid or unparseable response."""

    def __init__(self, message: str, *, raw_response: str | None = None) -> None:
        self.raw_response = raw_response
        super().__init__(message)


class ChunkingError(ExtractionError):
    """Content chunking failed."""


# ============================================================================
# Analysis Layer Exceptions
# ============================================================================


class AnalysisError(NousError):
    """Consensus/contention analysis failed."""


class InsufficientDataError(AnalysisError):
    """Not enough ideas to perform analysis."""

    def __init__(self, idea_count: int, min_required: int) -> None:
        self.idea_count = idea_count
        self.min_required = min_required
        super().__init__(
            f"Need at least {min_required} ideas, got {idea_count}",
            context={"count": idea_count, "min": min_required},
        )


# ============================================================================
# LLM/Rate Limiting Exceptions
# ============================================================================


class RateLimitError(NousError):
    """Rate limit exceeded."""

    def __init__(
        self,
        provider: str,
        message: str,
        *,
        retry_after: float | None = None,
    ) -> None:
        self.provider = provider
        self.retry_after = retry_after
        super().__init__(
            message,
            context={"provider": provider, "retry_after": retry_after},
        )


class TokenBudgetExceededError(RateLimitError):
    """Token budget exhausted for current window."""


class RequestLimitExceededError(RateLimitError):
    """Request limit exhausted for current window."""


# ============================================================================
# Configuration Exceptions
# ============================================================================


class ConfigurationError(NousError):
    """Invalid configuration."""


class MissingAPIKeyError(ConfigurationError):
    """Required API key not found."""

    def __init__(self, key_name: str, env_var: str) -> None:
        self.key_name = key_name
        self.env_var = env_var
        super().__init__(
            f"Missing API key: {key_name}. Set {env_var} environment variable.",
            context={"key": key_name, "env_var": env_var},
        )
