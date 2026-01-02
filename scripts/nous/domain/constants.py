"""
Nous Domain Constants

Named constants replacing magic numbers throughout the codebase.
Organized by domain area for easy discovery.
"""

from __future__ import annotations

# ============================================================================
# Content Thresholds
# ============================================================================

MIN_MEANINGFUL_CONTENT_CHARS = 200
"""Minimum characters for content to be considered meaningful."""

MIN_CONTENT_WORD_COUNT = 50
"""Minimum word count threshold for crawled pages."""

MAX_CONTENT_CHARS = 50000
"""Maximum content length before truncation for LLM processing."""


# ============================================================================
# Extraction Settings
# ============================================================================

DEFAULT_MAX_CONTENT_TOKENS = 2000
"""Default token budget for content sent to LLM."""

DEFAULT_CHUNK_TOKEN_THRESHOLD = 1000
"""Token threshold before chunking is applied."""

CHUNK_OVERLAP_RATE = 0.1
"""Overlap rate between content chunks (10%)."""

MAX_IDEAS_PER_SOURCE = 10
"""Maximum ideas to extract from a single source."""

MIN_CLAIM_LENGTH = 20
"""Minimum character length for a valid claim."""

MIN_CLAIM_WORD_COUNT = 8
"""Minimum word count for a valid claim (filters metadata noise)."""


# ============================================================================
# Rate Limiting (Groq Free Tier)
# ============================================================================

GROQ_BATCH_SIZE = 30
"""Number of items per batch for Groq API calls."""

RATE_LIMIT_DELAY_SECONDS = 5.0
"""Default delay between API calls to respect rate limits."""

GROQ_FREE_TIER_TPM = 6000
"""Groq free tier tokens per minute limit."""

GROQ_TOKEN_SAFETY_MARGIN = 0.8
"""Use only 80% of token limit for safety."""

MIN_WAIT_BETWEEN_LLM_CALLS = 2.0
"""Minimum seconds between LLM API calls."""


# ============================================================================
# Crawling Settings
# ============================================================================

DEFAULT_CRAWL_TIMEOUT_MS = 30000
"""Default page load timeout in milliseconds."""

MAX_CONCURRENT_CRAWLS = 10
"""Default maximum concurrent crawl connections."""

HUMAN_DELAY_MIN_SECONDS = 1.0
"""Minimum delay for human-like behavior."""

HUMAN_DELAY_MAX_SECONDS = 3.0
"""Maximum delay for human-like behavior."""

SAME_DOMAIN_DELAY_SECONDS = 2.0
"""Extra delay between requests to same domain."""


# ============================================================================
# Analysis Thresholds
# ============================================================================

CONSENSUS_SIMILARITY_THRESHOLD = 0.7
"""Minimum similarity for ideas to be considered consensus."""

CONTENTION_SIMILARITY_THRESHOLD = 0.4
"""Maximum similarity for ideas to be considered contention."""

MIN_CLUSTER_SIZE = 2
"""Minimum ideas needed to form a cluster."""

MIN_IDEAS_FOR_ANALYSIS = 2
"""Minimum ideas required to perform consensus analysis."""


# ============================================================================
# Discovery Settings
# ============================================================================

DEFAULT_MAX_URLS = 20
"""Default maximum URLs to crawl per snapshot."""

DEFAULT_MAX_RESULTS_PER_SOURCE = 50
"""Default maximum results per search provider."""

MAX_QUERY_VARIATIONS = 3
"""Number of query variations for search augmentation."""

URL_RELEVANCE_THRESHOLD = 6
"""Minimum relevance score (1-10) for URL filtering."""

IDEA_RELEVANCE_THRESHOLD = 6
"""Minimum relevance score (1-10) for idea filtering."""


# ============================================================================
# Domain Expansion
# ============================================================================

EXPANSION_MAX_DOMAINS = 5
"""Maximum domains to expand via sitemap/Common Crawl."""

EXPANSION_MAX_URLS_PER_DOMAIN = 20
"""Maximum URLs to fetch per domain during expansion."""

EXPANSION_SCORE_THRESHOLD = 0.3
"""Minimum BM25 score for URL relevance during expansion."""
