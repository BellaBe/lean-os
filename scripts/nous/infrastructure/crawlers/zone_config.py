"""
Zone-aware crawl configuration for Nous.

Configures crawling behavior based on source signal zones:
- INSTITUTIONAL: Government, academic, major news - cache enabled, no magic
- GRASSROOTS: Blogs, forums, social - magic enabled for anti-bot
- SPECULATIVE: Unknown/new sources - magic + bypass cache

Uses Crawl4AI features:
- CacheMode for intelligent caching
- magic for automatic anti-bot handling
- js_code for dynamic content
- wait_for for page readiness
- session_id for session reuse
"""

from dataclasses import dataclass, field
from typing import Any

from crawl4ai import CacheMode, CrawlerRunConfig

from ...domain import SignalZone


@dataclass
class ZoneCrawlProfile:
    """Crawl configuration for a signal zone."""

    # Caching
    cache_mode: CacheMode = CacheMode.ENABLED

    # Anti-bot handling
    magic: bool = False  # Auto anti-bot detection/evasion

    # Timeouts
    page_timeout: int = 30000  # ms
    delay_before_return_html: float = 0.0  # seconds

    # Content filtering
    word_count_threshold: int = 50
    excluded_tags: list[str] = field(
        default_factory=lambda: [
            "nav",
            "footer",
            "aside",
            "script",
            "style",
            "noscript",
        ]
    )
    remove_overlay_elements: bool = True

    # Dynamic content
    wait_for: str | None = None  # CSS selector to wait for
    js_code: str | None = None  # JavaScript to execute

    # Session
    use_session: bool = True  # Reuse session within domain


# Zone-specific crawl profiles
ZONE_PROFILES: dict[SignalZone, ZoneCrawlProfile] = {
    SignalZone.INSTITUTIONAL: ZoneCrawlProfile(
        cache_mode=CacheMode.ENABLED,
        magic=False,  # Institutional sites rarely block
        page_timeout=60000,  # 60s - arXiv and academic sites can be slow
        word_count_threshold=100,  # Higher quality threshold
        remove_overlay_elements=True,
        use_session=True,
    ),
    SignalZone.GRASSROOTS: ZoneCrawlProfile(
        cache_mode=CacheMode.ENABLED,
        magic=True,  # Blogs/forums may have anti-bot
        page_timeout=45000,  # Slower sites
        delay_before_return_html=0.5,  # Wait for JS
        word_count_threshold=50,
        remove_overlay_elements=True,
        js_code="window.scrollTo(0, document.body.scrollHeight);",  # Load comments
        use_session=True,
    ),
    SignalZone.SPECULATIVE: ZoneCrawlProfile(
        cache_mode=CacheMode.BYPASS,  # Don't cache unknown sources
        magic=True,  # Maximum anti-bot
        page_timeout=60000,  # Very generous timeout
        delay_before_return_html=1.0,
        word_count_threshold=30,  # Lower threshold for exploration
        remove_overlay_elements=True,
        use_session=False,  # Fresh session each time
    ),
}


# Domain to zone mappings (50+ domains)
DOMAIN_ZONES: dict[str, SignalZone] = {
    # === INSTITUTIONAL: Government ===
    "gov": SignalZone.INSTITUTIONAL,
    "gov.uk": SignalZone.INSTITUTIONAL,
    "europa.eu": SignalZone.INSTITUTIONAL,
    "who.int": SignalZone.INSTITUTIONAL,
    "un.org": SignalZone.INSTITUTIONAL,
    "whitehouse.gov": SignalZone.INSTITUTIONAL,
    "congress.gov": SignalZone.INSTITUTIONAL,
    "sec.gov": SignalZone.INSTITUTIONAL,
    "fda.gov": SignalZone.INSTITUTIONAL,
    "cdc.gov": SignalZone.INSTITUTIONAL,
    "nih.gov": SignalZone.INSTITUTIONAL,
    "nasa.gov": SignalZone.INSTITUTIONAL,
    # === INSTITUTIONAL: Academic ===
    "edu": SignalZone.INSTITUTIONAL,
    "ac.uk": SignalZone.INSTITUTIONAL,
    "arxiv.org": SignalZone.INSTITUTIONAL,
    "nature.com": SignalZone.INSTITUTIONAL,
    "science.org": SignalZone.INSTITUTIONAL,
    "cell.com": SignalZone.INSTITUTIONAL,
    "pnas.org": SignalZone.INSTITUTIONAL,
    "springer.com": SignalZone.INSTITUTIONAL,
    "wiley.com": SignalZone.INSTITUTIONAL,
    "elsevier.com": SignalZone.INSTITUTIONAL,
    "sciencedirect.com": SignalZone.INSTITUTIONAL,
    "semanticscholar.org": SignalZone.INSTITUTIONAL,
    "pubmed.ncbi.nlm.nih.gov": SignalZone.INSTITUTIONAL,
    "jstor.org": SignalZone.INSTITUTIONAL,
    "ssrn.com": SignalZone.INSTITUTIONAL,
    "researchgate.net": SignalZone.INSTITUTIONAL,
    # === INSTITUTIONAL: Major News ===
    "reuters.com": SignalZone.INSTITUTIONAL,
    "apnews.com": SignalZone.INSTITUTIONAL,
    "bbc.com": SignalZone.INSTITUTIONAL,
    "bbc.co.uk": SignalZone.INSTITUTIONAL,
    "nytimes.com": SignalZone.INSTITUTIONAL,
    "washingtonpost.com": SignalZone.INSTITUTIONAL,
    "theguardian.com": SignalZone.INSTITUTIONAL,
    "economist.com": SignalZone.INSTITUTIONAL,
    "ft.com": SignalZone.INSTITUTIONAL,
    "wsj.com": SignalZone.INSTITUTIONAL,
    "bloomberg.com": SignalZone.INSTITUTIONAL,
    "cnbc.com": SignalZone.INSTITUTIONAL,
    # === INSTITUTIONAL: Tech News ===
    "techcrunch.com": SignalZone.INSTITUTIONAL,
    "wired.com": SignalZone.INSTITUTIONAL,
    "arstechnica.com": SignalZone.INSTITUTIONAL,
    "theverge.com": SignalZone.INSTITUTIONAL,
    "zdnet.com": SignalZone.INSTITUTIONAL,
    "cnet.com": SignalZone.INSTITUTIONAL,
    # === INSTITUTIONAL: Research/Reports ===
    "mckinsey.com": SignalZone.INSTITUTIONAL,
    "bcg.com": SignalZone.INSTITUTIONAL,
    "bain.com": SignalZone.INSTITUTIONAL,
    "gartner.com": SignalZone.INSTITUTIONAL,
    "forrester.com": SignalZone.INSTITUTIONAL,
    "deloitte.com": SignalZone.INSTITUTIONAL,
    "pwc.com": SignalZone.INSTITUTIONAL,
    "kpmg.com": SignalZone.INSTITUTIONAL,
    "ey.com": SignalZone.INSTITUTIONAL,
    # === INSTITUTIONAL: Company Blogs ===
    "blog.google": SignalZone.INSTITUTIONAL,
    "openai.com": SignalZone.INSTITUTIONAL,
    "anthropic.com": SignalZone.INSTITUTIONAL,
    "microsoft.com": SignalZone.INSTITUTIONAL,
    "aws.amazon.com": SignalZone.INSTITUTIONAL,
    "cloud.google.com": SignalZone.INSTITUTIONAL,
    "ai.meta.com": SignalZone.INSTITUTIONAL,
    "developer.nvidia.com": SignalZone.INSTITUTIONAL,
    # === GRASSROOTS: Social/Forums ===
    "reddit.com": SignalZone.GRASSROOTS,
    "news.ycombinator.com": SignalZone.GRASSROOTS,
    "x.com": SignalZone.GRASSROOTS,
    "linkedin.com": SignalZone.GRASSROOTS,
    "facebook.com": SignalZone.GRASSROOTS,
    "quora.com": SignalZone.GRASSROOTS,
    "stackoverflow.com": SignalZone.GRASSROOTS,
    "stackexchange.com": SignalZone.GRASSROOTS,
    "discord.com": SignalZone.GRASSROOTS,
    # === GRASSROOTS: Blogs/Newsletters ===
    "medium.com": SignalZone.GRASSROOTS,
    "substack.com": SignalZone.GRASSROOTS,
    "dev.to": SignalZone.GRASSROOTS,
    "hashnode.com": SignalZone.GRASSROOTS,
    "wordpress.com": SignalZone.GRASSROOTS,
    "blogger.com": SignalZone.GRASSROOTS,
    "ghost.io": SignalZone.GRASSROOTS,
    "beehiiv.com": SignalZone.GRASSROOTS,
    # === GRASSROOTS: Video/Podcasts ===
    "youtube.com": SignalZone.GRASSROOTS,
    "vimeo.com": SignalZone.GRASSROOTS,
    "spotify.com": SignalZone.GRASSROOTS,
    "podcasts.apple.com": SignalZone.GRASSROOTS,
    # === GRASSROOTS: Code/Tech ===
    "github.com": SignalZone.GRASSROOTS,
    "gitlab.com": SignalZone.GRASSROOTS,
    "huggingface.co": SignalZone.GRASSROOTS,
    "kaggle.com": SignalZone.GRASSROOTS,
}


def get_zone_for_domain(domain: str) -> SignalZone:
    """
    Determine the signal zone for a domain.

    Checks exact match first, then TLD patterns.
    Defaults to SPECULATIVE for unknown domains.

    Args:
        domain: Domain name (e.g., "example.com", "news.bbc.co.uk")

    Returns:
        SignalZone for the domain
    """
    # Normalize domain
    domain = domain.lower().replace("www.", "")

    # Exact match
    if domain in DOMAIN_ZONES:
        return DOMAIN_ZONES[domain]

    # Check parent domains (e.g., blog.example.com -> example.com)
    parts = domain.split(".")
    for i in range(len(parts) - 1):
        parent = ".".join(parts[i:])
        if parent in DOMAIN_ZONES:
            return DOMAIN_ZONES[parent]

    # Check TLD patterns
    for tld_pattern in ["gov", "edu", "ac.uk", "gov.uk"]:
        if domain.endswith(f".{tld_pattern}") or domain == tld_pattern:
            return SignalZone.INSTITUTIONAL

    # Default to speculative for unknown domains
    return SignalZone.SPECULATIVE


def build_crawl_config(
    domain: str,
    session_id: str | None = None,
    override_profile: ZoneCrawlProfile | None = None,
) -> CrawlerRunConfig:
    """
    Build a CrawlerRunConfig for a domain based on its signal zone.

    Args:
        domain: Domain name
        session_id: Optional session ID for session reuse
        override_profile: Optional profile to override zone defaults

    Returns:
        CrawlerRunConfig configured for the domain's zone
    """
    zone = get_zone_for_domain(domain)
    profile = override_profile or ZONE_PROFILES[zone]

    config = CrawlerRunConfig(
        # Caching
        cache_mode=profile.cache_mode,
        # Anti-bot
        magic=profile.magic,
        # Timeouts
        page_timeout=profile.page_timeout,
        delay_before_return_html=profile.delay_before_return_html,
        # Content filtering
        word_count_threshold=profile.word_count_threshold,
        excluded_tags=profile.excluded_tags,
        remove_overlay_elements=profile.remove_overlay_elements,
        # Dynamic content
        wait_for=profile.wait_for,
        js_code=profile.js_code,
        # Session
        session_id=session_id if profile.use_session else None,
    )

    return config


def get_zone_profile(zone: SignalZone) -> ZoneCrawlProfile:
    """Get the crawl profile for a zone."""
    return ZONE_PROFILES[zone]


# Special site configurations (override zone defaults)
SPECIAL_SITE_CONFIGS: dict[str, dict[str, Any]] = {
    "medium.com": {
        "wait_for": ".postArticle-content, article",
        "delay_before_return_html": 1.0,
    },
    "bloomberg.com": {
        "js_code": "document.querySelector('.paywall-dismiss, [data-paywall-close]')?.click();",
        "delay_before_return_html": 1.5,
    },
    "linkedin.com": {
        "wait_for": ".feed-shared-update-v2__description",
        "magic": True,
    },
    "x.com": {
        "wait_for": "[data-testid='tweet']",
        "js_code": "window.scrollTo(0, 1000);",
        "delay_before_return_html": 2.0,
    },
}


def get_special_config(domain: str) -> dict[str, Any] | None:
    """Get special configuration for sites that need custom handling."""
    domain = domain.lower().replace("www.", "")
    return SPECIAL_SITE_CONFIGS.get(domain)
