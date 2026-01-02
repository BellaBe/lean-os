"""
Browser Configuration for Anti-Bot Evasion

SIMPLIFIED: Most anti-bot handling is now done by Crawl4AI's magic=True
in zone_config.py. This module now only handles:
1. Sites requiring special configuration (Cloudflare, DataDome)
2. Proxy support for IP rotation
3. Storage state for session persistence

For most sites, zone_config.py's magic=True is sufficient.
Only use this module for sites that still get blocked.
"""

from dataclasses import dataclass, field
from enum import Enum
from typing import TYPE_CHECKING, Any

if TYPE_CHECKING:
    from crawl4ai import BrowserConfig


class ProtectionLevel(str, Enum):
    """Site protection level - determines which countermeasures to use."""

    NONE = "none"  # No bot detection - use zone_config defaults
    BASIC = "basic"  # Simple checks - handled by magic=True
    ADVANCED = "advanced"  # Cloudflare, DataDome - needs undetected browser
    MAXIMUM = "maximum"  # All countermeasures + proxy


@dataclass
class ProxyConfig:
    """Proxy configuration for IP rotation and geo-targeting."""

    server: str  # e.g., "http://proxy.example.com:8080"
    username: str | None = None
    password: str | None = None

    # Geo-targeting
    country: str | None = None  # ISO country code for geo-proxy services

    def to_dict(self) -> dict:
        """Convert to Crawl4AI format."""
        config = {"server": self.server}
        if self.username:
            config["username"] = self.username
        if self.password:
            config["password"] = self.password
        return config


@dataclass
class StealthConfig:
    """Configuration for browser stealth features."""

    # Core stealth
    enable_stealth: bool = True  # playwright-stealth modifications

    # Undetected browser (for advanced protection)
    use_undetected: bool = False  # Use UndetectedAdapter

    # Browser behavior
    headless: bool = True  # Headless mode (visible browser more human-like)
    slow_mo: int = 0  # Slow down operations (ms)

    # User agent
    custom_user_agent: str | None = None
    randomize_user_agent: bool = False

    # Viewport randomization
    randomize_viewport: bool = False
    viewport_width: int = 1920
    viewport_height: int = 1080

    # Additional evasion
    disable_webgl: bool = False  # Some fingerprinters use WebGL
    block_resources: list[str] = field(default_factory=list)  # e.g., ["image", "font"]


@dataclass
class BrowserProfile:
    """Complete browser profile for crawling."""

    name: str
    protection_level: ProtectionLevel = ProtectionLevel.BASIC
    stealth: StealthConfig = field(default_factory=StealthConfig)
    proxy: ProxyConfig | None = None

    # Session persistence
    storage_state_path: str | None = None  # Path to storage state JSON

    # Timeouts
    page_timeout: int = 30000  # Page load timeout (ms)
    navigation_timeout: int = 30000  # Navigation timeout (ms)


# Pre-configured profiles for common scenarios
PROFILE_BASIC = BrowserProfile(
    name="basic",
    protection_level=ProtectionLevel.NONE,
    stealth=StealthConfig(enable_stealth=False),
)

PROFILE_STEALTH = BrowserProfile(
    name="stealth",
    protection_level=ProtectionLevel.BASIC,
    stealth=StealthConfig(enable_stealth=True),
)

PROFILE_UNDETECTED = BrowserProfile(
    name="undetected",
    protection_level=ProtectionLevel.ADVANCED,
    stealth=StealthConfig(
        enable_stealth=True,
        use_undetected=True,
        headless=False,  # Undetected works better with visible browser
    ),
)

PROFILE_MAXIMUM = BrowserProfile(
    name="maximum",
    protection_level=ProtectionLevel.MAXIMUM,
    stealth=StealthConfig(
        enable_stealth=True,
        use_undetected=True,
        headless=False,
        slow_mo=100,
        randomize_viewport=True,
    ),
)


class BrowserFactory:
    """
    Factory for creating configured browser instances.

    Handles the complexity of setting up stealth, undetected browser,
    and proxy configurations.
    """

    @staticmethod
    def create_browser_config(profile: BrowserProfile) -> "BrowserConfig":
        """
        Create Crawl4AI BrowserConfig from profile.

        Args:
            profile: Browser profile with desired settings

        Returns:
            Configured BrowserConfig instance
        """
        try:
            from crawl4ai import BrowserConfig
        except ImportError:
            raise ImportError("crawl4ai not installed. Run: pip install crawl4ai")

        config_kwargs: dict[str, Any] = {
            "headless": profile.stealth.headless,
            "verbose": False,
        }

        # Stealth mode
        if profile.stealth.enable_stealth:
            config_kwargs["enable_stealth"] = True

        # Proxy
        if profile.proxy:
            config_kwargs["proxy_config"] = profile.proxy.to_dict()

        # User agent
        if profile.stealth.custom_user_agent:
            config_kwargs["user_agent"] = profile.stealth.custom_user_agent

        # Viewport
        if not profile.stealth.randomize_viewport:
            config_kwargs["viewport_width"] = profile.stealth.viewport_width
            config_kwargs["viewport_height"] = profile.stealth.viewport_height

        return BrowserConfig(**config_kwargs)

    @staticmethod
    def create_crawler_strategy(profile: BrowserProfile) -> Any | None:
        """
        Create crawler strategy with undetected browser if needed.

        Args:
            profile: Browser profile

        Returns:
            Configured crawler strategy or None for default
        """
        if not profile.stealth.use_undetected:
            return None

        try:
            from crawl4ai import UndetectedAdapter
            from crawl4ai.async_crawler_strategy import AsyncPlaywrightCrawlerStrategy

            browser_config = BrowserFactory.create_browser_config(profile)
            adapter = UndetectedAdapter()

            return AsyncPlaywrightCrawlerStrategy(
                browser_config=browser_config,
                browser_adapter=adapter,
            )
        except ImportError:
            print("Warning: UndetectedAdapter not available, falling back to regular browser")
            return None

    @staticmethod
    async def create_crawler(profile: BrowserProfile) -> Any:
        """
        Create fully configured AsyncWebCrawler.

        Args:
            profile: Browser profile

        Returns:
            Configured AsyncWebCrawler instance
        """
        try:
            from crawl4ai import AsyncWebCrawler
        except ImportError:
            raise ImportError("crawl4ai not installed. Run: pip install crawl4ai")

        browser_config = BrowserFactory.create_browser_config(profile)
        strategy = BrowserFactory.create_crawler_strategy(profile)

        crawler_kwargs = {"config": browser_config}

        if strategy:
            crawler_kwargs["crawler_strategy"] = strategy

        if profile.storage_state_path:
            crawler_kwargs["storage_state"] = profile.storage_state_path

        return AsyncWebCrawler(**crawler_kwargs)


class ProtectedSiteCrawler:
    """
    High-level crawler for sites with bot protection.

    Automatically selects appropriate countermeasures based on
    detection level.

    Example:
        async with ProtectedSiteCrawler(ProtectionLevel.ADVANCED) as crawler:
            result = await crawler.crawl("https://protected-site.com")
    """

    def __init__(
        self,
        protection_level: ProtectionLevel = ProtectionLevel.BASIC,
        proxy: ProxyConfig | None = None,
        storage_state_path: str | None = None,
    ):
        self.protection_level = protection_level
        self.proxy = proxy
        self.storage_state_path = storage_state_path
        self._crawler: Any = None
        self._profile = self._build_profile()

    def _build_profile(self) -> BrowserProfile:
        """Build browser profile based on protection level."""
        if self.protection_level == ProtectionLevel.NONE:
            profile = BrowserProfile(
                name="custom",
                protection_level=self.protection_level,
                stealth=StealthConfig(enable_stealth=False),
            )
        elif self.protection_level == ProtectionLevel.BASIC:
            profile = BrowserProfile(
                name="custom",
                protection_level=self.protection_level,
                stealth=StealthConfig(enable_stealth=True),
            )
        elif self.protection_level == ProtectionLevel.ADVANCED:
            profile = BrowserProfile(
                name="custom",
                protection_level=self.protection_level,
                stealth=StealthConfig(
                    enable_stealth=True,
                    use_undetected=True,
                    headless=False,
                ),
            )
        else:  # MAXIMUM
            profile = BrowserProfile(
                name="custom",
                protection_level=self.protection_level,
                stealth=StealthConfig(
                    enable_stealth=True,
                    use_undetected=True,
                    headless=False,
                    slow_mo=100,
                    randomize_viewport=True,
                ),
            )

        profile.proxy = self.proxy
        profile.storage_state_path = self.storage_state_path
        return profile

    async def __aenter__(self) -> "ProtectedSiteCrawler":
        self._crawler = await BrowserFactory.create_crawler(self._profile)
        await self._crawler.start()
        return self

    async def __aexit__(
        self,
        exc_type: type[BaseException] | None,
        exc_val: BaseException | None,
        exc_tb: Any,
    ) -> None:
        if self._crawler:
            await self._crawler.close()

    async def crawl(
        self,
        url: str,
        wait_for: str | None = None,
        delay_before_return: float = 0.5,
    ) -> Any:
        """
        Crawl a protected URL.

        Args:
            url: URL to crawl
            wait_for: CSS selector to wait for
            delay_before_return: Delay after page load (helps with JS)

        Returns:
            CrawlResult
        """
        try:
            from crawl4ai import CacheMode, CrawlerRunConfig
        except ImportError:
            raise ImportError("crawl4ai not installed")

        config = CrawlerRunConfig(
            cache_mode=CacheMode.BYPASS,
            wait_for=wait_for,
            delay_before_return_html=delay_before_return,
        )

        return await self._crawler.arun(url=url, config=config)


# Sites requiring special configuration beyond magic=True
# These sites have advanced bot detection that magic=True can't handle
SITES_REQUIRING_SPECIAL_CONFIG: dict[str, dict[str, Any]] = {
    # Cloudflare protected sites
    "medium.com": {
        "protection_level": ProtectionLevel.ADVANCED,
        "use_undetected": True,
        "wait_for": ".postArticle-content, article",
        "delay": 1.5,
    },
    "discord.com": {
        "protection_level": ProtectionLevel.ADVANCED,
        "use_undetected": True,
    },
    "canva.com": {
        "protection_level": ProtectionLevel.ADVANCED,
        "use_undetected": True,
    },
    # DataDome protected sites
    "footlocker.com": {
        "protection_level": ProtectionLevel.MAXIMUM,
        "use_undetected": True,
        "slow_mo": 100,
    },
    "ticketmaster.com": {
        "protection_level": ProtectionLevel.MAXIMUM,
        "use_undetected": True,
        "slow_mo": 100,
    },
    # Paywall sites needing special handling
    "bloomberg.com": {
        "protection_level": ProtectionLevel.BASIC,
        "js_code": "document.querySelector('.paywall-dismiss, [data-paywall-close]')?.click();",
        "delay": 1.5,
    },
    "ft.com": {
        "protection_level": ProtectionLevel.BASIC,
        "wait_for": "article",
    },
    "wsj.com": {
        "protection_level": ProtectionLevel.BASIC,
        "wait_for": "article",
    },
}


def get_special_site_config(domain: str) -> dict[str, Any] | None:
    """
    Get special configuration for sites that need extra handling.

    Most sites work fine with zone_config.py's magic=True.
    This is only for sites that still get blocked.

    Args:
        domain: Domain name (e.g., "medium.com")

    Returns:
        Special config dict or None if no special handling needed
    """
    domain_lower = domain.lower().replace("www.", "")

    # Check exact match
    if domain_lower in SITES_REQUIRING_SPECIAL_CONFIG:
        return SITES_REQUIRING_SPECIAL_CONFIG[domain_lower]

    # Check parent domain match
    for site, config in SITES_REQUIRING_SPECIAL_CONFIG.items():
        if domain_lower.endswith(f".{site}") or domain_lower == site:
            return config

    return None


def needs_special_handling(domain: str) -> bool:
    """Check if a domain needs special browser configuration."""
    return get_special_site_config(domain) is not None


# Convenience functions
def get_profile_for_site(domain: str) -> BrowserProfile:
    """
    Get recommended browser profile for a domain.

    NOTE: For most sites, use zone_config.py instead.
    This is only for sites that need undetected browser.
    """
    special_config = get_special_site_config(domain)

    if special_config:
        level = special_config.get("protection_level", ProtectionLevel.BASIC)
        if level == ProtectionLevel.MAXIMUM:
            return PROFILE_MAXIMUM
        elif level == ProtectionLevel.ADVANCED:
            return PROFILE_UNDETECTED
        elif level == ProtectionLevel.BASIC:
            return PROFILE_STEALTH

    return PROFILE_BASIC
