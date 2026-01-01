"""
Topic-Aware Source Discovery

Uses search APIs for topic-specific discovery instead of sitemap crawling.

The key insight: Sitemaps return ALL URLs regardless of topic. Search APIs
return topic-relevant URLs directly. This is the correct approach.

Discovery flow:
1. Query search APIs (GDELT, Semantic Scholar, Reddit, etc.) - get relevant URLs
2. Optionally expand within discovered domains using sitemaps
3. Crawl content from discovered URLs

Supported sources:
- News: GDELT (free), NewsAPI (100 free/day)
- Academic: Semantic Scholar (free), arXiv (free)
- Social: Reddit (free), HackerNews (free)
"""

from dataclasses import dataclass, field
from datetime import UTC, datetime
from pathlib import Path
from typing import Optional
from urllib.parse import urlparse

from ..domain import (
    IdeaNode,
    SignalZone,
    SourceId,
    SourceNode,
    SourceType,
)
from ..infrastructure.crawlers import (
    ContentCrawler,
    CrawlResult,
    ProtectedSiteCrawler,
    ProtectionLevel,
    get_profile_for_site,
)
from ..infrastructure.crawlers.search_api import (
    APISearchResult,
    MultiSourceSearch,
    SearchAPIConfig,
)


@dataclass
class SeededDiscoveryConfig:
    """Configuration for topic-aware discovery."""

    # Source selection
    sources: list[str] = field(default_factory=lambda: ["news", "academic", "social"])
    max_results_per_source: int = 50

    # API keys (loaded from env if not provided)
    newsapi_key: Optional[str] = None

    # Content crawling
    max_concurrent_crawls: int = 5
    crawl_timeout: int = 30
    use_stealth_for_protected: bool = True
    skip_content_crawl: bool = False  # If True, only return URLs without crawling

    # Filtering
    language: str = "en"
    days_back: int = 30  # For news sources

    # Output
    save_snapshots: bool = False
    snapshot_dir: Optional[Path] = None


@dataclass
class SeededDiscoveryResult:
    """Result of seeded discovery."""

    topic: str
    discovered_at: datetime

    # Discovery stats
    urls_discovered: int = 0
    urls_crawled: int = 0
    urls_failed: int = 0

    # Results
    sources: list[SourceNode] = field(default_factory=list)
    ideas: list[IdeaNode] = field(default_factory=list)

    # Metadata
    domains_searched: list[str] = field(default_factory=list)
    avg_relevance_score: float = 0.0
    crawl_time_seconds: float = 0.0


def _classify_source_type(url: str, domain: str) -> SourceType:
    """Classify source type from URL/domain."""
    domain_lower = domain.lower()
    url_lower = url.lower()

    # Check domain-based classification first
    if any(
        d in domain_lower
        for d in ["arxiv", "semanticscholar", "nature.com", "science.org", "springer", "ieee"]
    ):
        return SourceType.ACADEMIC
    if any(d in domain_lower for d in ["reddit", "twitter", "x.com", "mastodon", "threads"]):
        return SourceType.SOCIAL
    if any(d in domain_lower for d in [".gov", "europa.eu", "gov.uk", "whitehouse"]):
        return SourceType.GOVERNMENT
    if any(d in domain_lower for d in ["substack", "medium", "wordpress", "blogger", "ghost"]):
        return SourceType.BLOG

    # Path-based detection for more precision
    if any(p in url_lower for p in ["/research/", "/paper/", "/publication/", "/abstract/", ".pdf"]):
        return SourceType.ACADEMIC
    if any(p in url_lower for p in ["/blog/", "/posts/", "/article/"]) and "news" not in domain_lower:
        return SourceType.BLOG
    if any(p in url_lower for p in ["/forum/", "/thread/", "/discussion/", "/comments/"]):
        return SourceType.FORUM
    if any(p in url_lower for p in ["/video/", "/watch/", "/embed/"]):
        return SourceType.VIDEO

    return SourceType.NEWS


def _classify_signal_zone(domain: str) -> SignalZone:
    """Classify signal zone from domain."""
    domain_lower = domain.lower()

    # Institutional sources
    institutional = [
        "reuters",
        "ap",
        "afp",
        "bbc",
        "nytimes",
        "wsj",
        "ft.com",
        "bloomberg",
        "economist",
        "nature",
        "science",
        "gov",
        "europa.eu",
        "who.int",
        "un.org",
        "imf.org",
        "worldbank",
    ]
    if any(i in domain_lower for i in institutional):
        return SignalZone.INSTITUTIONAL

    # Speculative sources
    speculative = [
        "twitter",
        "x.com",
        "telegram",
        "4chan",
        "reddit.com/r/conspiracy",
        "infowars",
        "zerohedge",
        "substack",  # substack is mixed but often speculative
    ]
    if any(s in domain_lower for s in speculative):
        return SignalZone.SPECULATIVE

    # Default to grassroots
    return SignalZone.GRASSROOTS


def _api_result_to_source(
    api_result: APISearchResult,
    crawl_result: Optional[CrawlResult] = None,
) -> SourceNode:
    """Convert APISearchResult + CrawlResult to SourceNode."""
    parsed = urlparse(api_result.url)
    domain = parsed.netloc.replace("www.", "")

    # Use API-provided source type if available, otherwise classify
    source_type = api_result.source_type or _classify_source_type(api_result.url, domain)

    source = SourceNode(
        id=SourceId(),
        url=api_result.url,
        title=api_result.title or (crawl_result.title if crawl_result else None) or domain,
        origin=api_result.source_name or domain,
        source_type=source_type,
        signal_zone=_classify_signal_zone(domain),
        published_at=api_result.published_at,
    )

    if crawl_result and crawl_result.success:
        source.content_markdown = crawl_result.markdown

    # Store metadata
    source.metadata = {
        "relevance_score": api_result.relevance_score,
        "snippet": api_result.snippet,
        "api_source": api_result.source,
        **api_result.metadata,
    }

    return source


class SeededDiscovery:
    """
    Topic-aware source discovery using search APIs.

    This uses actual search APIs (GDELT, Semantic Scholar, Reddit, etc.)
    to find topic-relevant sources, then optionally crawls content.

    Why this is better than sitemap crawling:
    - Sitemaps return ALL URLs regardless of topic
    - Search APIs return topic-relevant URLs directly
    - Much higher precision, less wasted crawling

    Example:
        discovery = SeededDiscovery()
        result = await discovery.discover("AI regulation EU")

        for source in result.sources:
            print(f"{source.title} ({source.signal_zone.value})")
            print(f"  Source: {source.metadata.get('api_source')}")
    """

    def __init__(self, config: Optional[SeededDiscoveryConfig] = None):
        self.config = config or SeededDiscoveryConfig()
        self._search = None

    def _get_search(self) -> MultiSourceSearch:
        """Lazy initialization of search client."""
        if self._search is None:
            api_config = SearchAPIConfig(
                newsapi_key=self.config.newsapi_key,
                max_results_per_provider=self.config.max_results_per_source,
                language=self.config.language,
                days_back=self.config.days_back,
            )
            self._search = MultiSourceSearch(api_config)
        return self._search

    async def discover(
        self,
        topic: str,
        sources: Optional[list[str]] = None,
        max_results: Optional[int] = None,
    ) -> SeededDiscoveryResult:
        """
        Discover sources for a topic using search APIs.

        Args:
            topic: Topic to search for
            sources: Source types: "news", "academic", "social", "all"
                     or specific: "gdelt", "arxiv", "reddit", etc.
            max_results: Maximum total results (across all sources)

        Returns:
            SeededDiscoveryResult with discovered sources
        """
        import time

        start_time = time.time()

        sources = sources or self.config.sources
        result = SeededDiscoveryResult(
            topic=topic,
            discovered_at=datetime.now(UTC),
            domains_searched=sources,  # Repurpose field for API sources
        )

        # Phase 1: Search APIs for topic-relevant URLs
        print(f"[1/3] Searching for '{topic}' via {sources}...")
        search = self._get_search()
        api_results = await search.search(
            topic,
            sources=sources,
            max_results_per_source=self.config.max_results_per_source,
        )

        result.urls_discovered = len(api_results)

        if not api_results:
            print("No results found. Try different sources or topic.")
            return result

        # Calculate average relevance
        scores = [r.relevance_score for r in api_results if r.relevance_score]
        result.avg_relevance_score = sum(scores) / len(scores) if scores else 0

        # Log by source
        source_counts: dict[str, int] = {}
        for r in api_results:
            source_counts[r.source] = source_counts.get(r.source, 0) + 1
        for src, count in source_counts.items():
            print(f"    {src}: {count} results")

        # Limit if requested
        if max_results and len(api_results) > max_results:
            api_results = api_results[:max_results]
            print(f"    Limited to {max_results} results")

        # Phase 2: Optionally crawl content
        if self.config.skip_content_crawl:
            print("[2/3] Skipping content crawl (skip_content_crawl=True)")
            for api_result in api_results:
                source = _api_result_to_source(api_result, None)
                result.sources.append(source)
            result.urls_crawled = 0
        else:
            print(f"[2/3] Crawling content from {len(api_results)} URLs...")
            crawl_results = await self._crawl_urls(api_results)

            # Phase 3: Convert to SourceNodes
            print("[3/3] Processing results...")
            for api_result, crawl_result in zip(api_results, crawl_results):
                source = _api_result_to_source(api_result, crawl_result)
                result.sources.append(source)
                if crawl_result and crawl_result.success:
                    result.urls_crawled += 1
                else:
                    result.urls_failed += 1

        result.crawl_time_seconds = time.time() - start_time

        print(f"    Discovered: {result.urls_discovered}")
        print(f"    Crawled: {result.urls_crawled}, Failed: {result.urls_failed}")
        print(f"    Total time: {result.crawl_time_seconds:.1f}s")

        return result

    async def _crawl_urls(
        self,
        api_results: list[APISearchResult],
    ) -> list[CrawlResult]:
        """Crawl content from discovered URLs."""
        urls = [r.url for r in api_results]

        # Group URLs by whether they need stealth
        if self.config.use_stealth_for_protected:
            regular_urls = []
            protected_urls = []

            for url in urls:
                domain = urlparse(url).netloc
                profile = get_profile_for_site(domain)

                if profile.protection_level.value in ["advanced", "maximum"]:
                    protected_urls.append(url)
                else:
                    regular_urls.append(url)

            results: dict[str, Optional[CrawlResult]] = {}

            # Crawl regular URLs
            if regular_urls:
                async with ContentCrawler() as crawler:
                    regular_results = await crawler.crawl_many(
                        regular_urls,
                        max_concurrent=self.config.max_concurrent_crawls,
                    )
                    for url, result in zip(regular_urls, regular_results):
                        results[url] = result

            # Crawl protected URLs with stealth
            if protected_urls:
                print(f"      Using stealth for {len(protected_urls)} protected URLs...")
                async with ProtectedSiteCrawler(ProtectionLevel.ADVANCED) as crawler:
                    for url in protected_urls:
                        try:
                            stealth_result = await crawler.crawl(url)
                            results[url] = CrawlResult(
                                url=url,
                                success=stealth_result.success,
                                html=stealth_result.html,
                                markdown=stealth_result.markdown.raw_markdown
                                if stealth_result.markdown
                                else "",
                                title=stealth_result.metadata.get("title")
                                if stealth_result.metadata
                                else "Unknown Title",
                            )
                        except Exception as e:
                            results[url] = CrawlResult(url=url, success=False, error=str(e))

            # Return in original order
            return [results.get(url) for url in urls]

        else:
            # Simple crawl without stealth detection
            async with ContentCrawler() as crawler:
                return await crawler.crawl_many(
                    urls,
                    max_concurrent=self.config.max_concurrent_crawls,
                )


# Convenience functions
async def discover_seeded(
    topic: str,
    sources: Optional[list[str]] = None,
    max_results: int = 100,
    skip_crawl: bool = False,
) -> SeededDiscoveryResult:
    """
    Quick helper for topic discovery.

    Example:
        result = await discover_seeded("AI regulation", max_results=50)
        for source in result.sources:
            print(source.title)
    """
    config = SeededDiscoveryConfig(
        sources=sources or ["news", "academic", "social"],
        skip_content_crawl=skip_crawl,
    )
    discovery = SeededDiscovery(config)
    return await discovery.discover(topic, max_results=max_results)


async def discover_news(topic: str, max_results: int = 100) -> SeededDiscoveryResult:
    """Discover from news sources (GDELT + NewsAPI)."""
    config = SeededDiscoveryConfig(sources=["news"])
    discovery = SeededDiscovery(config)
    return await discovery.discover(topic, max_results=max_results)


async def discover_tech(topic: str, max_results: int = 100) -> SeededDiscoveryResult:
    """Discover from tech/social sources (HackerNews + Reddit)."""
    config = SeededDiscoveryConfig(sources=["social"])
    discovery = SeededDiscovery(config)
    return await discovery.discover(topic, max_results=max_results)


async def discover_academic(topic: str, max_results: int = 100) -> SeededDiscoveryResult:
    """Discover from academic sources (Semantic Scholar + arXiv)."""
    config = SeededDiscoveryConfig(sources=["academic"])
    discovery = SeededDiscovery(config)
    return await discovery.discover(topic, max_results=max_results)


async def discover_all(topic: str, max_results: int = 200) -> SeededDiscoveryResult:
    """Discover from all available sources."""
    config = SeededDiscoveryConfig(sources=["all"])
    discovery = SeededDiscovery(config)
    return await discovery.discover(topic, max_results=max_results)
