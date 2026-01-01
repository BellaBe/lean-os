"""
URL Seeding Source Discovery

Uses Crawl4AI's AsyncUrlSeeder for bulk URL discovery from:
- Sitemaps (fast, structured)
- Common Crawl (comprehensive, historical)

Key advantage over SERP: No browser needed, BM25 scoring, thousands of URLs in seconds.
"""

from dataclasses import dataclass, field
from datetime import datetime
from typing import Any

from ...domain import SearchResponse, SearchResult


@dataclass
class SeedingConfig:
    """Configuration for URL seeding."""

    source: str = "sitemap+cc"  # "sitemap", "cc", or "sitemap+cc"
    max_urls: int = 100
    extract_head: bool = True  # Get title, description, meta
    live_check: bool = False  # Verify URLs are accessible
    concurrency: int = 10
    hits_per_sec: int = 5  # Rate limiting

    # BM25 relevance scoring
    query: str | None = None
    scoring_method: str = "bm25"
    score_threshold: float = 0.3

    # Pattern filtering
    pattern: str = "*"  # e.g., "*/blog/*", "*/news/*"
    filter_nonsense_urls: bool = True


@dataclass
class SeededUrl:
    """A URL discovered via seeding with metadata."""

    url: str
    status: str = "unknown"  # "valid", "not_valid", "unknown"
    relevance_score: float = 0.0
    title: str | None = None
    description: str | None = None
    meta: dict = field(default_factory=dict)
    jsonld: list = field(default_factory=list)


class UrlSeeder:
    """
    Bulk URL discovery using sitemaps and Common Crawl.

    Much faster than SERP crawling for known domains.
    Use when you know which sites to analyze.
    """

    def __init__(self) -> None:
        self._seeder: Any = None

    async def _get_seeder(self) -> Any:
        """Lazy initialization."""
        if self._seeder is None:
            try:
                from crawl4ai import AsyncUrlSeeder

                self._seeder = AsyncUrlSeeder()
            except ImportError:
                raise ImportError("crawl4ai not installed. Run: pip install crawl4ai")
        return self._seeder

    async def close(self) -> None:
        """Close the seeder."""
        if self._seeder:
            await self._seeder.close()
            self._seeder = None

    async def __aenter__(self) -> "UrlSeeder":
        await self._get_seeder()
        return self

    async def __aexit__(
        self,
        exc_type: type[BaseException] | None,
        exc_val: BaseException | None,
        exc_tb: Any,
    ) -> None:
        await self.close()

    async def discover(
        self,
        domain: str,
        topic: str,
        config: SeedingConfig | None = None,
    ) -> list[SeededUrl]:
        """
        Discover relevant URLs from a domain.

        Args:
            domain: Domain to seed (e.g., "techcrunch.com")
            topic: Topic for relevance scoring
            config: Optional seeding configuration

        Returns:
            List of SeededUrl objects sorted by relevance
        """
        config = config or SeedingConfig()
        seeder = await self._get_seeder()

        try:
            from crawl4ai import SeedingConfig as C4ASeedingConfig

            c4a_config = C4ASeedingConfig(
                source=config.source,
                pattern=config.pattern,
                extract_head=config.extract_head,
                live_check=config.live_check,
                max_urls=config.max_urls,
                concurrency=config.concurrency,
                hits_per_sec=config.hits_per_sec,
                query=topic,  # Use topic for BM25 scoring
                scoring_method=config.scoring_method,
                score_threshold=config.score_threshold,
                filter_nonsense_urls=config.filter_nonsense_urls,
            )

            raw_urls = await seeder.urls(domain, c4a_config)

            # Convert to our domain objects
            results = []
            for item in raw_urls:
                head_data = item.get("head_data", {}) or {}
                meta = head_data.get("meta", {}) or {}

                results.append(
                    SeededUrl(
                        url=item.get("url", ""),
                        status=item.get("status", "unknown"),
                        relevance_score=item.get("relevance_score", 0.0),
                        title=head_data.get("title"),
                        description=meta.get("description"),
                        meta=meta,
                        jsonld=head_data.get("jsonld", []),
                    )
                )

            # Sort by relevance (already sorted, but ensure)
            results.sort(key=lambda x: x.relevance_score, reverse=True)
            return results

        except Exception as e:
            print(f"URL seeding failed for {domain}: {e}")
            return []

    async def discover_many(
        self,
        domains: list[str],
        topic: str,
        config: SeedingConfig | None = None,
    ) -> dict[str, list[SeededUrl]]:
        """
        Discover URLs from multiple domains in parallel.

        Args:
            domains: List of domains to seed
            topic: Topic for relevance scoring
            config: Optional seeding configuration

        Returns:
            Dict mapping domain -> list of SeededUrl
        """
        config = config or SeedingConfig()
        seeder = await self._get_seeder()

        try:
            from crawl4ai import SeedingConfig as C4ASeedingConfig

            c4a_config = C4ASeedingConfig(
                source=config.source,
                pattern=config.pattern,
                extract_head=config.extract_head,
                live_check=config.live_check,
                max_urls=config.max_urls,
                concurrency=config.concurrency,
                hits_per_sec=config.hits_per_sec,
                query=topic,
                scoring_method=config.scoring_method,
                score_threshold=config.score_threshold,
                filter_nonsense_urls=config.filter_nonsense_urls,
            )

            raw_results = await seeder.many_urls(domains, c4a_config)

            # Convert to our domain objects
            results = {}
            for domain, urls in raw_results.items():
                domain_results = []
                for item in urls:
                    head_data = item.get("head_data", {}) or {}
                    meta = head_data.get("meta", {}) or {}

                    domain_results.append(
                        SeededUrl(
                            url=item.get("url", ""),
                            status=item.get("status", "unknown"),
                            relevance_score=item.get("relevance_score", 0.0),
                            title=head_data.get("title"),
                            description=meta.get("description"),
                            meta=meta,
                            jsonld=head_data.get("jsonld", []),
                        )
                    )

                domain_results.sort(key=lambda x: x.relevance_score, reverse=True)
                results[domain] = domain_results

            return results

        except Exception as e:
            print(f"Multi-domain seeding failed: {e}")
            return {d: [] for d in domains}

    def to_search_response(
        self,
        topic: str,
        seeded_urls: list[SeededUrl],
        source_domain: str,
    ) -> SearchResponse:
        """
        Convert seeded URLs to SearchResponse for compatibility with existing pipeline.

        This allows using URL seeding as a drop-in replacement for SERP crawling.
        """
        results = []
        for i, seeded in enumerate(seeded_urls):
            results.append(
                SearchResult(
                    title=seeded.title or "",
                    url=seeded.url,
                    snippet=seeded.description or "",
                    position=i + 1,
                    date=None,  # Could extract from jsonld if available
                )
            )

        return SearchResponse(
            query=topic,
            results=results,
            top_stories=[],
            related_queries=[],
            searched_at=datetime.utcnow(),
            source=f"seeding:{source_domain}",
        )


# Curated domain lists for different source types
NEWS_DOMAINS = [
    "reuters.com",
    "bbc.com",
    "nytimes.com",
    "wsj.com",
    "bloomberg.com",
    "ft.com",
    "theguardian.com",
    "washingtonpost.com",
    "economist.com",
    "apnews.com",
]

TECH_NEWS_DOMAINS = [
    "techcrunch.com",
    "theverge.com",
    "wired.com",
    "arstechnica.com",
    "venturebeat.com",
    "thenextweb.com",
]

ACADEMIC_DOMAINS = [
    "arxiv.org",
    "semanticscholar.org",
    "nature.com",
    "science.org",
]

SOCIAL_DOMAINS = [
    "reddit.com",
    "news.ycombinator.com",
]


async def seed_topic(
    topic: str,
    domains: list[str],
    max_per_domain: int = 20,
    score_threshold: float = 0.3,
) -> dict[str, list[SeededUrl]]:
    """
    Quick helper to seed a topic across multiple domains.

    Example:
        results = await seed_topic(
            "AI regulation",
            NEWS_DOMAINS[:5],
            max_per_domain=10,
        )
    """
    config = SeedingConfig(
        max_urls=max_per_domain,
        extract_head=True,
        score_threshold=score_threshold,
    )

    async with UrlSeeder() as seeder:
        return await seeder.discover_many(domains, topic, config)
