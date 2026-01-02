"""
Search API Discovery

Topic-specific source discovery using search APIs and RSS feeds.

Supported providers:
- RSS Feeds (news, free, no rate limits) - major news outlets
- arXiv (academic, free)
- Reddit (social, free with limits)
- DuckDuckGo (web, free, general web coverage)

Source categories:
- "news"     -> RSS feeds from major news outlets
- "academic" -> arXiv
- "social"   -> Reddit
- "web"      -> DuckDuckGo
- "all"      -> All providers

For broader social/tech coverage, use site-specific web searches:
- Social: site:x.com, site:linkedin.com, etc.
- Tech: ycombinator.com/library, ycombinator.com/companies, etc.

The key insight: Use search APIs for DISCOVERY (topic-relevant URLs),
then use Crawl4AI for content extraction from any page.
"""

import asyncio
import logging
import re
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from datetime import UTC, datetime, timedelta

import aiohttp

from ...domain import SourceType

log = logging.getLogger("nous.search")


@dataclass
class SearchAPIConfig:
    """Configuration for search API providers."""

    # Limits
    max_results_per_provider: int = 50
    timeout_seconds: int = 30

    # Filtering
    language: str = "en"
    days_back: int = 30  # For news sources

    # Region/Geolocation
    region: str | None = None  # ISO 3166-1 alpha-2: us, de, fr, gb, jp, etc.
    regions: list[str] | None = None  # Multi-region search: ["us", "de", "gb"]

    # RSS-specific
    rss_keyword_filter: bool = True  # Filter RSS entries by query keywords

    # Screenshot fallback (for blocked sites like Reuters, Bloomberg)
    use_screenshot_fallback: bool = False  # Enable screenshot-based extraction
    screenshot_llm_provider: str = "groq/llama-3.2-90b-vision-preview"  # Vision LLM


# Region code mappings for DuckDuckGo
REGION_TO_DDG = {
    # DuckDuckGo uses region-lang format: "us-en", "de-de", "fr-fr"
    "us": "us-en",
    "gb": "uk-en",
    "uk": "uk-en",
    "au": "au-en",
    "ca": "ca-en",
    "de": "de-de",
    "fr": "fr-fr",
    "es": "es-es",
    "it": "it-it",
    "nl": "nl-nl",
    "jp": "jp-jp",
    "kr": "kr-kr",
    "cn": "cn-zh",
    "br": "br-pt",
    "mx": "mx-es",
    "in": "in-en",
    "ru": "ru-ru",
    "pl": "pl-pl",
    "se": "se-sv",
    "no": "no-no",
}


# RSS feeds for major news sources - grouped by category
# Note: Some feeds (Reuters) discontinued in 2020 - use SCREENSHOT_FALLBACK_SITES instead
NEWS_RSS_FEEDS = {
    # Tech News - Reliable RSS feeds
    "techcrunch": "https://techcrunch.com/feed/",
    "theverge": "https://www.theverge.com/rss/index.xml",
    "arstechnica": "https://feeds.arstechnica.com/arstechnica/technology-lab",
    "wired": "https://www.wired.com/feed/rss",
    "engadget": "https://www.engadget.com/rss.xml",
    "zdnet": "https://www.zdnet.com/news/rss.xml",
    "venturebeat": "https://venturebeat.com/feed/",  # Updated: feedburner deprecated
    "thenextweb": "https://thenextweb.com/feed",
    # General News - Tech sections
    "bbc_tech": "https://feeds.bbci.co.uk/news/technology/rss.xml",
    "guardian_tech": "https://www.theguardian.com/technology/rss",
    "nyt_tech": "https://rss.nytimes.com/services/xml/rss/nyt/Technology.xml",
    # reuters_tech: REMOVED - Reuters discontinued RSS in 2020, use screenshot fallback
    # Business/Finance
    "bloomberg_tech": "https://feeds.bloomberg.com/technology/news.rss",
    "forbes_tech": "https://www.forbes.com/innovation/feed/",
    "businessinsider": "https://www.businessinsider.com/sai/rss",
    # AI/ML Specific
    "mit_news": "https://news.mit.edu/rss/topic/artificial-intelligence2",
    "nvidia_blog": "https://blogs.nvidia.com/feed/",
    "openai_blog": "https://openai.com/blog/rss/",
    "deepmind_blog": "https://deepmind.google/blog/rss.xml",
    "huggingface": "https://huggingface.co/blog/feed.xml",
    # Startup/VC
    "techcrunch_startups": "https://techcrunch.com/category/startups/feed/",
    "sifted": "https://sifted.eu/feed",
}

# Sites that block RSS/scraping - use screenshot + LLM extraction
SCREENSHOT_FALLBACK_SITES = {
    "reuters.com": "https://www.reuters.com/technology/",
    "bloomberg.com": "https://www.bloomberg.com/technology",
    "wsj.com": "https://www.wsj.com/tech",
    "ft.com": "https://www.ft.com/technology",
}


@dataclass
class APISearchResult:
    """Unified search result from any API."""

    title: str
    url: str
    snippet: str
    source: str  # "newsapi", "bing", "gdelt", etc.
    source_name: str  # "Reuters", "BBC", etc.
    published_at: datetime | None = None
    relevance_score: float = 0.0
    source_type: SourceType = SourceType.NEWS
    metadata: dict = field(default_factory=dict)


class SearchAPIProvider(ABC):
    """Base class for search API providers."""

    @property
    @abstractmethod
    def name(self) -> str:
        pass

    @property
    @abstractmethod
    def source_type(self) -> SourceType:
        pass

    @abstractmethod
    async def search(
        self,
        query: str,
        max_results: int = 50,
        **kwargs,
    ) -> list[APISearchResult]:
        pass


class RSSNewsProvider(SearchAPIProvider):
    """
    RSS Feed aggregator for news sources.

    Free, no API keys, no rate limits.
    Fetches from 20+ major news RSS feeds and filters by query keywords.

    Much more reliable than GDELT/NewsAPI.
    """

    def __init__(self, feeds: dict[str, str] | None = None):
        self.feeds = feeds or NEWS_RSS_FEEDS

    @property
    def name(self) -> str:
        return "rss"

    @property
    def source_type(self) -> SourceType:
        return SourceType.NEWS

    async def search(
        self,
        query: str,
        max_results: int = 50,
        days_back: int = 30,
        **kwargs,
    ) -> list[APISearchResult]:
        """
        Fetch RSS feeds and filter entries by query keywords.
        """
        print(f"  → RSS: Searching {len(self.feeds)} news feeds...")
        log.info(f"RSS: searching {len(self.feeds)} feeds for '{query}'")

        # Extract keywords for filtering (lowercase, split on spaces)
        keywords = [k.lower().strip() for k in query.split() if len(k) > 2]

        all_results: list[APISearchResult] = []
        cutoff_date = datetime.now(UTC) - timedelta(days=days_back)

        # Fetch feeds concurrently
        async with aiohttp.ClientSession() as session:
            tasks = [
                self._fetch_feed(session, name, url, keywords, cutoff_date)
                for name, url in self.feeds.items()
            ]
            feed_results = await asyncio.gather(*tasks, return_exceptions=True)

            for result in feed_results:
                if isinstance(result, list):
                    all_results.extend(result)
                elif isinstance(result, Exception):
                    log.debug(f"RSS feed error: {result}")

        # Sort by relevance (keyword match count) and recency
        # Use timezone-aware datetime.min for comparison safety
        min_dt = datetime.min.replace(tzinfo=UTC)
        all_results.sort(
            key=lambda x: (-x.relevance_score, x.published_at or min_dt), reverse=True
        )

        # Limit results
        results = all_results[:max_results]
        print(f"    ✓ RSS: Found {len(results)} matching articles")
        log.info(
            f"RSS: found {len(results)} matching entries from {len(all_results)} total"
        )
        return results

    async def _fetch_feed(
        self,
        session: aiohttp.ClientSession,
        feed_name: str,
        feed_url: str,
        keywords: list[str],
        cutoff_date: datetime,
    ) -> list[APISearchResult]:
        """Fetch a single RSS feed and filter entries."""
        try:
            async with session.get(
                feed_url,
                timeout=aiohttp.ClientTimeout(total=15),
                headers={"User-Agent": "Nous/1.0 RSS Reader"},
            ) as response:
                if response.status != 200:
                    return []

                text = await response.text()
                return self._parse_rss(text, feed_name, keywords, cutoff_date)

        except Exception as e:
            log.debug(f"RSS feed {feed_name} failed: {e}")
            return []

    def _parse_rss(
        self,
        xml_text: str,
        feed_name: str,
        keywords: list[str],
        cutoff_date: datetime,
    ) -> list[APISearchResult]:
        """Parse RSS/Atom XML and filter by keywords."""
        results = []

        # Try RSS 2.0 format first (<item> elements)
        items = re.findall(
            r"<item[^>]*>(.*?)</item>", xml_text, re.DOTALL | re.IGNORECASE
        )

        # Fallback to Atom format (<entry> elements)
        if not items:
            items = re.findall(
                r"<entry[^>]*>(.*?)</entry>", xml_text, re.DOTALL | re.IGNORECASE
            )

        for item in items:
            # Extract fields with regex (avoiding XML parser dependency)
            title = self._extract_tag(item, "title") or ""
            link = self._extract_link(item)
            description = (
                self._extract_tag(item, "description")
                or self._extract_tag(item, "summary")
                or ""
            )
            pub_date = (
                self._extract_tag(item, "pubDate")
                or self._extract_tag(item, "published")
                or self._extract_tag(item, "updated")
            )

            # Clean HTML from description
            description = re.sub(r"<[^>]+>", "", description)
            description = description[:500]

            # Parse date
            published_at = self._parse_date(pub_date)
            if published_at and published_at < cutoff_date:
                continue  # Skip old entries

            # Calculate relevance based on keyword matches
            text_to_search = f"{title} {description}".lower()
            matches = sum(1 for kw in keywords if kw in text_to_search)

            if matches == 0:
                continue  # Skip non-matching entries

            relevance = min(1.0, matches / len(keywords)) if keywords else 0.5

            results.append(
                APISearchResult(
                    title=title,
                    url=link,
                    snippet=description,
                    source=self.name,
                    source_name=feed_name.replace("_", " ").title(),
                    published_at=published_at,
                    relevance_score=relevance,
                    source_type=self.source_type,
                    metadata={"feed": feed_name},
                )
            )

        return results

    def _extract_tag(self, text: str, tag: str) -> str | None:
        """Extract content from an XML tag."""
        # Handle CDATA
        pattern = rf"<{tag}[^>]*>(?:<!\[CDATA\[)?(.*?)(?:\]\]>)?</{tag}>"
        match = re.search(pattern, text, re.DOTALL | re.IGNORECASE)
        if match:
            return match.group(1).strip()
        return None

    def _extract_link(self, text: str) -> str:
        """Extract link from RSS item (handles both RSS and Atom formats)."""
        # RSS 2.0: <link>url</link>
        link_match = re.search(r"<link[^>]*>([^<]+)</link>", text, re.IGNORECASE)
        if link_match:
            return link_match.group(1).strip()

        # Atom: <link href="url" />
        href_match = re.search(
            r'<link[^>]*href=["\']([^"\']+)["\']', text, re.IGNORECASE
        )
        if href_match:
            return href_match.group(1).strip()

        return ""

    def _parse_date(self, date_str: str | None) -> datetime | None:
        """Parse various date formats from RSS feeds.

        Always returns timezone-aware datetime (UTC) to avoid comparison issues.
        """
        if not date_str:
            return None

        date_str = date_str.strip()

        # Handle common timezone abbreviations that strptime can't parse
        # Replace with offset or remove
        tz_replacements = {
            " GMT": " +0000",
            " UTC": " +0000",
            " EST": " -0500",
            " EDT": " -0400",
            " CST": " -0600",
            " CDT": " -0500",
            " MST": " -0700",
            " MDT": " -0600",
            " PST": " -0800",
            " PDT": " -0700",
        }
        for tz_name, tz_offset in tz_replacements.items():
            if tz_name in date_str:
                date_str = date_str.replace(tz_name, tz_offset)
                break

        # Formats that include timezone info
        formats_with_tz = [
            "%a, %d %b %Y %H:%M:%S %z",  # RFC 822: Mon, 01 Jan 2024 12:00:00 +0000
            "%Y-%m-%dT%H:%M:%S%z",  # ISO 8601 with offset
        ]

        # Formats without timezone info (will be assumed UTC)
        formats_naive = [
            "%a, %d %b %Y %H:%M:%S",  # RFC 822 without tz
            "%Y-%m-%dT%H:%M:%SZ",  # ISO 8601 UTC (Z suffix)
            "%Y-%m-%dT%H:%M:%S",  # ISO 8601 no tz
            "%Y-%m-%d %H:%M:%S",  # Simple format
            "%Y-%m-%d",  # Date only
        ]

        # Try timezone-aware formats first
        for fmt in formats_with_tz:
            try:
                return datetime.strptime(date_str, fmt)
            except ValueError:
                continue

        # Try naive formats and convert to UTC
        for fmt in formats_naive:
            try:
                dt = datetime.strptime(date_str, fmt)
                # Make timezone-aware (assume UTC)
                return dt.replace(tzinfo=UTC)
            except ValueError:
                continue

        # Try ISO format with fromisoformat
        try:
            dt = datetime.fromisoformat(date_str.replace("Z", "+00:00"))
            # Ensure it's timezone-aware
            if dt.tzinfo is None:
                dt = dt.replace(tzinfo=UTC)
            return dt
        except (ValueError, TypeError, AttributeError):
            pass

        return None


class ArxivProvider(SearchAPIProvider):
    """
    arXiv API provider.

    Free, no API key required.
    Rate limit: 1 request/3 seconds recommended.

    Docs: https://arxiv.org/help/api
    """

    BASE_URL = "http://export.arxiv.org/api/query"

    @property
    def name(self) -> str:
        return "arxiv"

    @property
    def source_type(self) -> SourceType:
        return SourceType.ACADEMIC

    async def search(
        self,
        query: str,
        max_results: int = 50,
        **kwargs,
    ) -> list[APISearchResult]:
        print("  → arXiv: Searching academic papers...")
        log.debug(f"arXiv: searching query='{query}'")
        params = {
            "search_query": f"all:{query}",
            "start": 0,
            "max_results": min(max_results, 100),
            "sortBy": "relevance",
            "sortOrder": "descending",
        }

        async with aiohttp.ClientSession() as session:
            try:
                async with session.get(
                    self.BASE_URL,
                    params=params,
                    timeout=aiohttp.ClientTimeout(total=30),
                ) as response:
                    if response.status != 200:
                        log.warning(f"arXiv: error status={response.status}")
                        print(f"arXiv error: {response.status}")
                        return []

                    # arXiv returns Atom XML
                    text = await response.text()
                    results = self._parse_arxiv_response(text, max_results)
                    print(f"    ✓ arXiv: Found {len(results)} papers")
                    log.info(
                        f"arXiv: received {len(results)} papers for query='{query}'"
                    )
                    return results

            except Exception as e:
                log.error(f"arXiv exception: {e}")
                print(f"arXiv error: {e}")
                return []

    def _parse_arxiv_response(
        self, xml_text: str, max_results: int
    ) -> list[APISearchResult]:
        """Parse arXiv Atom XML response."""
        results = []

        # Simple regex parsing (avoid xml dependency)
        entries = re.findall(r"<entry>(.*?)</entry>", xml_text, re.DOTALL)

        for i, entry in enumerate(entries[:max_results]):
            title_match = re.search(r"<title>(.*?)</title>", entry, re.DOTALL)
            summary_match = re.search(r"<summary>(.*?)</summary>", entry, re.DOTALL)
            id_match = re.search(r"<id>(.*?)</id>", entry)
            published_match = re.search(r"<published>(.*?)</published>", entry)

            # Get PDF link
            pdf_match = re.search(r'<link[^>]*title="pdf"[^>]*href="([^"]*)"', entry)

            # Get authors
            authors = re.findall(r"<author>\s*<name>(.*?)</name>", entry)

            title = title_match.group(1).strip() if title_match else ""
            title = re.sub(r"\s+", " ", title)  # Normalize whitespace

            summary = summary_match.group(1).strip() if summary_match else ""
            summary = re.sub(r"\s+", " ", summary)[:500]

            url = id_match.group(1) if id_match else ""
            pdf_url = pdf_match.group(1) if pdf_match else ""

            published = None
            if published_match:
                try:
                    published = datetime.fromisoformat(
                        published_match.group(1).replace("Z", "+00:00")
                    )
                except (ValueError, AttributeError):
                    pass

            results.append(
                APISearchResult(
                    title=title,
                    url=url,
                    snippet=summary,
                    source=self.name,
                    source_name="arXiv",
                    published_at=published,
                    relevance_score=1.0 - (i / max_results),
                    source_type=self.source_type,
                    metadata={
                        "authors": authors,
                        "pdf_url": pdf_url,
                        "arxiv_id": url.split("/")[-1] if url else "",
                    },
                )
            )

        return results


class RedditSearchProvider(SearchAPIProvider):
    """
    Reddit search provider (via JSON API).

    No API key required for basic search.
    Rate limited but generous for moderate use.
    """

    BASE_URL = "https://www.reddit.com/search.json"

    @property
    def name(self) -> str:
        return "reddit"

    @property
    def source_type(self) -> SourceType:
        return SourceType.SOCIAL

    async def search(
        self,
        query: str,
        max_results: int = 50,
        **kwargs,
    ) -> list[APISearchResult]:
        print("  → Reddit: Searching discussions...")
        log.debug(f"Reddit: searching query='{query}'")
        params = {
            "q": query,
            "limit": min(max_results, 100),
            "sort": "relevance",
            "t": "month",  # Time filter: hour, day, week, month, year, all
        }

        headers = {
            "User-Agent": "Nous/1.0 (research tool)",
        }

        async with aiohttp.ClientSession() as session:
            try:
                async with session.get(
                    self.BASE_URL,
                    params=params,
                    headers=headers,
                    timeout=aiohttp.ClientTimeout(total=30),
                ) as response:
                    if response.status != 200:
                        log.warning(f"Reddit: error status={response.status}")
                        print(f"Reddit error: {response.status}")
                        return []

                    data = await response.json()
                    children = data.get("data", {}).get("children", [])
                    print(f"    ✓ Reddit: Found {len(children)} posts")
                    log.info(
                        f"Reddit: received {len(children)} posts for query='{query}'"
                    )

                    results = []
                    for i, child in enumerate(children):
                        post = child.get("data", {})

                        # Skip if not a post with content
                        if not post.get("title"):
                            continue

                        # Build permalink
                        permalink = post.get("permalink", "")
                        url = f"https://www.reddit.com{permalink}" if permalink else ""

                        # Get snippet from selftext or title
                        snippet = post.get("selftext", "")[:500] or post.get(
                            "title", ""
                        )

                        results.append(
                            APISearchResult(
                                title=post.get("title", ""),
                                url=url,
                                snippet=snippet,
                                source=self.name,
                                source_name=f"r/{post.get('subreddit', '')}",
                                published_at=datetime.fromtimestamp(
                                    post.get("created_utc", 0)
                                ),
                                relevance_score=1.0 - (i / max_results),
                                source_type=self.source_type,
                                metadata={
                                    "subreddit": post.get("subreddit"),
                                    "score": post.get("score"),
                                    "num_comments": post.get("num_comments"),
                                    "author": post.get("author"),
                                },
                            )
                        )

                    return results

            except Exception as e:
                print(f"Reddit error: {e}")
                return []


class DuckDuckGoProvider(SearchAPIProvider):
    """
    DuckDuckGo web search provider.

    Free, no API key required.
    Provides general web coverage that specialized APIs miss.

    Requires: pip install ddgs
    """

    @property
    def name(self) -> str:
        return "duckduckgo"

    @property
    def source_type(self) -> SourceType:
        return SourceType.NEWS  # Default, actual type may vary

    async def search(
        self,
        query: str,
        max_results: int = 50,
        region: str | None = None,
        **kwargs,
    ) -> list[APISearchResult]:
        try:
            from ddgs import DDGS
        except ImportError:
            log.error("DuckDuckGo: ddgs not installed")
            print("DuckDuckGo error: ddgs not installed (pip install ddgs)")
            return []

        try:
            print("  → DuckDuckGo: Searching web...")
            log.debug(f"DuckDuckGo: searching query='{query}' region={region}")
            results = []

            # Map region to DDG format
            ddg_region = None
            if region:
                ddg_region = REGION_TO_DDG.get(region.lower())

            # Run sync DDG search in executor to avoid blocking
            def _search():
                ddgs = DDGS()
                search_kwargs: dict[str, int | str] = {
                    "max_results": min(max_results, 50)
                }
                if ddg_region:
                    search_kwargs["region"] = ddg_region
                return list(ddgs.text(query, **search_kwargs))

            ddg_results = await asyncio.get_running_loop().run_in_executor(
                None, _search
            )
            print(f"    ✓ DuckDuckGo: Found {len(ddg_results)} results")
            log.info(
                f"DuckDuckGo: received {len(ddg_results)} results for query='{query}'"
            )

            for i, result in enumerate(ddg_results):
                # Infer source type from domain
                url = result.get("href", "")
                source_type = self._infer_source_type(url)

                results.append(
                    APISearchResult(
                        title=result.get("title", ""),
                        url=url,
                        snippet=result.get("body", "")[:500],
                        source=self.name,
                        source_name=self._extract_domain(url),
                        published_at=None,  # DDG doesn't provide dates
                        relevance_score=1.0 - (i / max_results),
                        source_type=source_type,
                        metadata={
                            "search_engine": "duckduckgo",
                        },
                    )
                )

            return results

        except Exception as e:
            print(f"DuckDuckGo error: {e}")
            return []

    def _extract_domain(self, url: str) -> str:
        """Extract domain name from URL."""
        try:
            from urllib.parse import urlparse

            parsed = urlparse(url)
            domain = parsed.netloc.replace("www.", "")
            return domain
        except (ValueError, AttributeError):
            return "unknown"

    def _infer_source_type(self, url: str) -> SourceType:
        """Infer source type from URL domain."""
        domain = self._extract_domain(url).lower()

        # Academic indicators
        academic_indicators = [
            ".edu",
            "arxiv",
            "scholar",
            "academic",
            "journal",
            "research",
        ]
        if any(ind in domain for ind in academic_indicators):
            return SourceType.ACADEMIC

        # Social indicators
        social_indicators = [
            "reddit",
            "twitter",
            "x.com",
            "facebook",
            "linkedin",
            "medium",
        ]
        if any(ind in domain for ind in social_indicators):
            return SourceType.SOCIAL

        # Forum indicators
        forum_indicators = ["forum", "community", "discuss", "stackexchange", "quora"]
        if any(ind in domain for ind in forum_indicators):
            return SourceType.FORUM

        # Default to news/general
        return SourceType.NEWS


class MultiSourceSearch:
    """
    Unified search across multiple API providers.

    This is the main entry point for topic-specific discovery.

    Example:
        search = MultiSourceSearch()
        results = await search.search("AI regulation EU", sources=["news", "academic"])
    """

    def __init__(self, config: SearchAPIConfig | None = None):
        self.config = config or SearchAPIConfig()
        self._providers: dict[str, SearchAPIProvider] = {}
        self._init_providers()

    def _init_providers(self):
        """Initialize available providers."""
        # All providers are free, no API keys needed
        self._providers["rss"] = RSSNewsProvider()  # News from 20+ RSS feeds
        self._providers["arxiv"] = ArxivProvider()
        self._providers["reddit"] = RedditSearchProvider()
        self._providers["duckduckgo"] = DuckDuckGoProvider()

    @property
    def available_providers(self) -> list[str]:
        return list(self._providers.keys())

    async def search(
        self,
        query: str,
        sources: list[str] | None,
        max_results_per_source: int = 50,
    ) -> list[APISearchResult]:
        """
        Search across multiple sources.

        Args:
            query: Search query
            sources: List of source names or categories:
                     - Provider names: "gdelt", "arxiv", "reddit", etc.
                     - Categories: "news", "academic", "social", "all"
            max_results_per_source: Max results from each provider

        Returns:
            Combined list of APISearchResult, deduplicated by URL
        """
        log.info(f"MultiSourceSearch.search: query='{query}', sources={sources}")

        # Resolve source categories
        providers = self._resolve_sources(sources)

        if not providers:
            log.warning(
                f"No providers available. Available: {self.available_providers}"
            )
            print(f"No providers available. Available: {self.available_providers}")
            return []

        # Determine regions to search
        regions_to_search = [self.config.region] if self.config.region else [None]
        if self.config.regions:
            regions_to_search = self.config.regions

        # Search all providers in parallel, across all regions
        tasks = []
        for region in regions_to_search:
            for provider in providers:
                tasks.append(
                    provider.search(
                        query,
                        max_results=max_results_per_source,
                        language=self.config.language,
                        days_back=self.config.days_back,
                        region=region,
                    )
                )

        results_lists = await asyncio.gather(*tasks, return_exceptions=True)

        # Combine and deduplicate
        all_results = []
        seen_urls = set()

        for i, results in enumerate(results_lists):
            if isinstance(results, BaseException):
                log.error(f"Provider error (task {i}): {results}")
                print(f"Provider error: {results}")
                continue

            log.debug(f"Task {i}: received {len(results)} results")
            for result in results:
                if result.url not in seen_urls:
                    seen_urls.add(result.url)
                    all_results.append(result)

        # Sort by relevance score
        all_results.sort(key=lambda x: x.relevance_score, reverse=True)

        # Screenshot fallback for blocked sites (if enabled)
        if self.config.use_screenshot_fallback and (
            "news" in (sources or []) or "all" in (sources or [])
        ):
            try:
                screenshot_results = await self._search_screenshot_sites(query)
                for result in screenshot_results:
                    if result.url not in seen_urls:
                        seen_urls.add(result.url)
                        all_results.append(result)
            except Exception as e:
                log.error(f"Screenshot fallback error: {e}")

        log.info(
            f"MultiSourceSearch complete: {len(all_results)} unique results from {len(tasks)} provider tasks"
        )
        return all_results

    async def _search_screenshot_sites(self, query: str) -> list[APISearchResult]:
        """Extract content from blocked sites using screenshot + LLM."""
        try:
            from .screenshot_extractor import ScreenshotExtractor
        except ImportError:
            log.warning("screenshot_extractor not available")
            return []

        async with ScreenshotExtractor(
            llm_provider=self.config.screenshot_llm_provider
        ) as extractor:
            return await extractor.extract_from_fallback_sites(query)

    def _resolve_sources(self, sources: list[str] | None) -> list[SearchAPIProvider]:
        """Resolve source names/categories to provider instances."""
        if sources is None:
            sources = ["all"]

        log.debug(f"Resolving sources: {sources}")
        providers = []

        for source in sources:
            source = source.lower()

            # Direct provider name
            if source in self._providers:
                providers.append(self._providers[source])
                continue

            # Category mappings
            if source == "all":
                providers.extend(self._providers.values())
            elif source == "news":
                if "rss" in self._providers:
                    providers.append(self._providers["rss"])
            elif source == "academic":
                if "arxiv" in self._providers:
                    providers.append(self._providers["arxiv"])
            elif source == "social":
                if "reddit" in self._providers:
                    providers.append(self._providers["reddit"])
            elif source == "web":
                for name in ["duckduckgo"]:
                    if name in self._providers:
                        providers.append(self._providers[name])

        # Deduplicate
        unique_providers = list({id(p): p for p in providers}.values())
        log.debug(
            f"Resolved to {len(unique_providers)} providers: {[p.name for p in unique_providers]}"
        )
        return unique_providers


# Convenience functions
async def search_news(query: str, max_results: int = 100) -> list[APISearchResult]:
    """Search news sources via RSS feeds from 20+ major outlets."""
    search = MultiSourceSearch()
    return await search.search(
        query, sources=["news"], max_results_per_source=max_results
    )


async def search_academic(query: str, max_results: int = 100) -> list[APISearchResult]:
    """Search academic sources (arXiv)."""
    search = MultiSourceSearch()
    return await search.search(
        query, sources=["academic"], max_results_per_source=max_results
    )


async def search_social(query: str, max_results: int = 100) -> list[APISearchResult]:
    """Search social sources (Reddit)."""
    search = MultiSourceSearch()
    return await search.search(
        query, sources=["social"], max_results_per_source=max_results
    )


async def search_web(query: str, max_results: int = 50) -> list[APISearchResult]:
    """Search general web via DuckDuckGo."""
    search = MultiSourceSearch()
    return await search.search(
        query, sources=["web"], max_results_per_source=max_results
    )


async def search_all(
    query: str, max_results_per_source: int = 50
) -> list[APISearchResult]:
    """Search all available sources."""
    search = MultiSourceSearch()
    return await search.search(
        query, sources=["all"], max_results_per_source=max_results_per_source
    )
