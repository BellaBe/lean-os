"""
Search API Discovery

Topic-specific source discovery using actual search APIs instead of sitemap crawling.

Supported providers:
- NewsAPI.org (news, free tier: 100 req/day)
- GDELT (news, free, massive historical)
- Semantic Scholar (academic, free)
- arXiv (academic, free)
- Reddit (social, free with limits)
- Hacker News (social, free)
- DuckDuckGo (web, free, general web coverage) - requires: pip install ddgs

Source categories:
- "news"     -> NewsAPI, GDELT
- "academic" -> Semantic Scholar, arXiv
- "social"   -> Reddit, HackerNews
- "web"      -> DuckDuckGo
- "all"      -> All providers

The key insight: Use search APIs for DISCOVERY (topic-relevant URLs),
then optionally use sitemaps for EXPANSION within discovered domains.
"""

import asyncio
import os
import re
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from typing import Optional
from urllib.parse import urlencode

import aiohttp

from ...domain import SourceType


@dataclass
class SearchAPIConfig:
    """Configuration for search API providers."""

    # API keys (from env vars if not provided)
    newsapi_key: str | None
    bing_key: str | None

    # Limits
    max_results_per_provider: int = 50
    timeout_seconds: int = 30

    # Filtering
    language: str = "en"
    days_back: int = 30  # For news sources

    def __post_init__(self):
        # Load from environment if not provided
        self.newsapi_key = self.newsapi_key or os.getenv("NEWSAPI_KEY")
        self.bing_key = self.bing_key or os.getenv("BING_SEARCH_KEY")


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


class NewsAPIProvider(SearchAPIProvider):
    """
    NewsAPI.org provider.

    Free tier: 100 requests/day, 1 month history
    Paid: $449/month for 250k requests

    Docs: https://newsapi.org/docs
    """

    BASE_URL = "https://newsapi.org/v2/everything"

    def __init__(self, api_key: str):
        self.api_key = api_key

    @property
    def name(self) -> str:
        return "newsapi"

    @property
    def source_type(self) -> SourceType:
        return SourceType.NEWS

    async def search(
        self,
        query: str,
        max_results: int = 50,
        language: str = "en",
        days_back: int = 30,
        **kwargs,
    ) -> list[APISearchResult]:
        if not self.api_key:
            return []

        from_date = (
            datetime.now(timezone.utc)  # noqa: UP017
            - timedelta(days=days_back)
        ).strftime("%Y-%m-%d")

        params = {
            "q": query,
            "language": language,
            "from": from_date,
            "sortBy": "relevancy",
            "pageSize": min(max_results, 100),
            "apiKey": self.api_key,
        }

        async with aiohttp.ClientSession() as session:
            try:
                async with session.get(
                    self.BASE_URL,
                    params=params,
                    timeout=aiohttp.ClientTimeout(total=30),
                ) as response:
                    if response.status != 200:
                        print(f"NewsAPI error: {response.status}")
                        return []

                    data = await response.json()

                    if data.get("status") != "ok":
                        print(f"NewsAPI error: {data.get('message')}")
                        return []

                    results = []
                    for i, article in enumerate(data.get("articles", [])):
                        results.append(
                            APISearchResult(
                                title=article.get("title", ""),
                                url=article.get("url", ""),
                                snippet=article.get("description", ""),
                                source=self.name,
                                source_name=article.get("source", {}).get("name", ""),
                                published_at=self._parse_date(article.get("publishedAt")),
                                relevance_score=1.0 - (i / max_results),  # Position-based
                                source_type=self.source_type,
                                metadata={
                                    "author": article.get("author"),
                                    "image_url": article.get("urlToImage"),
                                },
                            )
                        )

                    return results

            except Exception as e:
                print(f"NewsAPI error: {e}")
                return []

    def _parse_date(self, date_str: str | None) -> datetime | None:
        if not date_str:
            return None
        try:
            return datetime.fromisoformat(date_str.replace("Z", "+00:00"))
        except Exception:
            return None


class GDELTProvider(SearchAPIProvider):
    """
    GDELT Project provider.

    Free, no API key required!
    Massive database of global news.

    Docs: https://blog.gdeltproject.org/gdelt-doc-2-0-api-debuts/
    """

    BASE_URL = "https://api.gdeltproject.org/api/v2/doc/doc"

    @property
    def name(self) -> str:
        return "gdelt"

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
        # GDELT query format
        params = {
            "query": query,
            "mode": "artlist",
            "maxrecords": min(max_results, 250),
            "format": "json",
            "timespan": f"{days_back}d",
            "sort": "relevance",
        }

        url = f"{self.BASE_URL}?{urlencode(params)}"

        async with aiohttp.ClientSession() as session:
            try:
                async with session.get(
                    url,
                    timeout=aiohttp.ClientTimeout(total=30),
                ) as response:
                    if response.status != 200:
                        print(f"GDELT error: {response.status}")
                        return []

                    data = await response.json()

                    results = []
                    for i, article in enumerate(data.get("articles", [])):
                        results.append(
                            APISearchResult(
                                title=article.get("title", ""),
                                url=article.get("url", ""),
                                snippet=article.get("seendate", ""),  # GDELT doesn't have snippets
                                source=self.name,
                                source_name=article.get("domain", ""),
                                published_at=self._parse_gdelt_date(article.get("seendate")),
                                relevance_score=1.0 - (i / max_results),
                                source_type=self.source_type,
                                metadata={
                                    "domain": article.get("domain"),
                                    "language": article.get("language"),
                                    "sourcecountry": article.get("sourcecountry"),
                                },
                            )
                        )

                    return results

            except Exception as e:
                print(f"GDELT error: {e}")
                return []

    def _parse_gdelt_date(self, date_str: str | None) -> datetime | None:
        if not date_str:
            return None
        try:
            # GDELT format: 20240115T120000Z
            return datetime.strptime(date_str, "%Y%m%dT%H%M%SZ")
        except Exception:
            return None


class SemanticScholarProvider(SearchAPIProvider):
    """
    Semantic Scholar API provider.

    Free, no API key required (but recommended for higher limits).
    100 requests/5 minutes without key.

    Docs: https://api.semanticscholar.org/
    """

    BASE_URL = "https://api.semanticscholar.org/graph/v1/paper/search"

    def __init__(self, api_key: str | None = None):
        self.api_key = api_key

    @property
    def name(self) -> str:
        return "semantic_scholar"

    @property
    def source_type(self) -> SourceType:
        return SourceType.ACADEMIC

    async def search(
        self,
        query: str,
        max_results: int = 50,
        **kwargs,
    ) -> list[APISearchResult]:
        params = {
            "query": query,
            "limit": min(max_results, 100),
            "fields": "title,abstract,url,authors,year,citationCount,venue",
        }

        headers = {}
        if self.api_key:
            headers["x-api-key"] = self.api_key

        async with aiohttp.ClientSession() as session:
            try:
                async with session.get(
                    self.BASE_URL,
                    params=params,
                    headers=headers,
                    timeout=aiohttp.ClientTimeout(total=30),
                ) as response:
                    if response.status != 200:
                        print(f"Semantic Scholar error: {response.status}")
                        return []

                    data = await response.json()

                    results = []
                    for i, paper in enumerate(data.get("data", [])):
                        # Build URL (S2 doesn't always have direct URLs)
                        paper_id = paper.get("paperId", "")
                        url = (
                            paper.get("url") or f"https://www.semanticscholar.org/paper/{paper_id}"
                        )

                        # Get author names
                        authors = [a.get("name", "") for a in paper.get("authors", [])]

                        results.append(
                            APISearchResult(
                                title=paper.get("title", ""),
                                url=url,
                                snippet=paper.get("abstract", "")[:500]
                                if paper.get("abstract")
                                else "",
                                source=self.name,
                                source_name=paper.get("venue", ""),
                                published_at=None,  # Only have year
                                relevance_score=1.0 - (i / max_results),
                                source_type=self.source_type,
                                metadata={
                                    "authors": authors,
                                    "year": paper.get("year"),
                                    "citation_count": paper.get("citationCount"),
                                    "paper_id": paper_id,
                                },
                            )
                        )

                    return results

            except Exception as e:
                print(f"Semantic Scholar error: {e}")
                return []


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
                        print(f"arXiv error: {response.status}")
                        return []

                    # arXiv returns Atom XML
                    text = await response.text()
                    return self._parse_arxiv_response(text, max_results)

            except Exception as e:
                print(f"arXiv error: {e}")
                return []

    def _parse_arxiv_response(self, xml_text: str, max_results: int) -> list[APISearchResult]:
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
                except Exception:
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
                        print(f"Reddit error: {response.status}")
                        return []

                    data = await response.json()

                    results = []
                    for i, child in enumerate(data.get("data", {}).get("children", [])):
                        post = child.get("data", {})

                        # Skip if not a post with content
                        if not post.get("title"):
                            continue

                        # Build permalink
                        permalink = post.get("permalink", "")
                        url = f"https://www.reddit.com{permalink}" if permalink else ""

                        # Get snippet from selftext or title
                        snippet = post.get("selftext", "")[:500] or post.get("title", "")

                        results.append(
                            APISearchResult(
                                title=post.get("title", ""),
                                url=url,
                                snippet=snippet,
                                source=self.name,
                                source_name=f"r/{post.get('subreddit', '')}",
                                published_at=datetime.fromtimestamp(post.get("created_utc", 0)),
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


class HackerNewsProvider(SearchAPIProvider):
    """
    Hacker News search provider (via Algolia API).

    Free, no API key required.

    Docs: https://hn.algolia.com/api
    """

    BASE_URL = "https://hn.algolia.com/api/v1/search"

    @property
    def name(self) -> str:
        return "hackernews"

    @property
    def source_type(self) -> SourceType:
        return SourceType.SOCIAL

    async def search(
        self,
        query: str,
        max_results: int = 50,
        **kwargs,
    ) -> list[APISearchResult]:
        params = {
            "query": query,
            "hitsPerPage": min(max_results, 100),
            "tags": "story",  # Only stories, not comments
        }

        async with aiohttp.ClientSession() as session:
            try:
                async with session.get(
                    self.BASE_URL,
                    params=params,
                    timeout=aiohttp.ClientTimeout(total=30),
                ) as response:
                    if response.status != 200:
                        print(f"HackerNews error: {response.status}")
                        return []

                    data = await response.json()

                    results = []
                    for i, hit in enumerate(data.get("hits", [])):
                        # HN stories can link externally or be self-posts
                        url = (
                            hit.get("url")
                            or f"https://news.ycombinator.com/item?id={hit.get('objectID')}"
                        )

                        results.append(
                            APISearchResult(
                                title=hit.get("title", ""),
                                url=url,
                                snippet=hit.get("story_text", "")[:500]
                                if hit.get("story_text")
                                else "",
                                source=self.name,
                                source_name="Hacker News",
                                published_at=datetime.fromtimestamp(hit.get("created_at_i", 0)),
                                relevance_score=1.0 - (i / max_results),
                                source_type=self.source_type,
                                metadata={
                                    "points": hit.get("points"),
                                    "num_comments": hit.get("num_comments"),
                                    "author": hit.get("author"),
                                    "hn_id": hit.get("objectID"),
                                },
                            )
                        )

                    return results

            except Exception as e:
                print(f"HackerNews error: {e}")
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
        **kwargs,
    ) -> list[APISearchResult]:
        try:
            from ddgs import DDGS
        except ImportError:
            print("DuckDuckGo error: ddgs not installed (pip install ddgs)")
            return []

        try:
            results = []

            # Run sync DDG search in executor to avoid blocking
            import asyncio

            def _search():
                ddgs = DDGS()
                return list(ddgs.text(query, max_results=min(max_results, 50)))

            loop = asyncio.get_event_loop()
            ddg_results = await loop.run_in_executor(None, _search)

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
        except Exception:
            return "unknown"

    def _infer_source_type(self, url: str) -> SourceType:
        """Infer source type from URL domain."""
        domain = self._extract_domain(url).lower()

        # Academic indicators
        academic_indicators = [".edu", "arxiv", "scholar", "academic", "journal", "research"]
        if any(ind in domain for ind in academic_indicators):
            return SourceType.ACADEMIC

        # Social indicators
        social_indicators = ["reddit", "twitter", "x.com", "facebook", "linkedin", "medium"]
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
        self.config = config or SearchAPIConfig(
            config.newsapi_key if config else None, config.bing_key if config else None
        )
        self._providers: dict[str, SearchAPIProvider] = {}
        self._init_providers()

    def _init_providers(self):
        """Initialize available providers."""
        # News providers
        if self.config.newsapi_key:
            self._providers["newsapi"] = NewsAPIProvider(self.config.newsapi_key)

        # Always available (no API key needed)
        self._providers["gdelt"] = GDELTProvider()
        self._providers["semantic_scholar"] = SemanticScholarProvider()
        self._providers["arxiv"] = ArxivProvider()
        self._providers["reddit"] = RedditSearchProvider()
        self._providers["hackernews"] = HackerNewsProvider()
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
        # Resolve source categories
        providers = self._resolve_sources(sources)

        if not providers:
            print(f"No providers available. Available: {self.available_providers}")
            return []

        # Search all providers in parallel
        tasks = [
            provider.search(
                query,
                max_results=max_results_per_source,
                language=self.config.language,
                days_back=self.config.days_back,
            )
            for provider in providers
        ]

        results_lists = await asyncio.gather(*tasks, return_exceptions=True)

        # Combine and deduplicate
        all_results = []
        seen_urls = set()

        for results in results_lists:
            if isinstance(results, BaseException):
                print(f"Provider error: {results}")
                continue

            for result in results:
                if result.url not in seen_urls:
                    seen_urls.add(result.url)
                    all_results.append(result)

        # Sort by relevance score
        all_results.sort(key=lambda x: x.relevance_score, reverse=True)

        return all_results

    def _resolve_sources(self, sources: list[str] | None) -> list[SearchAPIProvider]:
        """Resolve source names/categories to provider instances."""
        if sources is None:
            sources = ["all"]

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
                for name in ["newsapi", "gdelt"]:
                    if name in self._providers:
                        providers.append(self._providers[name])
            elif source == "academic":
                for name in ["semantic_scholar", "arxiv"]:
                    if name in self._providers:
                        providers.append(self._providers[name])
            elif source == "social":
                for name in ["reddit", "hackernews"]:
                    if name in self._providers:
                        providers.append(self._providers[name])
            elif source == "web":
                for name in ["duckduckgo"]:
                    if name in self._providers:
                        providers.append(self._providers[name])

        # Deduplicate
        return list({id(p): p for p in providers}.values())


# Convenience functions
async def search_news(query: str, max_results: int = 100) -> list[APISearchResult]:
    """Search news sources (GDELT + NewsAPI if configured)."""
    search = MultiSourceSearch()
    return await search.search(query, sources=["news"], max_results_per_source=max_results)


async def search_academic(query: str, max_results: int = 100) -> list[APISearchResult]:
    """Search academic sources (Semantic Scholar + arXiv)."""
    search = MultiSourceSearch()
    return await search.search(query, sources=["academic"], max_results_per_source=max_results)


async def search_social(query: str, max_results: int = 100) -> list[APISearchResult]:
    """Search social sources (Reddit + HackerNews)."""
    search = MultiSourceSearch()
    return await search.search(query, sources=["social"], max_results_per_source=max_results)


async def search_web(query: str, max_results: int = 50) -> list[APISearchResult]:
    """Search general web via DuckDuckGo."""
    search = MultiSourceSearch()
    return await search.search(query, sources=["web"], max_results_per_source=max_results)


async def search_all(query: str, max_results_per_source: int = 50) -> list[APISearchResult]:
    """Search all available sources."""
    search = MultiSourceSearch()
    return await search.search(
        query, sources=["all"], max_results_per_source=max_results_per_source
    )
