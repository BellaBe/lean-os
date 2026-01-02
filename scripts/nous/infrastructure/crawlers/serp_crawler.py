"""
SERP Crawler - Search Engine Results Page Extraction

Implements the two-phase approach from Crawl4AI tutorial:
1. Generate CSS extraction schemas using LLM (one-time)
2. Use JsonCssExtractionStrategy for fast, LLM-free extraction

Supports: Google, DuckDuckGo (fallback, no captchas)
"""

import json
from abc import ABC, abstractmethod
from dataclasses import dataclass
from datetime import datetime
from typing import Any
from urllib.parse import quote_plus

from ...domain import SearchResponse, SearchResult
from .schema_manager import SchemaManager

# Pre-defined schemas for known SERP structures
# These can be used as fallbacks or starting points

GOOGLE_ORGANIC_SCHEMA = {
    "name": "Google Organic Results",
    "baseSelector": "div.g",
    "fields": [
        {"name": "title", "selector": "h3", "type": "text"},
        {"name": "url", "selector": "a", "type": "attribute", "attribute": "href"},
        {"name": "snippet", "selector": "div[data-sncf], div.VwiC3b", "type": "text"},
        {"name": "date", "selector": "span.LEwnzc", "type": "text"},
    ],
}

GOOGLE_TOP_STORIES_SCHEMA = {
    "name": "Google Top Stories",
    "baseSelector": "div[data-hveid] g-card",
    "fields": [
        {"name": "title", "selector": "div[role='heading']", "type": "text"},
        {"name": "url", "selector": "a", "type": "attribute", "attribute": "href"},
        {"name": "source", "selector": "g-img + div", "type": "text"},
        {"name": "time", "selector": "div > span", "type": "text"},
    ],
}

DUCKDUCKGO_RESULTS_SCHEMA = {
    "name": "DuckDuckGo Results",
    "baseSelector": "article[data-testid='result']",
    "fields": [
        {"name": "title", "selector": "h2 a span", "type": "text"},
        {"name": "url", "selector": "h2 a", "type": "attribute", "attribute": "href"},
        {
            "name": "snippet",
            "selector": "div[data-result='snippet'] span",
            "type": "text",
        },
    ],
}


@dataclass
class SerpConfig:
    """Configuration for SERP crawling."""

    num_results: int = 10
    start_page: int = 0
    language: str = "en"
    country: str = "us"
    time_range: str | None = None  # d=day, w=week, m=month, y=year
    headless: bool = True
    delay_before_return: float = 1.0


class SerpCrawler(ABC):
    """Base class for SERP crawlers."""

    @abstractmethod
    async def search(
        self, query: str, config: SerpConfig | None = None
    ) -> SearchResponse:
        """Execute search and return parsed results."""

    @abstractmethod
    async def close(self) -> None:
        """Close the crawler and release resources."""
        ...


class Crawl4AISerpCrawler(SerpCrawler):
    """
    SERP crawler using Crawl4AI.

    Uses the two-phase approach:
    1. Fetch HTML with AsyncWebCrawler
    2. Extract with JsonCssExtractionStrategy (no LLM per-request)
    """

    def __init__(
        self,
        schema_manager: SchemaManager | None = None,
        use_fallback_schemas: bool = True,
    ):
        self.schema_manager = schema_manager
        self.use_fallback_schemas = use_fallback_schemas
        self._crawler: Any = None

    async def _get_crawler(self) -> Any:
        """Lazy initialization of crawler."""
        if self._crawler is None:
            try:
                from crawl4ai import AsyncWebCrawler, BrowserConfig

                browser_config = BrowserConfig(
                    headless=True,
                    verbose=False,
                )
                self._crawler = AsyncWebCrawler(config=browser_config)
                await self._crawler.start()
            except ImportError:
                raise ImportError("crawl4ai not installed. Run: pip install crawl4ai")
        return self._crawler

    async def close(self) -> None:
        """Close the crawler and release resources."""
        if self._crawler:
            await self._crawler.close()
            self._crawler = None

    async def __aenter__(self) -> "SerpCrawler":
        await self._get_crawler()
        return self

    async def __aexit__(
        self,
        exc_type: type[BaseException] | None,
        exc_val: BaseException | None,
        exc_tb: Any,
    ) -> None:
        await self.close()

    def _build_google_url(self, query: str, config: SerpConfig) -> str:
        """Build Google search URL with parameters."""
        base = "https://www.google.com/search"
        params = {
            "q": query,
            "start": config.start_page * config.num_results,
            "num": config.num_results,
            "hl": config.language,
            "gl": config.country,
        }
        if config.time_range:
            params["tbs"] = f"qdr:{config.time_range}"

        query_string = "&".join(f"{k}={quote_plus(str(v))}" for k, v in params.items())
        return f"{base}?{query_string}"

    def _build_duckduckgo_url(self, query: str, config: SerpConfig) -> str:
        """Build DuckDuckGo search URL."""
        base = "https://duckduckgo.com/"
        params = {"q": query, "kl": f"{config.country}-{config.language}"}
        if config.time_range:
            time_map = {"d": "d", "w": "w", "m": "m", "y": "y"}
            params["df"] = time_map.get(config.time_range, "")

        query_string = "&".join(f"{k}={quote_plus(str(v))}" for k, v in params.items())
        return f"{base}?{query_string}"

    async def _extract_with_schema(
        self,
        html: str,
        schema: dict[str, Any],
    ) -> list[dict[str, Any]]:
        """Extract data from HTML using CSS schema (no LLM)."""
        try:
            from crawl4ai import JsonCssExtractionStrategy

            strategy = JsonCssExtractionStrategy(schema, verbose=False)
            # Use the strategy's run method directly (independent of crawler)
            results = strategy.run("", [html])

            if results:
                return json.loads(results) if isinstance(results, str) else results
            return []
        except Exception as e:
            print(f"Extraction error: {e}")
            return []

    async def _get_schema(self, schema_name: str, fallback: dict) -> dict[str, Any]:
        """Get schema from manager or use fallback."""
        if self.schema_manager:
            schema = await self.schema_manager.get(schema_name)
            if schema:
                return schema

        if self.use_fallback_schemas:
            return fallback

        raise ValueError(f"No schema available for {schema_name}")

    async def search(
        self,
        query: str,
        config: SerpConfig | None = None,
    ) -> SearchResponse:
        """
        Execute search and extract results.

        Args:
            query: Search query
            config: Optional search configuration

        Returns:
            SearchResponse with parsed results
        """
        config = config or SerpConfig()

        # Try Google first, fall back to DuckDuckGo on failure
        try:
            return await self._search_google(query, config)
        except Exception as e:
            print(f"Google search failed: {e}, trying DuckDuckGo...")
            return await self._search_duckduckgo(query, config)

    async def _search_google(
        self,
        query: str,
        config: SerpConfig,
    ) -> SearchResponse:
        """Execute Google search."""
        from crawl4ai import CacheMode, CrawlerRunConfig

        crawler = await self._get_crawler()
        url = self._build_google_url(query, config)

        run_config = CrawlerRunConfig(
            cache_mode=CacheMode.BYPASS,
            delay_before_return_html=config.delay_before_return,
            # Keep IDs and classes for CSS extraction
            remove_forms=True,
            excluded_tags=["script", "style", "noscript"],
        )

        result = await crawler.arun(url=url, config=run_config)

        if not result.success:
            raise Exception(f"Failed to crawl Google: {result.error_message}")

        html = result.cleaned_html or result.html

        # Extract organic results
        organic_schema = await self._get_schema(
            "google_organic",
            GOOGLE_ORGANIC_SCHEMA,
        )
        organic_raw = await self._extract_with_schema(html, organic_schema)

        # Extract top stories
        stories_schema = await self._get_schema(
            "google_top_stories",
            GOOGLE_TOP_STORIES_SCHEMA,
        )
        stories_raw = await self._extract_with_schema(html, stories_schema)

        # Parse into domain objects
        results = []
        for i, item in enumerate(organic_raw):
            if not item.get("url"):
                continue
            results.append(
                SearchResult(
                    title=item.get("title", ""),
                    url=item.get("url", ""),
                    snippet=item.get("snippet", ""),
                    position=i + 1,
                    date=item.get("date"),
                )
            )

        return SearchResponse(
            query=query,
            results=results,
            top_stories=stories_raw,
            related_queries=[],
            searched_at=datetime.utcnow(),
            source="google",
        )

    async def _search_duckduckgo(
        self,
        query: str,
        config: SerpConfig,
    ) -> SearchResponse:
        """Execute DuckDuckGo search (no captchas, privacy-friendly)."""
        from crawl4ai import CacheMode, CrawlerRunConfig

        crawler = await self._get_crawler()
        url = self._build_duckduckgo_url(query, config)

        # DuckDuckGo loads results via JS, need to wait
        run_config = CrawlerRunConfig(
            cache_mode=CacheMode.BYPASS,
            delay_before_return_html=2.0,  # DDG needs more time
            wait_for="css:article[data-testid='result']",
            excluded_tags=["script", "style", "noscript"],
        )

        result = await crawler.arun(url=url, config=run_config)

        if not result.success:
            raise Exception(f"Failed to crawl DuckDuckGo: {result.error_message}")

        html = result.cleaned_html or result.html

        # Extract results
        schema = await self._get_schema(
            "duckduckgo_results",
            DUCKDUCKGO_RESULTS_SCHEMA,
        )
        raw_results = await self._extract_with_schema(html, schema)

        results = []
        for i, item in enumerate(raw_results):
            if not item.get("url"):
                continue
            results.append(
                SearchResult(
                    title=item.get("title", ""),
                    url=item.get("url", ""),
                    snippet=item.get("snippet", ""),
                    position=i + 1,
                )
            )

        return SearchResponse(
            query=query,
            results=results,
            top_stories=[],
            related_queries=[],
            searched_at=datetime.utcnow(),
            source="duckduckgo",
        )


class MockSerpCrawler(SerpCrawler):
    """Mock crawler for testing without browser."""

    def __init__(self, mock_results: list[SearchResult] | None = None):
        self.mock_results = mock_results or [
            SearchResult(
                title="Test Result 1",
                url="https://example.com/1",
                snippet="This is a test result snippet.",
                position=1,
            ),
            SearchResult(
                title="Test Result 2",
                url="https://example.com/2",
                snippet="Another test result snippet.",
                position=2,
            ),
        ]

    async def search(
        self,
        query: str,
        config: SerpConfig | None = None,
    ) -> SearchResponse:
        # Respect num_results from config if provided
        results = self.mock_results
        if config and config.num_results:
            results = results[: config.num_results]

        return SearchResponse(
            query=query,
            results=results,
            top_stories=[],
            related_queries=[],
            searched_at=datetime.utcnow(),
            source="mock",
        )
