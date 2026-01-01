"""
Content Crawler - Extract and process page content

Handles fetching and processing content from discovered source URLs.
Outputs clean markdown suitable for LLM processing.
"""

import asyncio
from dataclasses import dataclass, field
from datetime import datetime
from typing import Any
from urllib.parse import urlparse

from ...domain import SignalZone, SourceId, SourceNode, SourceType


@dataclass
class ContentConfig:
    """Configuration for content crawling."""

    headless: bool = True
    timeout: int = 30000
    wait_for_selector: str | None = None
    exclude_tags: list[str] = field(
        default_factory=lambda: ["nav", "footer", "aside", "header", "script", "style", "noscript"]
    )
    word_count_threshold: int = 50
    use_pruning_filter: bool = True  # Use PruningContentFilter for cleaner markdown


@dataclass
class CrawlResult:
    """Result of a content crawl."""

    url: str
    success: bool
    title: str = ""
    markdown: str = ""
    fit_markdown: str = ""  # Filtered/pruned markdown
    html: str = ""
    links: list[dict] = field(default_factory=list)
    images: list[dict] = field(default_factory=list)
    metadata: dict = field(default_factory=dict)
    error: str | None = None
    crawled_at: datetime = field(default_factory=datetime.utcnow)


class ContentCrawler:
    """
    Crawler for extracting content from web pages.

    Uses Crawl4AI's markdown generation with optional content filtering
    for clean, LLM-friendly output.
    """

    def __init__(self, config: ContentConfig | None = None) -> None:
        self.config = config or ContentConfig()
        self._crawler: Any = None

    async def _get_crawler(self) -> Any:
        """Lazy initialization of crawler."""
        if self._crawler is None:
            try:
                from crawl4ai import AsyncWebCrawler, BrowserConfig

                browser_config = BrowserConfig(
                    headless=self.config.headless,
                    verbose=False,
                )
                self._crawler = AsyncWebCrawler(config=browser_config)
                await self._crawler.start()
            except ImportError:
                raise ImportError("crawl4ai not installed. Run: pip install crawl4ai")
        return self._crawler

    async def close(self) -> None:
        """Close the crawler."""
        if self._crawler:
            await self._crawler.close()
            self._crawler = None

    async def __aenter__(self) -> "ContentCrawler":
        await self._get_crawler()
        return self

    async def __aexit__(
        self,
        exc_type: type[BaseException] | None,
        exc_val: BaseException | None,
        exc_tb: Any,
    ) -> None:
        await self.close()

    def _detect_source_type(self, url: str) -> SourceType:
        """Detect source type from URL."""
        domain = urlparse(url).netloc.lower()

        # Academic sources
        academic_patterns = [
            "arxiv.org",
            "scholar.google",
            "semanticscholar",
            ".edu",
            "researchgate",
        ]
        if any(p in domain for p in academic_patterns):
            return SourceType.ACADEMIC

        # Government sources
        if ".gov" in domain:
            return SourceType.GOVERNMENT

        # Social platforms
        social_patterns = ["reddit.com", "twitter.com", "x.com", "facebook.com", "linkedin.com"]
        if any(p in domain for p in social_patterns):
            return SourceType.SOCIAL

        # Video platforms
        video_patterns = ["youtube.com", "vimeo.com", "tiktok.com"]
        if any(p in domain for p in video_patterns):
            return SourceType.VIDEO

        # Forums
        forum_patterns = ["forum", "community", "discuss", "hackernews", "news.ycombinator"]
        if any(p in domain for p in forum_patterns):
            return SourceType.FORUM

        # Major news outlets (non-exhaustive)
        news_patterns = [
            "nytimes.com",
            "wsj.com",
            "reuters.com",
            "bbc.com",
            "cnn.com",
            "bloomberg.com",
            "ft.com",
            "washingtonpost.com",
            "theguardian.com",
            "news",
            "times",
            "post",
            "journal",
        ]
        if any(p in domain for p in news_patterns):
            return SourceType.NEWS

        # Blog patterns
        blog_patterns = ["blog", "medium.com", "substack.com", "wordpress.com"]
        if any(p in domain for p in blog_patterns):
            return SourceType.BLOG

        return SourceType.UNKNOWN

    def _detect_signal_zone(self, url: str, source_type: SourceType) -> SignalZone:
        """Detect signal zone based on URL and source type."""
        if source_type in [SourceType.NEWS, SourceType.GOVERNMENT, SourceType.ACADEMIC]:
            return SignalZone.INSTITUTIONAL

        if source_type in [SourceType.SOCIAL, SourceType.FORUM, SourceType.BLOG]:
            return SignalZone.GRASSROOTS

        # Check for speculative patterns
        domain = urlparse(url).netloc.lower()
        speculative_patterns = ["4chan", "crypto", "defi", "anon"]
        if any(p in domain for p in speculative_patterns):
            return SignalZone.SPECULATIVE

        return SignalZone.GRASSROOTS

    def _extract_origin(self, url: str) -> str:
        """Extract readable origin name from URL."""
        domain = urlparse(url).netloc
        # Remove www. and common TLDs
        origin = domain.replace("www.", "")
        parts = origin.split(".")
        if len(parts) >= 2:
            return parts[-2].title()  # Get the main domain name
        return origin.title()

    async def crawl(self, url: str, config: ContentConfig | None = None) -> CrawlResult:
        """
        Crawl a single URL and extract content.

        Args:
            url: URL to crawl
            config: Optional override configuration

        Returns:
            CrawlResult with extracted content
        """
        cfg = config or self.config

        try:
            from crawl4ai import CacheMode, CrawlerRunConfig
            from crawl4ai.content_filter_strategy import PruningContentFilter
            from crawl4ai.markdown_generation_strategy import DefaultMarkdownGenerator

            crawler = await self._get_crawler()

            # Configure markdown generator with optional pruning
            md_generator = DefaultMarkdownGenerator()
            if cfg.use_pruning_filter:
                md_generator = DefaultMarkdownGenerator(
                    content_filter=PruningContentFilter(
                        threshold=0.48,
                        threshold_type="fixed",
                        min_word_threshold=cfg.word_count_threshold,
                    )
                )

            run_config = CrawlerRunConfig(
                cache_mode=CacheMode.BYPASS,
                page_timeout=cfg.timeout,
                word_count_threshold=cfg.word_count_threshold,
                excluded_tags=cfg.exclude_tags,
                markdown_generator=md_generator,
                wait_for=cfg.wait_for_selector,
            )

            result = await crawler.arun(url=url, config=run_config)

            if not result.success:
                return CrawlResult(
                    url=url,
                    success=False,
                    error=result.error_message,
                )

            # Extract markdown content
            markdown = ""
            fit_markdown = ""

            if hasattr(result, "markdown") and result.markdown:
                if hasattr(result.markdown, "raw_markdown"):
                    markdown = result.markdown.raw_markdown
                    fit_markdown = getattr(result.markdown, "fit_markdown", markdown)
                else:
                    markdown = str(result.markdown)
                    fit_markdown = markdown

            return CrawlResult(
                url=url,
                success=True,
                title=result.metadata.get("title", "") if result.metadata else "",
                markdown=markdown,
                fit_markdown=fit_markdown,
                html=result.html or "",
                links=result.links if hasattr(result, "links") and result.links else [],
                images=result.media.get("images", [])
                if hasattr(result, "media") and result.media
                else [],
                metadata=result.metadata or {},
            )

        except Exception as e:
            return CrawlResult(
                url=url,
                success=False,
                error=str(e),
            )

    async def crawl_many(
        self,
        urls: list[str],
        config: ContentConfig | None = None,
        max_concurrent: int = 5,
    ) -> list[CrawlResult]:
        """
        Crawl multiple URLs with controlled concurrency.

        Args:
            urls: List of URLs to crawl
            config: Optional configuration
            max_concurrent: Maximum concurrent requests

        Returns:
            List of CrawlResults
        """
        semaphore = asyncio.Semaphore(max_concurrent)

        async def crawl_with_limit(url: str) -> CrawlResult:
            async with semaphore:
                return await self.crawl(url, config)

        tasks = [crawl_with_limit(url) for url in urls]
        return await asyncio.gather(*tasks)

    def result_to_source_node(self, result: CrawlResult) -> SourceNode | None:
        """Convert a CrawlResult to a SourceNode domain entity."""
        if not result.success:
            return None

        source_type = self._detect_source_type(result.url)
        signal_zone = self._detect_signal_zone(result.url, source_type)

        return SourceNode(
            id=SourceId(),
            url=result.url,
            title=result.title or result.metadata.get("title", ""),
            source_type=source_type,
            signal_zone=signal_zone,
            origin=self._extract_origin(result.url),
            content_markdown=result.fit_markdown or result.markdown,
            metadata=result.metadata,
            crawled_at=result.crawled_at,
        )
