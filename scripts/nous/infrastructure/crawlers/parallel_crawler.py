"""
High-throughput parallel crawler for Nous.

Key features:
- Domain batching with session reuse
- Zone-aware crawl configuration
- Semaphore-controlled concurrency
- Integrated diagnostics
- Graceful error handling

Uses Crawl4AI's AsyncWebCrawler with:
- BrowserConfig for headless chromium
- CrawlerRunConfig per-request
- session_id for session persistence within domain
"""

import asyncio
import logging
from collections import defaultdict
from dataclasses import dataclass, field
from typing import Any
from urllib.parse import urlparse

from crawl4ai import AsyncWebCrawler, BrowserConfig

from .diagnostics import CrawlDiagnostics, DropReason
from .zone_config import build_crawl_config, get_special_config, get_zone_for_domain

logger = logging.getLogger(__name__)


@dataclass
class CrawlResult:
    """Result from crawling a single URL."""

    url: str
    success: bool
    markdown: str = ""
    html: str = ""
    title: str = ""
    links: list[dict[str, str]] = field(default_factory=list)
    zone: str = ""
    error: str | None = None
    crawl_time_ms: int = 0

    @property
    def word_count(self) -> int:
        """Approximate word count of markdown content."""
        if not self.markdown:
            return 0
        return len(self.markdown.split())

    @property
    def is_empty(self) -> bool:
        """Check if content is essentially empty."""
        return self.word_count < 50


@dataclass
class BatchCrawlResult:
    """Result from crawling a batch of URLs."""

    results: list[CrawlResult] = field(default_factory=list)
    diagnostics: CrawlDiagnostics = field(default_factory=CrawlDiagnostics)
    total_time_ms: int = 0

    @property
    def success_rate(self) -> float:
        """Percentage of successful crawls."""
        if not self.results:
            return 0.0
        return sum(1 for r in self.results if r.success) / len(self.results)

    def get_successful(self) -> list[CrawlResult]:
        """Get only successful crawl results."""
        return [r for r in self.results if r.success and not r.is_empty]


class ParallelCrawler:
    """
    Parallel URL crawler with domain batching and zone awareness.

    Usage:
        crawler = ParallelCrawler(max_concurrent=10)
        results = await crawler.crawl_many(urls)

        for result in results.get_successful():
            print(f"{result.url}: {result.word_count} words")

        print(results.diagnostics.report())
    """

    def __init__(
        self,
        max_concurrent: int = 10,
        headless: bool = True,
        verbose: bool = False,
        timeout_per_url: int = 60000,
    ):
        """
        Initialize the parallel crawler.

        Args:
            max_concurrent: Maximum concurrent crawls
            headless: Run browser in headless mode
            verbose: Enable verbose logging
            timeout_per_url: Timeout per URL in milliseconds
        """
        self.max_concurrent = max_concurrent
        self.headless = headless
        self.verbose = verbose
        self.timeout_per_url = timeout_per_url

        self._browser_config = BrowserConfig(
            headless=headless,
            verbose=verbose,
            browser_type="chromium",
            viewport_width=1920,
            viewport_height=1080,
        )

    async def crawl_many(
        self,
        urls: list[str],
        diagnostics: CrawlDiagnostics | None = None,
    ) -> BatchCrawlResult:
        """
        Crawl multiple URLs in parallel with domain batching.

        URLs are grouped by domain, and each domain batch shares a session.
        This improves performance and reduces bot detection.

        Args:
            urls: List of URLs to crawl
            diagnostics: Optional existing diagnostics to update

        Returns:
            BatchCrawlResult with all results and diagnostics
        """
        import time

        start_time = time.time()

        diag = diagnostics or CrawlDiagnostics()
        diag.discovered = len(urls)

        # Deduplicate URLs
        unique_urls = []
        for url in urls:
            if diag.is_duplicate(url):
                diag.drop(DropReason.DUPLICATE, urls=[url])
            else:
                diag.mark_seen(url)
                unique_urls.append(url)

        if not unique_urls:
            return BatchCrawlResult(diagnostics=diag)

        # Group URLs by domain
        by_domain: dict[str, list[str]] = defaultdict(list)
        for url in unique_urls:
            try:
                domain = urlparse(url).netloc
                by_domain[domain].append(url)
            except (ValueError, AttributeError):
                diag.drop(DropReason.INVALID_URL, urls=[url])

        logger.info(
            f"PARALLEL CRAWL START: {len(unique_urls)} URLs across {len(by_domain)} domains "
            f"(max_concurrent={self.max_concurrent}, timeout={self.timeout_per_url}ms)"
        )

        # Log domain distribution
        for domain, domain_urls in sorted(by_domain.items(), key=lambda x: -len(x[1]))[
            :5
        ]:
            zone = get_zone_for_domain(domain)
            logger.debug(f"  {domain}: {len(domain_urls)} URLs (zone: {zone.name})")
        if len(by_domain) > 5:
            logger.debug(f"  ... and {len(by_domain) - 5} more domains")

        # Crawl each domain batch with semaphore
        semaphore = asyncio.Semaphore(self.max_concurrent)
        all_results: list[CrawlResult] = []

        async def crawl_domain_batch(
            domain: str, domain_urls: list[str]
        ) -> list[CrawlResult]:
            async with semaphore:
                return await self._crawl_domain(domain, domain_urls, diag)

        # Run all domain batches
        tasks = [
            crawl_domain_batch(domain, domain_urls)
            for domain, domain_urls in by_domain.items()
        ]
        batch_results = await asyncio.gather(*tasks, return_exceptions=True)

        # Collect results
        for result in batch_results:
            if isinstance(result, Exception):
                logger.error(f"Domain batch failed: {result}")
                continue
            all_results.extend(result)

        total_time = int((time.time() - start_time) * 1000)

        # Log final summary
        success_count = sum(1 for r in all_results if r.success and not r.is_empty)
        total_words = sum(r.word_count for r in all_results if r.success)
        logger.info(
            f"PARALLEL CRAWL COMPLETE: {success_count}/{len(all_results)} successful "
            f"in {total_time}ms ({total_words:,} words total)"
        )
        logger.info(f"  Yield rate: {diag.yield_rate():.1%}")
        logger.info(f"  Zone distribution: {dict(diag.by_zone)}")
        if diag.dropped:
            logger.info(f"  Drops: {dict(diag.dropped)}")

        return BatchCrawlResult(
            results=all_results,
            diagnostics=diag,
            total_time_ms=total_time,
        )

    async def _crawl_domain(
        self,
        domain: str,
        urls: list[str],
        diag: CrawlDiagnostics,
    ) -> list[CrawlResult]:
        """
        Crawl all URLs for a single domain.

        Uses a shared session for the domain to improve performance.

        Args:
            domain: Domain name
            urls: URLs to crawl for this domain
            diag: Diagnostics tracker

        Returns:
            List of CrawlResults
        """
        import time

        domain_start = time.time()
        results: list[CrawlResult] = []
        zone = get_zone_for_domain(domain)
        session_id = f"nous_{domain.replace('.', '_')}"
        special_config = get_special_config(domain)

        logger.info(f"[{domain}] Starting batch: {len(urls)} URLs (zone: {zone.name})")

        async with AsyncWebCrawler(config=self._browser_config) as crawler:
            for i, url in enumerate(urls):
                result = await self._crawl_single(
                    crawler, url, domain, session_id, zone.name, special_config, diag
                )
                results.append(result)

                # Log per-URL result
                if result.success and not result.is_empty:
                    logger.debug(
                        f"  [{domain}] [{i+1}/{len(urls)}] OK: {result.word_count} words, "
                        f"{result.crawl_time_ms}ms"
                    )
                else:
                    logger.debug(
                        f"  [{domain}] [{i+1}/{len(urls)}] FAIL: {result.error or 'empty'}"
                    )

        # Domain batch summary
        domain_time = int((time.time() - domain_start) * 1000)
        success_count = sum(1 for r in results if r.success and not r.is_empty)
        total_words = sum(r.word_count for r in results if r.success)
        logger.info(
            f"[{domain}] Complete: {success_count}/{len(urls)} success, "
            f"{total_words:,} words in {domain_time}ms"
        )

        return results

    async def _crawl_single(
        self,
        crawler: AsyncWebCrawler,
        url: str,
        domain: str,
        session_id: str,
        zone_name: str,
        special_config: dict[str, Any] | None,
        diag: CrawlDiagnostics,
    ) -> CrawlResult:
        """
        Crawl a single URL.

        Args:
            crawler: AsyncWebCrawler instance
            url: URL to crawl
            domain: Domain name
            session_id: Session ID for session reuse
            zone_name: Signal zone name
            special_config: Optional special configuration overrides
            diag: Diagnostics tracker

        Returns:
            CrawlResult
        """
        import time

        start_time = time.time()

        try:
            # Build zone-aware config
            config = build_crawl_config(domain, session_id=session_id)

            # Apply special config overrides
            if special_config:
                for key, value in special_config.items():
                    if hasattr(config, key):
                        setattr(config, key, value)

            # Execute crawl
            crawl_result = await asyncio.wait_for(
                crawler.arun(url=url, config=config),
                timeout=self.timeout_per_url / 1000,
            )

            crawl_time = int((time.time() - start_time) * 1000)

            if not crawl_result.success:
                error_msg = getattr(crawl_result, "error_message", "Unknown error")
                logger.warning(f"Crawl failed for {url}: {error_msg}")

                # Categorize the failure
                if "timeout" in str(error_msg).lower():
                    diag.drop(DropReason.TIMEOUT, urls=[url])
                elif "403" in str(error_msg) or "blocked" in str(error_msg).lower():
                    diag.drop(DropReason.BLOCKED, urls=[url])
                else:
                    diag.drop(DropReason.PARSE_ERROR, urls=[url])

                return CrawlResult(
                    url=url,
                    success=False,
                    zone=zone_name,
                    error=str(error_msg),
                    crawl_time_ms=crawl_time,
                )

            # Extract content
            markdown = getattr(crawl_result, "markdown", "") or ""
            html = getattr(crawl_result, "html", "") or ""
            title = getattr(crawl_result, "title", "") or ""

            # Extract links
            links = []
            raw_links = getattr(crawl_result, "links", {})
            if isinstance(raw_links, dict):
                for link_type in ["external", "internal"]:
                    for link in raw_links.get(link_type, []):
                        if isinstance(link, dict):
                            links.append(link)
                        elif isinstance(link, str):
                            links.append({"href": link, "text": ""})

            # Check for empty content
            result = CrawlResult(
                url=url,
                success=True,
                markdown=markdown,
                html=html,
                title=title,
                links=links,
                zone=zone_name,
                crawl_time_ms=crawl_time,
            )

            if result.is_empty:
                diag.drop(DropReason.EMPTY, urls=[url])
            else:
                # Calculate a simple relevance score based on content quality
                relevance = min(result.word_count / 500, 1.0)  # Max out at 500 words
                from ...domain import SignalZone

                diag.record_crawl(url, SignalZone[zone_name], relevance)

            return result

        except TimeoutError:
            logger.warning(f"Timeout crawling {url}")
            diag.drop(DropReason.TIMEOUT, urls=[url])
            return CrawlResult(
                url=url,
                success=False,
                zone=zone_name,
                error="Timeout",
                crawl_time_ms=self.timeout_per_url,
            )

        except Exception as e:
            logger.error(f"Error crawling {url}: {e}")
            diag.drop(DropReason.PARSE_ERROR, urls=[url])
            return CrawlResult(
                url=url,
                success=False,
                zone=zone_name,
                error=str(e),
                crawl_time_ms=int((time.time() - start_time) * 1000),
            )

    async def crawl_single(self, url: str) -> CrawlResult:
        """
        Convenience method to crawl a single URL.

        Args:
            url: URL to crawl

        Returns:
            CrawlResult
        """
        result = await self.crawl_many([url])
        if result.results:
            return result.results[0]
        return CrawlResult(url=url, success=False, error="No results")


async def crawl_urls(
    urls: list[str],
    max_concurrent: int = 10,
    headless: bool = True,
) -> BatchCrawlResult:
    """
    Convenience function for parallel crawling.

    Args:
        urls: List of URLs to crawl
        max_concurrent: Maximum concurrent crawls
        headless: Run browser in headless mode

    Returns:
        BatchCrawlResult
    """
    crawler = ParallelCrawler(max_concurrent=max_concurrent, headless=headless)
    return await crawler.crawl_many(urls)
