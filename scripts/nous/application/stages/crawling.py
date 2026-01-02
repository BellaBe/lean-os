"""
Crawling stage for content retrieval.

Handles:
- Parallel crawling with Crawl4AI
- Social media snapshots with PageSnapshotter
- Zone-aware configuration
- Content extraction and normalization
"""

from __future__ import annotations

import re
from typing import TYPE_CHECKING
from urllib.parse import urlparse

from ...infrastructure.logging import get_structured_logger
from ...infrastructure.crawlers.parallel_crawler import ParallelCrawler
from ...infrastructure.crawlers.page_snapshot import PageSnapshotter, PageSnapshotConfig
from ...infrastructure.crawlers.diagnostics import CrawlDiagnostics
from ...infrastructure.crawlers.zone_config import get_zone_for_domain
from ...domain import SourceId, SourceNode, SourceType, SignalZone

if TYPE_CHECKING:
    from .base import PipelineContext

_log = get_structured_logger("nous.stages.crawling")


# Social platform domains that benefit from PageSnapshotter
SOCIAL_SNAPSHOT_DOMAINS = {
    "x.com",
    "twitter.com",
    "linkedin.com",
    "youtube.com",
    "facebook.com",
    "instagram.com",
    "tiktok.com",
    "threads.net",
    "mastodon.social",
}


def _is_social_url(url: str) -> bool:
    """Check if URL is from a social platform that needs PageSnapshotter."""
    try:
        domain = urlparse(url).netloc.lower().replace("www.", "")
        return any(social in domain for social in SOCIAL_SNAPSHOT_DOMAINS)
    except Exception:
        return False


def _classify_source_type(url: str, domain: str) -> SourceType:
    """Classify URL into source type."""
    url_lower = url.lower()
    domain_lower = domain.lower()

    if any(d in domain_lower for d in ["arxiv.org", "scholar.google", "researchgate", "pubmed"]):
        return SourceType.ACADEMIC
    if any(d in domain_lower for d in ["reddit.com", "twitter.com", "x.com", "linkedin.com"]):
        return SourceType.SOCIAL
    if any(d in domain_lower for d in ["github.com", "gitlab.com", "stackoverflow.com"]):
        return SourceType.CODE
    if any(d in domain_lower for d in [".gov", "official", "government"]):
        return SourceType.OFFICIAL
    if any(d in domain_lower for d in ["medium.com", "substack.com", "wordpress.com", "blogspot"]):
        return SourceType.BLOG
    if any(d in domain_lower for d in ["ycombinator", "producthunt", "techcrunch", "theverge"]):
        return SourceType.NEWS

    if any(p in url_lower for p in ["/research/", "/paper/", "/publication/", "/abstract/", ".pdf"]):
        return SourceType.ACADEMIC
    if any(p in url_lower for p in ["/blog/", "/posts/", "/article/"]) and "news" not in domain_lower:
        return SourceType.BLOG
    if any(p in url_lower for p in ["/forum/", "/thread/", "/discussion/", "/comments/"]):
        return SourceType.FORUM
    if any(p in url_lower for p in ["/video/", "/watch/", "/embed/", "youtube.com"]):
        return SourceType.VIDEO

    return SourceType.NEWS


class CrawlingStage:
    """
    Pipeline stage for content crawling.

    Routes URLs to appropriate crawlers:
    - Social URLs -> PageSnapshotter
    - Regular URLs -> ParallelCrawler
    """

    @property
    def name(self) -> str:
        return "crawling"

    async def execute(self, context: "PipelineContext") -> "PipelineContext":
        """
        Execute content crawling.

        Populates context.sources, context.urls_crawled, context.urls_failed.
        """
        _log.info("stage_start", stage=self.name, url_count=len(context.discovered_urls))

        urls = context.discovered_urls
        if not urls:
            _log.warning("no_urls_to_crawl")
            return context

        # Build URL list and metadata map
        url_list = [item["url"] for item in urls]
        url_metadata = {item["url"]: item for item in urls}

        # Split URLs into social and non-social
        social_urls = []
        regular_urls = []

        if context.config.use_social_snapshots:
            for url in url_list:
                if _is_social_url(url):
                    social_urls.append(url)
                else:
                    regular_urls.append(url)
            if social_urls:
                _log.info("url_split", social=len(social_urls), regular=len(regular_urls))
        else:
            regular_urls = url_list

        all_sources: list[SourceNode] = []
        total_crawled = 0
        total_failed = 0
        diagnostics = CrawlDiagnostics()

        # Crawl regular URLs
        if regular_urls:
            sources, crawled, failed, diag = await self._crawl_regular(
                context, regular_urls, url_metadata
            )
            all_sources.extend(sources)
            total_crawled += crawled
            total_failed += failed
            if diag:
                diagnostics = diag

        # Crawl social URLs
        if social_urls:
            sources, crawled, failed = await self._crawl_social(
                context, social_urls, url_metadata
            )
            all_sources.extend(sources)
            total_crawled += crawled
            total_failed += failed

        context.sources = all_sources
        context.urls_crawled = total_crawled
        context.urls_failed = total_failed
        context.crawl_diagnostics = diagnostics

        _log.info(
            "stage_complete",
            stage=self.name,
            sources=len(all_sources),
            crawled=total_crawled,
            failed=total_failed,
        )
        return context

    async def _crawl_regular(
        self,
        context: "PipelineContext",
        url_list: list[str],
        url_metadata: dict[str, dict],
    ) -> tuple[list[SourceNode], int, int, CrawlDiagnostics | None]:
        """Crawl regular URLs with ParallelCrawler."""
        _log.info("crawling_regular", count=len(url_list))

        crawler = ParallelCrawler(
            max_concurrent=context.config.max_concurrent_crawls,
            headless=True,
            timeout_per_url=60000,
        )

        result = await crawler.crawl_many(url_list)

        sources = []
        crawled = 0
        failed = 0

        for crawl_result in result.results:
            if crawl_result.success and not crawl_result.is_empty:
                meta = url_metadata.get(crawl_result.url, {})
                domain = urlparse(crawl_result.url).netloc.replace("www.", "")
                zone = get_zone_for_domain(domain)
                source_type = _classify_source_type(crawl_result.url, domain)

                source = SourceNode(
                    id=SourceId.generate(),
                    url=crawl_result.url,
                    title=crawl_result.title or meta.get("title") or domain,
                    domain=domain,
                    source_type=source_type,
                    zone=zone,
                    raw_content=crawl_result.markdown,
                    metadata={
                        "crawl_time_ms": crawl_result.crawl_time_ms,
                        "word_count": crawl_result.word_count,
                        "zone": zone.value,
                    },
                )
                sources.append(source)
                crawled += 1
            else:
                failed += 1

        return sources, crawled, failed, result.diagnostics

    async def _crawl_social(
        self,
        context: "PipelineContext",
        url_list: list[str],
        url_metadata: dict[str, dict],
    ) -> tuple[list[SourceNode], int, int]:
        """Crawl social URLs with PageSnapshotter."""
        _log.info("crawling_social", count=len(url_list))

        sources = []
        crawled = 0
        failed = 0

        snapshot_config = PageSnapshotConfig(
            capture_screenshot=context.config.social_snapshot_screenshot,
            capture_html=True,
            capture_pdf=False,
            capture_mhtml=False,
            delay_before_capture=context.config.social_snapshot_delay,
            wait_for_images=True,
        )

        async with PageSnapshotter() as snapshotter:
            for url in url_list:
                domain = urlparse(url).netloc.replace("www.", "")
                meta = url_metadata.get(url, {})

                try:
                    snapshot = await snapshotter.capture(url, snapshot_config)

                    content = snapshot.html_content or ""
                    text_content = self._extract_text_from_html(content)

                    if len(text_content) < 100:
                        _log.debug("social_too_short", domain=domain, chars=len(text_content))
                        failed += 1
                        continue

                    zone = get_zone_for_domain(domain)

                    source = SourceNode(
                        id=SourceId.generate(),
                        url=url,
                        title=snapshot.page_title or meta.get("title") or domain,
                        domain=domain,
                        source_type=SourceType.SOCIAL,
                        zone=zone,
                        raw_content=text_content,
                        metadata={
                            "captured_at": snapshot.captured_at.isoformat() if snapshot.captured_at else None,
                            "word_count": len(text_content.split()),
                            "zone": zone.value,
                        },
                    )
                    sources.append(source)
                    crawled += 1

                except Exception as e:
                    _log.warning("social_crawl_failed", url=url, error=str(e))
                    failed += 1

        return sources, crawled, failed

    @staticmethod
    def _extract_text_from_html(html: str) -> str:
        """Extract text from HTML, removing scripts and styles."""
        text = re.sub(r"<script[^>]*>.*?</script>", "", html, flags=re.DOTALL | re.IGNORECASE)
        text = re.sub(r"<style[^>]*>.*?</style>", "", text, flags=re.DOTALL | re.IGNORECASE)
        text = re.sub(r"<[^>]+>", " ", text)
        text = re.sub(r"\s+", " ", text).strip()
        return text
