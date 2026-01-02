"""
Link Analysis for Source Network Mapping

Uses Crawl4AI's LinkPreviewConfig to:
1. Extract and score links from crawled pages
2. Build citation/reference networks
3. Detect amplification patterns (same story, multiple outlets)
4. Score links by intrinsic quality AND topic relevance (BM25)

Key insight: Link head extraction lets us score relevance BEFORE crawling,
saving massive time on large source discovery operations.
"""

from dataclasses import dataclass, field
from datetime import datetime
from typing import Any
from urllib.parse import urlparse

from ...domain import SignalZone


@dataclass
class LinkScore:
    """Scoring breakdown for a discovered link.

    Three score types:
    - intrinsic: URL quality, link text, page context (0-10)
    - contextual: BM25 relevance to topic query (0-1)
    - total: Smart combination of both scores
    """

    intrinsic: float = 0.0  # URL quality, link text, context (0-10)
    contextual: float = 0.0  # BM25 relevance to topic (0-1)
    total: float = 0.0  # Combined score


@dataclass
class DiscoveredLink:
    """A link discovered from a source page with metadata."""

    url: str
    text: str
    title: str | None = None

    # Head data (if extracted)
    page_title: str | None = None
    page_description: str | None = None
    meta: dict = field(default_factory=dict)
    jsonld: list = field(default_factory=list)

    # Scores
    score: LinkScore = field(default_factory=LinkScore)

    # Metadata
    is_internal: bool = False
    domain: str = ""
    extraction_status: str = "unknown"  # "valid", "failed", "timeout"


@dataclass
class LinkAnalysisResult:
    """Result of analyzing links from a page."""

    source_url: str
    internal_links: list[DiscoveredLink]
    external_links: list[DiscoveredLink]

    # Aggregates
    total_links: int = 0
    links_with_head_data: int = 0
    avg_relevance_score: float = 0.0

    analyzed_at: datetime = field(default_factory=datetime.utcnow)


class LinkAnalyzer:
    """
    Analyzes links from crawled pages to build source networks.

    Key capabilities:
    - Extract head data from linked pages (title, description, meta)
    - Score links by intrinsic quality and topic relevance
    - Identify high-value citation sources
    - Detect amplification (same content across sources)
    """

    def __init__(self) -> None:
        self._crawler: Any = None

    async def _get_crawler(self) -> Any:
        """Lazy initialization."""
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
        """Close the crawler."""
        if self._crawler:
            await self._crawler.close()
            self._crawler = None

    async def __aenter__(self) -> "LinkAnalyzer":
        await self._get_crawler()
        return self

    async def __aexit__(
        self,
        exc_type: type[BaseException] | None,
        exc_val: BaseException | None,
        exc_tb: Any,
    ) -> None:
        await self.close()

    async def analyze(
        self,
        url: str,
        topic: str,
        max_links: int = 50,
        include_internal: bool = True,
        include_external: bool = True,
        include_patterns: list[str] | None = None,
        exclude_patterns: list[str] | None = None,
        score_threshold: float = 0.0,
    ) -> LinkAnalysisResult:
        """
        Analyze links from a page with head extraction and scoring.

        Args:
            url: Page URL to analyze
            topic: Topic for contextual scoring
            max_links: Maximum links to process
            include_internal: Include same-domain links
            include_external: Include external links
            include_patterns: URL patterns to include (e.g., ["*/article/*"])
            exclude_patterns: URL patterns to exclude (e.g., ["*/login*"])
            score_threshold: Minimum score to include

        Returns:
            LinkAnalysisResult with scored links
        """
        try:
            from crawl4ai import CacheMode, CrawlerRunConfig, LinkPreviewConfig

            crawler = await self._get_crawler()

            link_config = LinkPreviewConfig(
                include_internal=include_internal,
                include_external=include_external,
                max_links=max_links,
                concurrency=10,
                timeout=10,
                query=topic,
                score_threshold=score_threshold,
                include_patterns=include_patterns or [],
                exclude_patterns=exclude_patterns or [],
                verbose=False,
            )

            run_config = CrawlerRunConfig(
                cache_mode=CacheMode.BYPASS,
                link_preview_config=link_config,
                score_links=True,
                only_text=True,
            )

            result = await crawler.arun(url=url, config=run_config)

            if not result.success:
                return LinkAnalysisResult(
                    source_url=url,
                    internal_links=[],
                    external_links=[],
                )

            # Process links
            internal = []
            external = []

            for link in result.links.get("internal", []):
                discovered = self._convert_link(link)
                discovered.is_internal = True
                internal.append(discovered)

            for link in result.links.get("external", []):
                discovered = self._convert_link(link)
                discovered.is_internal = False
                external.append(discovered)

            # Calculate aggregates
            all_links = internal + external
            total = len(all_links)
            with_head = len([link for link in all_links if link.page_title])
            avg_score = (
                sum(link.score.total for link in all_links) / total
                if total > 0
                else 0.0
            )

            return LinkAnalysisResult(
                source_url=url,
                internal_links=internal,
                external_links=external,
                total_links=total,
                links_with_head_data=with_head,
                avg_relevance_score=avg_score,
            )

        except Exception as e:
            print(f"Link analysis failed for {url}: {e}")
            return LinkAnalysisResult(
                source_url=url,
                internal_links=[],
                external_links=[],
            )

    def _convert_link(self, raw_link: dict) -> DiscoveredLink:
        """Convert raw link dict to DiscoveredLink."""
        head_data = raw_link.get("head_data", {}) or {}
        meta = head_data.get("meta", {}) or {}

        # Extract domain
        parsed = urlparse(raw_link.get("href", ""))
        domain = parsed.netloc

        # Build score object
        score = LinkScore(
            intrinsic=raw_link.get("intrinsic_score", 0.0) or 0.0,
            contextual=raw_link.get("contextual_score", 0.0) or 0.0,
            total=raw_link.get("total_score", 0.0) or 0.0,
        )

        return DiscoveredLink(
            url=raw_link.get("href", ""),
            text=raw_link.get("text", ""),
            title=raw_link.get("title"),
            page_title=head_data.get("title"),
            page_description=meta.get("description"),
            meta=meta,
            jsonld=head_data.get("jsonld", []),
            score=score,
            domain=domain,
            extraction_status=raw_link.get("head_extraction_status", "unknown"),
        )

    def find_high_value_citations(
        self,
        analysis: LinkAnalysisResult,
        min_score: float = 0.5,
        prefer_external: bool = True,
    ) -> list[DiscoveredLink]:
        """
        Find high-value citation sources from analysis.

        These are links that:
        - Have high relevance scores
        - Come from authoritative domains
        - Contain substantive content (have page title/description)
        """
        candidates = (
            analysis.external_links
            if prefer_external
            else (analysis.external_links + analysis.internal_links)
        )

        high_value = [
            link
            for link in candidates
            if link.score.total >= min_score
            and link.page_title  # Has head data
            and link.extraction_status == "valid"
        ]

        # Sort by total score
        high_value.sort(key=lambda x: x.score.total, reverse=True)
        return high_value

    def detect_amplification_candidates(
        self,
        analyses: list[LinkAnalysisResult],
        similarity_threshold: float = 0.8,
    ) -> list[tuple[str, list[str]]]:
        """
        Detect potential amplification patterns.

        Looks for:
        - Multiple sources linking to the same URL
        - Similar page titles across different sources (fuzzy matching)

        Args:
            analyses: List of link analysis results
            similarity_threshold: Minimum title similarity to group (0-1)

        Returns:
            List of (url_or_title_group, [source_urls]) tuples
        """
        # Group by linked URL (exact match)
        url_sources: dict[str, list[str]] = {}

        # Also collect titles for similarity matching
        title_to_urls: dict[str, list[tuple[str, str]]] = (
            {}
        )  # title -> [(url, source_url)]

        for analysis in analyses:
            for link in analysis.external_links:
                # Exact URL grouping
                if link.url not in url_sources:
                    url_sources[link.url] = []
                url_sources[link.url].append(analysis.source_url)

                # Collect titles for similarity matching
                if link.page_title:
                    title = link.page_title.strip().lower()
                    if title not in title_to_urls:
                        title_to_urls[title] = []
                    title_to_urls[title].append((link.url, analysis.source_url))

        # Find URLs referenced by multiple sources (exact match)
        amplified = [
            (url, sources) for url, sources in url_sources.items() if len(sources) > 1
        ]

        # Find similar titles across different sources (fuzzy match)
        if title_to_urls and similarity_threshold < 1.0:
            title_groups = self._group_similar_titles(
                title_to_urls, similarity_threshold
            )
            for group_title, url_source_pairs in title_groups.items():
                # Get unique sources that linked to similar-titled pages
                unique_sources = list(set(source for _, source in url_source_pairs))
                if len(unique_sources) > 1:
                    # Use representative title as key
                    amplified.append(
                        (f"[similar titles: {group_title[:50]}...]", unique_sources)
                    )

        # Sort by number of sources (most amplified first)
        amplified.sort(key=lambda x: len(x[1]), reverse=True)
        return amplified

    def _group_similar_titles(
        self,
        title_to_urls: dict[str, list[tuple[str, str]]],
        threshold: float,
    ) -> dict[str, list[tuple[str, str]]]:
        """Group titles by similarity using simple token overlap."""
        titles = list(title_to_urls.keys())
        if len(titles) < 2:
            return title_to_urls

        # Simple similarity based on word overlap (Jaccard-like)
        def title_similarity(t1: str, t2: str) -> float:
            words1 = set(t1.split())
            words2 = set(t2.split())
            if not words1 or not words2:
                return 0.0
            intersection = len(words1 & words2)
            union = len(words1 | words2)
            return intersection / union if union > 0 else 0.0

        # Group similar titles
        used = set()
        groups = {}

        for i, title1 in enumerate(titles):
            if title1 in used:
                continue

            # Start new group
            group_urls = list(title_to_urls[title1])
            used.add(title1)

            # Find similar titles
            for j, title2 in enumerate(titles):
                if i != j and title2 not in used:
                    if title_similarity(title1, title2) >= threshold:
                        group_urls.extend(title_to_urls[title2])
                        used.add(title2)
            # Only keep groups with multiple items from different sources
            if len(group_urls) > len(title_to_urls[title1]):
                groups[title1] = group_urls

        return groups


def classify_link_signal_zone(link: DiscoveredLink) -> SignalZone:
    """Classify a link's signal zone based on domain."""
    domain = link.domain.lower()

    # Institutional sources
    institutional_patterns = [
        ".gov",
        ".edu",
        "reuters.com",
        "bbc.com",
        "nytimes.com",
        "wsj.com",
        "bloomberg.com",
        "ft.com",
        "nature.com",
        "science.org",
    ]
    if any(p in domain for p in institutional_patterns):
        return SignalZone.INSTITUTIONAL

    # Speculative sources
    speculative_patterns = [
        "4chan",
        "crypto",
        "defi",
        "anon",
        "rumor",
    ]
    if any(p in domain for p in speculative_patterns):
        return SignalZone.SPECULATIVE

    # Default to grassroots
    return SignalZone.GRASSROOTS
