"""
Recursive link expansion for finding idea origins.

Expands outbound links from crawled pages to trace ideas
back to their original sources. Useful for:
- Finding primary sources (not amplifiers)
- Detecting citation chains
- Measuring amplification/echo chamber effects

Uses Crawl4AI's result.links for external link extraction.
"""

import asyncio
import logging
import re
from dataclasses import dataclass, field
from urllib.parse import urljoin, urlparse

from .diagnostics import CrawlDiagnostics, DropReason
from .parallel_crawler import CrawlResult, ParallelCrawler
from .zone_config import get_zone_for_domain

from ...domain import SignalZone

logger = logging.getLogger(__name__)


@dataclass
class LinkExpansionConfig:
    """Configuration for link expansion."""

    max_depth: int = 2  # Maximum depth to expand
    max_urls_per_page: int = 10  # Max outbound links to follow per page
    max_total_urls: int = 50  # Max total URLs to crawl
    min_relevance: float = 0.4  # Minimum relevance score to continue
    follow_institutional: bool = True  # Prioritize institutional links
    follow_same_domain: bool = False  # Follow same-domain links


@dataclass
class ExpandedLink:
    """A link discovered through expansion."""

    url: str
    depth: int
    parent_url: str
    zone: SignalZone
    relevance: float = 0.0
    anchor_text: str = ""
    is_origin: bool = False  # True if likely an original source


@dataclass
class CitationChain:
    """A chain of citations from origin to amplifiers."""

    origin_url: str
    origin_zone: SignalZone
    amplifiers: list[str] = field(default_factory=list)
    chain_depth: int = 0

    @property
    def amplification_factor(self) -> float:
        """How much this idea has been amplified."""
        return len(self.amplifiers)


@dataclass
class ExpansionResult:
    """Result of link expansion."""

    expanded_urls: list[ExpandedLink] = field(default_factory=list)
    citation_chains: list[CitationChain] = field(default_factory=list)
    potential_origins: list[str] = field(default_factory=list)
    total_crawled: int = 0
    diagnostics: CrawlDiagnostics = field(default_factory=CrawlDiagnostics)


class LinkExpander:
    """
    Recursively expands links to find idea origins.

    Usage:
        expander = LinkExpander(topic="artificial intelligence")
        result = await expander.expand(seed_crawl_results)

        for origin in result.potential_origins:
            print(f"Potential origin: {origin}")
    """

    def __init__(
        self,
        topic: str,
        config: LinkExpansionConfig | None = None,
        max_concurrent: int = 5,
    ):
        """
        Initialize the link expander.

        Args:
            topic: Topic for relevance scoring
            config: Expansion configuration
            max_concurrent: Max concurrent crawls
        """
        self.topic = topic.lower()
        self.config = config or LinkExpansionConfig()
        self.crawler = ParallelCrawler(max_concurrent=max_concurrent)

        # Track expansion state
        self._seen_urls: set[str] = set()
        self._origin_candidates: dict[str, float] = {}  # url -> origin score

    async def expand(
        self,
        seed_results: list[CrawlResult],
    ) -> ExpansionResult:
        """
        Expand links from seed crawl results.

        Args:
            seed_results: Initial crawl results to expand from

        Returns:
            ExpansionResult with expanded links and citation chains
        """
        result = ExpansionResult()

        # Initialize with seed URLs
        for seed in seed_results:
            self._seen_urls.add(seed.url)

        # Collect initial outbound links
        to_expand: list[ExpandedLink] = []
        for seed in seed_results:
            outlinks = self._extract_relevant_outlinks(seed, depth=0)
            to_expand.extend(outlinks)

        logger.info(f"Starting expansion with {len(to_expand)} outbound links")

        # Expand iteratively up to max_depth
        current_depth = 1
        while to_expand and current_depth <= self.config.max_depth:
            # Limit URLs per depth
            urls_to_crawl = [
                link.url
                for link in to_expand
                if link.url not in self._seen_urls
            ][: self.config.max_total_urls - result.total_crawled]

            if not urls_to_crawl:
                break

            logger.info(f"Depth {current_depth}: crawling {len(urls_to_crawl)} URLs")

            # Crawl the URLs
            crawl_result = await self.crawler.crawl_many(urls_to_crawl)
            result.total_crawled += len(crawl_result.results)
            result.diagnostics.merge(crawl_result.diagnostics)

            # Process results and find next level
            next_expand: list[ExpandedLink] = []
            for crawl in crawl_result.get_successful():
                self._seen_urls.add(crawl.url)

                # Check if this could be an origin
                origin_score = self._calculate_origin_score(crawl)
                if origin_score > 0.7:
                    self._origin_candidates[crawl.url] = origin_score
                    result.potential_origins.append(crawl.url)

                # Find link that led here
                parent_link = next(
                    (link for link in to_expand if link.url == crawl.url), None
                )
                if parent_link:
                    parent_link.relevance = self._calculate_relevance(crawl.markdown)
                    parent_link.is_origin = origin_score > 0.7
                    result.expanded_urls.append(parent_link)

                # Get next level links
                if current_depth < self.config.max_depth:
                    outlinks = self._extract_relevant_outlinks(
                        crawl, depth=current_depth
                    )
                    next_expand.extend(outlinks)

            to_expand = next_expand
            current_depth += 1

            # Check total URL limit
            if result.total_crawled >= self.config.max_total_urls:
                logger.info("Reached max total URLs limit")
                break

        # Build citation chains
        result.citation_chains = self._build_citation_chains(
            seed_results, result.expanded_urls
        )

        return result

    def _extract_relevant_outlinks(
        self,
        crawl: CrawlResult,
        depth: int,
    ) -> list[ExpandedLink]:
        """
        Extract relevant outbound links from a crawl result.

        Args:
            crawl: Crawl result to extract links from
            depth: Current depth level

        Returns:
            List of ExpandedLinks to potentially follow
        """
        outlinks: list[ExpandedLink] = []
        source_domain = urlparse(crawl.url).netloc

        for link in crawl.links:
            href = link.get("href", "")
            anchor = link.get("text", "")

            if not href or href.startswith("#") or href.startswith("javascript:"):
                continue

            # Resolve relative URLs
            try:
                full_url = urljoin(crawl.url, href)
                link_domain = urlparse(full_url).netloc
            except Exception:
                continue

            # Skip same domain unless configured
            if link_domain == source_domain and not self.config.follow_same_domain:
                continue

            # Skip already seen
            if full_url in self._seen_urls:
                continue

            # Skip non-http URLs
            if not full_url.startswith(("http://", "https://")):
                continue

            # Get zone
            zone = get_zone_for_domain(link_domain)

            # Calculate priority score
            priority = self._calculate_link_priority(anchor, zone)

            if priority < self.config.min_relevance:
                continue

            outlinks.append(
                ExpandedLink(
                    url=full_url,
                    depth=depth + 1,
                    parent_url=crawl.url,
                    zone=zone,
                    anchor_text=anchor,
                    relevance=priority,
                )
            )

        # Sort by priority and limit
        outlinks.sort(key=lambda x: x.relevance, reverse=True)
        return outlinks[: self.config.max_urls_per_page]

    def _calculate_link_priority(
        self,
        anchor_text: str,
        zone: SignalZone,
    ) -> float:
        """
        Calculate priority score for a link.

        Args:
            anchor_text: Anchor text of the link
            zone: Signal zone of the target domain

        Returns:
            Priority score between 0 and 1
        """
        score = 0.3  # Base score

        # Boost institutional links
        if zone == SignalZone.INSTITUTIONAL:
            score += 0.3

        # Boost if anchor contains topic keywords
        anchor_lower = anchor_text.lower()
        topic_words = self.topic.split()
        matching_words = sum(1 for word in topic_words if word in anchor_lower)
        if matching_words > 0:
            score += min(matching_words * 0.15, 0.3)

        # Boost citation-like anchors
        citation_patterns = [
            r"source",
            r"original",
            r"study",
            r"research",
            r"paper",
            r"report",
            r"according to",
            r"published",
            r"journal",
            r"arxiv",
        ]
        for pattern in citation_patterns:
            if re.search(pattern, anchor_lower):
                score += 0.1
                break

        return min(score, 1.0)

    def _calculate_relevance(self, content: str) -> float:
        """
        Calculate relevance of content to the topic.

        Args:
            content: Page content (markdown)

        Returns:
            Relevance score between 0 and 1
        """
        if not content:
            return 0.0

        content_lower = content.lower()
        topic_words = self.topic.split()

        # Count topic word occurrences
        total_matches = sum(
            content_lower.count(word) for word in topic_words
        )

        # Normalize by content length
        word_count = len(content_lower.split())
        if word_count == 0:
            return 0.0

        # Density-based relevance
        density = total_matches / word_count
        return min(density * 100, 1.0)  # Scale up but cap at 1.0

    def _calculate_origin_score(self, crawl: CrawlResult) -> float:
        """
        Calculate how likely a page is to be an original source.

        Indicators:
        - Institutional zone
        - Contains dates, authors, DOIs
        - High word count
        - Few outbound links (not an aggregator)

        Args:
            crawl: Crawl result to score

        Returns:
            Origin score between 0 and 1
        """
        score = 0.0
        content = crawl.markdown.lower()

        # Zone-based scoring
        if crawl.zone == "INSTITUTIONAL":
            score += 0.3
        elif crawl.zone == "GRASSROOTS":
            score += 0.1

        # Content indicators
        origin_patterns = [
            (r"\b\d{4}\b", 0.05),  # Year
            (r"by\s+[A-Z][a-z]+\s+[A-Z]", 0.1),  # Author byline
            (r"10\.\d{4,}/", 0.2),  # DOI
            (r"abstract", 0.15),  # Academic paper
            (r"methodology|methods", 0.1),  # Research paper
            (r"et al\.", 0.1),  # Academic citation
        ]

        for pattern, boost in origin_patterns:
            if re.search(pattern, content):
                score += boost

        # Word count (originals tend to be longer)
        if crawl.word_count > 1000:
            score += 0.1
        elif crawl.word_count > 500:
            score += 0.05

        # Few outbound links suggests original content
        outlink_count = len(crawl.links)
        if outlink_count < 5:
            score += 0.1
        elif outlink_count > 50:
            score -= 0.1  # Aggregator penalty

        return min(max(score, 0.0), 1.0)

    def _build_citation_chains(
        self,
        seeds: list[CrawlResult],
        expanded: list[ExpandedLink],
    ) -> list[CitationChain]:
        """
        Build citation chains from expanded links.

        Args:
            seeds: Original seed crawl results
            expanded: Expanded links

        Returns:
            List of CitationChains
        """
        chains: list[CitationChain] = []

        # Group by potential origins
        for origin_url, score in self._origin_candidates.items():
            # Find the link that points to this origin
            origin_link = next(
                (link for link in expanded if link.url == origin_url), None
            )

            if origin_link:
                # Trace back the chain
                amplifiers: list[str] = []
                current = origin_link.parent_url

                while current:
                    amplifiers.append(current)
                    # Find parent of current
                    parent_link = next(
                        (link for link in expanded if link.url == current), None
                    )
                    if parent_link:
                        current = parent_link.parent_url
                    else:
                        # Check if it's a seed
                        if any(seed.url == current for seed in seeds):
                            break
                        current = None

                chains.append(
                    CitationChain(
                        origin_url=origin_url,
                        origin_zone=origin_link.zone,
                        amplifiers=amplifiers,
                        chain_depth=origin_link.depth,
                    )
                )

        return chains


async def find_origins(
    topic: str,
    seed_results: list[CrawlResult],
    max_depth: int = 2,
    max_urls: int = 50,
) -> ExpansionResult:
    """
    Convenience function to find original sources.

    Args:
        topic: Topic for relevance scoring
        seed_results: Initial crawl results
        max_depth: Maximum expansion depth
        max_urls: Maximum total URLs to crawl

    Returns:
        ExpansionResult with potential origins
    """
    config = LinkExpansionConfig(max_depth=max_depth, max_total_urls=max_urls)
    expander = LinkExpander(topic=topic, config=config)
    return await expander.expand(seed_results)
