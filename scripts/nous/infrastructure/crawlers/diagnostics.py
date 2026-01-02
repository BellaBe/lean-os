"""
Crawl diagnostics for tracking URL attrition through the pipeline.

Provides visibility into:
- How many URLs were discovered vs crawled
- Why URLs were dropped (rate limit, timeout, blocked, etc.)
- Distribution across signal zones
- Overall yield rate and relevance metrics
"""

from dataclasses import dataclass, field
from enum import Enum, auto

from ...domain import SignalZone


class DropReason(Enum):
    """Reasons a URL may be dropped from the pipeline."""

    RELEVANCE = auto()  # Below relevance threshold
    TIMEOUT = auto()  # Page load timeout
    BLOCKED = auto()  # Anti-bot/403/captcha
    EMPTY = auto()  # No meaningful content extracted
    DUPLICATE = auto()  # Already processed
    RATE_LIMITED = auto()  # Hit rate limit
    PARSE_ERROR = auto()  # Failed to parse content
    INVALID_URL = auto()  # Malformed or inaccessible URL


@dataclass
class CrawlDiagnostics:
    """
    Track URL attrition through the crawling pipeline.

    Usage:
        diag = CrawlDiagnostics()
        diag.discovered = 100  # Set total discovered

        # Record drops as they happen
        diag.drop(DropReason.RELEVANCE, count=10)
        diag.drop(DropReason.TIMEOUT, count=5, urls=["http://slow.com"])

        # Record successful crawls
        diag.record_crawl("http://example.com", SignalZone.INSTITUTIONAL, 0.8)

        # Get final report
        print(diag.report())
    """

    # Input counts
    discovered: int = 0

    # Drop tracking
    dropped: dict[DropReason, int] = field(default_factory=dict)
    dropped_urls: dict[DropReason, list[str]] = field(default_factory=dict)

    # Success tracking
    crawled: int = 0
    by_zone: dict[SignalZone, int] = field(default_factory=dict)
    total_relevance: float = 0.0

    # URL tracking (for deduplication)
    seen_urls: set[str] = field(default_factory=set)
    # Separate tracking for URLs actually crawled (to prevent double-counting)
    crawled_urls: set[str] = field(default_factory=set)

    def drop(
        self,
        reason: DropReason,
        count: int = 1,
        urls: list[str] | None = None,
    ) -> None:
        """
        Record dropped URLs.

        Args:
            reason: Why the URL(s) were dropped
            count: Number of URLs dropped (default 1)
            urls: Optional list of specific URLs for debugging
        """
        self.dropped[reason] = self.dropped.get(reason, 0) + count

        if urls:
            if reason not in self.dropped_urls:
                self.dropped_urls[reason] = []
            self.dropped_urls[reason].extend(urls)

    def record_crawl(
        self,
        url: str,
        zone: SignalZone,
        relevance: float = 0.0,
    ) -> bool:
        """
        Record a successful crawl.

        Args:
            url: The crawled URL
            zone: Signal zone of the source
            relevance: Relevance score (0-1)

        Returns:
            True if recorded, False if already recorded as crawled
        """
        # Check crawled_urls, not seen_urls - URLs may be pre-marked as seen
        # for deduplication before crawling, but we still want to record them
        if url in self.crawled_urls:
            return False

        self.crawled_urls.add(url)
        self.seen_urls.add(url)  # Also mark as seen
        self.crawled += 1
        self.by_zone[zone] = self.by_zone.get(zone, 0) + 1
        self.total_relevance += relevance
        return True

    def is_duplicate(self, url: str) -> bool:
        """Check if URL has already been processed."""
        return url in self.seen_urls

    def mark_seen(self, url: str) -> None:
        """Mark a URL as seen without recording as crawl."""
        self.seen_urls.add(url)

    @property
    def total_dropped(self) -> int:
        """Total number of dropped URLs."""
        return sum(self.dropped.values())

    @property
    def avg_relevance(self) -> float:
        """Average relevance of crawled content."""
        if self.crawled == 0:
            return 0.0
        return self.total_relevance / self.crawled

    def yield_rate(self) -> float:
        """
        Calculate the yield rate (crawled / discovered).

        Returns:
            Float between 0-1, or 0 if no URLs discovered
        """
        if self.discovered == 0:
            return 0.0
        return self.crawled / self.discovered

    def drop_rate(self) -> float:
        """
        Calculate the drop rate (dropped / discovered).

        Returns:
            Float between 0-1, or 0 if no URLs discovered
        """
        if self.discovered == 0:
            return 0.0
        return self.total_dropped / self.discovered

    def zone_distribution(self) -> dict[str, float]:
        """
        Get percentage distribution across zones.

        Returns:
            Dict mapping zone name to percentage (0-100)
        """
        if self.crawled == 0:
            return {}

        return {
            zone.name: (count / self.crawled) * 100
            for zone, count in self.by_zone.items()
        }

    def report(self) -> str:
        """
        Generate a human-readable diagnostic report.

        Returns:
            Formatted multi-line string with all metrics
        """
        lines = [
            "=" * 50,
            "CRAWL DIAGNOSTICS REPORT",
            "=" * 50,
            "",
            f"Discovered: {self.discovered}",
            f"Crawled:    {self.crawled}",
            f"Dropped:    {self.total_dropped}",
            f"Yield Rate: {self.yield_rate():.1%}",
            f"Avg Relevance: {self.avg_relevance:.2f}",
            "",
        ]

        # Drop breakdown
        if self.dropped:
            lines.append("Drop Breakdown:")
            for reason, count in sorted(
                self.dropped.items(), key=lambda x: x[1], reverse=True
            ):
                pct = (count / self.discovered * 100) if self.discovered else 0
                lines.append(f"  {reason.name}: {count} ({pct:.1f}%)")
            lines.append("")

        # Zone distribution
        if self.by_zone:
            lines.append("Zone Distribution:")
            for zone, count in sorted(
                self.by_zone.items(), key=lambda x: x[1], reverse=True
            ):
                pct = (count / self.crawled * 100) if self.crawled else 0
                lines.append(f"  {zone.name}: {count} ({pct:.1f}%)")
            lines.append("")

        lines.append("=" * 50)
        return "\n".join(lines)

    def to_dict(self) -> dict:
        """
        Export diagnostics as a dictionary for logging/serialization.

        Returns:
            Dict with all metrics
        """
        return {
            "discovered": self.discovered,
            "crawled": self.crawled,
            "total_dropped": self.total_dropped,
            "yield_rate": self.yield_rate(),
            "avg_relevance": self.avg_relevance,
            "dropped_by_reason": {
                reason.name: count for reason, count in self.dropped.items()
            },
            "by_zone": {zone.name: count for zone, count in self.by_zone.items()},
        }

    def merge(self, other: "CrawlDiagnostics") -> None:
        """
        Merge another diagnostics instance into this one.

        Useful for aggregating results from parallel crawlers.

        Args:
            other: Another CrawlDiagnostics instance
        """
        self.discovered += other.discovered
        self.crawled += other.crawled
        self.total_relevance += other.total_relevance

        # Merge drops
        for reason, count in other.dropped.items():
            self.dropped[reason] = self.dropped.get(reason, 0) + count

        # Merge dropped URLs
        for reason, urls in other.dropped_urls.items():
            if reason not in self.dropped_urls:
                self.dropped_urls[reason] = []
            self.dropped_urls[reason].extend(urls)

        # Merge zones
        for zone, count in other.by_zone.items():
            self.by_zone[zone] = self.by_zone.get(zone, 0) + count

        # Merge seen URLs
        self.seen_urls.update(other.seen_urls)

        # Merge crawled URLs
        self.crawled_urls.update(other.crawled_urls)
