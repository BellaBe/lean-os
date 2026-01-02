"""
Page Snapshot for Temporal Archival

Captures point-in-time snapshots of web pages in multiple formats:
- Screenshot (PNG) - Visual record
- PDF - Printable document
- MHTML - Complete page with all resources (CSS, images, scripts)

Use cases:
- Temporal diff analysis (compare page snapshots over time)
- Evidence preservation
- Offline viewing
- Archival

Note: This is for capturing individual web pages, not to be confused with
the topic Snapshot entity which represents intelligence analysis results.
"""

import base64
import hashlib
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Any


@dataclass
class PageSnapshotConfig:
    """Configuration for page snapshot capture."""

    # What to capture
    capture_screenshot: bool = True
    capture_pdf: bool = False
    capture_mhtml: bool = False
    capture_html: bool = True

    # Screenshot options
    full_page_screenshot: bool = True

    # Wait options (ensure page is fully loaded)
    wait_for_images: bool = True
    delay_before_capture: float = 1.0  # seconds
    wait_for_selector: str | None = None

    # Output
    output_dir: Path | None = None


@dataclass
class PageSnapshot:
    """A captured page snapshot with all requested formats."""

    url: str
    captured_at: datetime

    # Raw content (base64 encoded for binary)
    screenshot_b64: str | None = None
    pdf_bytes: bytes | None = None
    mhtml_content: str | None = None
    html_content: str | None = None

    # Metadata
    page_title: str | None = None
    content_hash: str | None = None  # For diff detection

    # Saved file paths (if output_dir specified)
    screenshot_path: Path | None = None
    pdf_path: Path | None = None
    mhtml_path: Path | None = None
    html_path: Path | None = None

    def save_all(self, output_dir: Path, prefix: str = "") -> dict[str, Path]:
        """
        Save all captured content to files.

        Args:
            output_dir: Directory to save files
            prefix: Optional prefix for filenames

        Returns:
            Dict mapping format to saved path
        """
        output_dir = Path(output_dir)
        output_dir.mkdir(parents=True, exist_ok=True)

        timestamp = self.captured_at.strftime("%Y%m%d_%H%M%S")
        base_name = f"{prefix}_{timestamp}" if prefix else timestamp

        saved = {}

        if self.screenshot_b64:
            path = output_dir / f"{base_name}.png"
            path.write_bytes(base64.b64decode(self.screenshot_b64))
            self.screenshot_path = path
            saved["screenshot"] = path

        if self.pdf_bytes:
            path = output_dir / f"{base_name}.pdf"
            path.write_bytes(self.pdf_bytes)
            self.pdf_path = path
            saved["pdf"] = path

        if self.mhtml_content:
            path = output_dir / f"{base_name}.mhtml"
            path.write_text(self.mhtml_content, encoding="utf-8")
            self.mhtml_path = path
            saved["mhtml"] = path

        if self.html_content:
            path = output_dir / f"{base_name}.html"
            path.write_text(self.html_content, encoding="utf-8")
            self.html_path = path
            saved["html"] = path

        return saved

    def compute_content_hash(self) -> str:
        """Compute hash of HTML content for diff detection."""
        if self.html_content:
            self.content_hash = hashlib.sha256(
                self.html_content.encode("utf-8")
            ).hexdigest()[:16]
        return self.content_hash or ""


@dataclass
class PageComparison:
    """Comparison between two page snapshots."""

    snapshot_a: PageSnapshot
    snapshot_b: PageSnapshot

    content_changed: bool = False
    time_delta_seconds: float = 0.0

    # Detailed changes (if computed)
    added_text: str | None = None
    removed_text: str | None = None


class PageSnapshotter:
    """
    Captures web page snapshots in multiple formats.

    Example:
        snapshotter = PageSnapshotter()
        snapshot = await snapshotter.capture(
            "https://example.com",
            config=PageSnapshotConfig(
                capture_screenshot=True,
                capture_pdf=True,
                capture_mhtml=True,
            ),
        )
        snapshot.save_all(Path("./archives"))
    """

    def __init__(self, browser_profile: Any = None) -> None:
        """
        Args:
            browser_profile: Optional BrowserProfile for anti-bot evasion
        """
        self.browser_profile = browser_profile
        self._crawler: Any = None

    async def _get_crawler(self) -> Any:
        """Get or create crawler instance."""
        if self._crawler is None:
            try:
                from crawl4ai import AsyncWebCrawler, BrowserConfig
            except ImportError:
                raise ImportError("crawl4ai not installed. Run: pip install crawl4ai")

            if self.browser_profile:
                from .browser_config import BrowserFactory

                self._crawler = await BrowserFactory.create_crawler(
                    self.browser_profile
                )
            else:
                config = BrowserConfig(headless=True, verbose=False)
                self._crawler = AsyncWebCrawler(config=config)

            await self._crawler.start()

        return self._crawler

    async def close(self) -> None:
        """Close the crawler."""
        if self._crawler:
            await self._crawler.close()
            self._crawler = None

    async def __aenter__(self) -> "PageSnapshotter":
        await self._get_crawler()
        return self

    async def __aexit__(
        self,
        exc_type: type[BaseException] | None,
        exc_val: BaseException | None,
        exc_tb: Any,
    ) -> None:
        await self.close()

    async def capture(
        self,
        url: str,
        config: PageSnapshotConfig | None = None,
    ) -> PageSnapshot:
        """
        Capture a snapshot of a URL.

        Args:
            url: URL to capture
            config: Snapshot configuration

        Returns:
            PageSnapshot with requested formats
        """
        config = config or PageSnapshotConfig()

        try:
            from crawl4ai import CacheMode, CrawlerRunConfig
        except ImportError:
            raise ImportError("crawl4ai not installed")

        crawler = await self._get_crawler()

        run_config = CrawlerRunConfig(
            cache_mode=CacheMode.BYPASS,
            screenshot=config.capture_screenshot,
            pdf=config.capture_pdf,
            capture_mhtml=config.capture_mhtml,
            wait_for_images=config.wait_for_images,
            delay_before_return_html=config.delay_before_capture,
            wait_for=config.wait_for_selector,
            page_timeout=60000,  # 60s timeout
            ignore_https_errors=True,
        )

        try:
            result = await crawler.arun(url=url, config=run_config)
        except Exception as e:
            error_msg = str(e).lower()
            # Handle navigation/context destruction errors gracefully
            if any(
                msg in error_msg
                for msg in ["navigation", "context was destroyed", "frame was detached"]
            ):
                raise RuntimeError(f"Page navigation error for {url}: {e}")
            raise

        if not result.success:
            raise RuntimeError(f"Failed to capture {url}: {result.error_message}")

        snapshot = PageSnapshot(
            url=url,
            captured_at=datetime.utcnow(),
            screenshot_b64=result.screenshot if config.capture_screenshot else None,
            pdf_bytes=result.pdf if config.capture_pdf else None,
            mhtml_content=result.mhtml if config.capture_mhtml else None,
            html_content=result.html if config.capture_html else None,
            page_title=result.metadata.get("title") if result.metadata else None,
        )

        # Compute content hash for diff detection
        snapshot.compute_content_hash()

        # Save if output_dir specified
        if config.output_dir:
            snapshot.save_all(config.output_dir)

        return snapshot

    async def capture_many(
        self,
        urls: list[str],
        config: PageSnapshotConfig | None = None,
        max_concurrent: int = 3,
    ) -> list[PageSnapshot]:
        """
        Capture snapshots of multiple URLs.

        Args:
            urls: URLs to capture
            config: Snapshot configuration
            max_concurrent: Maximum concurrent captures

        Returns:
            List of PageSnapshot objects
        """
        import asyncio

        semaphore = asyncio.Semaphore(max_concurrent)

        async def capture_with_semaphore(url: str) -> PageSnapshot | None:
            async with semaphore:
                try:
                    return await self.capture(url, config)
                except Exception as e:
                    print(f"Failed to capture {url}: {e}")
                    return None

        tasks = [capture_with_semaphore(url) for url in urls]
        results = await asyncio.gather(*tasks)

        return [r for r in results if r is not None]


class TemporalArchive:
    """
    Manages temporal page snapshots for diff analysis.

    Example:
        archive = TemporalArchive(Path("./archives/topic_x"))

        # Capture initial snapshot
        await archive.capture("https://example.com/article")

        # Later, capture another and compare
        comparison = await archive.capture_and_compare("https://example.com/article")
        if comparison.content_changed:
            print("Content has changed!")
    """

    def __init__(self, archive_dir: Path):
        self.archive_dir = Path(archive_dir)
        self.archive_dir.mkdir(parents=True, exist_ok=True)
        self._snapshotter = None

    async def _get_snapshotter(self) -> PageSnapshotter:
        if self._snapshotter is None:
            self._snapshotter = PageSnapshotter()
            await self._snapshotter._get_crawler()
        return self._snapshotter

    async def close(self):
        if self._snapshotter:
            await self._snapshotter.close()

    def _url_to_prefix(self, url: str) -> str:
        """Convert URL to safe filename prefix."""
        from urllib.parse import urlparse

        parsed = urlparse(url)
        safe_name = f"{parsed.netloc}{parsed.path}".replace("/", "_").replace(".", "_")
        return safe_name[:100]  # Limit length

    def get_snapshots_for_url(self, url: str) -> list[Path]:
        """Get all snapshot files for a URL."""
        prefix = self._url_to_prefix(url)
        return sorted(self.archive_dir.glob(f"{prefix}_*.html"))

    def get_latest_snapshot(self, url: str) -> PageSnapshot | None:
        """Load the most recent snapshot for a URL."""
        files = self.get_snapshots_for_url(url)
        if not files:
            return None

        latest = files[-1]
        html_content = latest.read_text(encoding="utf-8")

        # Parse timestamp from filename
        timestamp_str = latest.stem.split("_")[-2] + "_" + latest.stem.split("_")[-1]
        try:
            captured_at = datetime.strptime(timestamp_str, "%Y%m%d_%H%M%S")
        except ValueError:
            captured_at = datetime.fromtimestamp(latest.stat().st_mtime)

        snapshot = PageSnapshot(
            url=url,
            captured_at=captured_at,
            html_content=html_content,
            html_path=latest,
        )
        snapshot.compute_content_hash()

        return snapshot

    async def capture(
        self,
        url: str,
        config: PageSnapshotConfig | None = None,
    ) -> PageSnapshot:
        """Capture and archive a page snapshot."""
        config = config or PageSnapshotConfig(
            capture_screenshot=True,
            capture_html=True,
            capture_mhtml=True,
        )
        config.output_dir = self.archive_dir

        snapshotter = await self._get_snapshotter()

        # Use URL-based prefix
        prefix = self._url_to_prefix(url)
        snapshot = await snapshotter.capture(url, config)

        # Re-save with proper prefix
        snapshot.save_all(self.archive_dir, prefix)

        return snapshot

    async def capture_and_compare(
        self,
        url: str,
        config: PageSnapshotConfig | None = None,
    ) -> PageComparison:
        """
        Capture a new snapshot and compare with the latest.

        Returns:
            PageComparison with diff information
        """
        # Get previous snapshot
        previous = self.get_latest_snapshot(url)

        # Capture new snapshot
        current = await self.capture(url, config)

        if previous is None:
            # First snapshot, no comparison possible
            return PageComparison(
                snapshot_a=current,
                snapshot_b=current,
                content_changed=False,
                time_delta_seconds=0,
            )

        # Compare
        content_changed = previous.content_hash != current.content_hash
        time_delta = (current.captured_at - previous.captured_at).total_seconds()

        return PageComparison(
            snapshot_a=previous,
            snapshot_b=current,
            content_changed=content_changed,
            time_delta_seconds=time_delta,
        )

    def list_all_urls(self) -> list[str]:
        """List all URLs that have been archived."""
        # This is a simplified approach - in production you'd want a proper index
        html_files = list(self.archive_dir.glob("*.html"))

        # Extract unique prefixes
        prefixes = set()
        for f in html_files:
            parts = f.stem.rsplit("_", 2)
            if len(parts) >= 3:
                prefixes.add(parts[0])

        return list(prefixes)


# Convenience function
async def capture_page_snapshot(
    url: str,
    output_dir: Path | None = None,
    formats: list[str] | None = None,
) -> PageSnapshot:
    """
    Quick helper to capture a page snapshot.

    Args:
        url: URL to capture
        output_dir: Where to save files
        formats: List of formats: "screenshot", "pdf", "mhtml", "html"

    Example:
        snapshot = await capture_page_snapshot(
            "https://example.com",
            output_dir=Path("./snapshots"),
            formats=["screenshot", "mhtml"],
        )
    """
    formats = formats or ["screenshot", "html"]

    config = PageSnapshotConfig(
        capture_screenshot="screenshot" in formats,
        capture_pdf="pdf" in formats,
        capture_mhtml="mhtml" in formats,
        capture_html="html" in formats,
        output_dir=output_dir,
    )

    async with PageSnapshotter() as snapshotter:
        return await snapshotter.capture(url, config)
