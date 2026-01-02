"""
Console UI for Nous CLI output.

Provides clean, human-readable output for CLI while logging
structured data to files for debugging.
"""

from __future__ import annotations

import sys
from typing import TextIO

from ..infrastructure.logging import get_structured_logger


class ConsoleUI:
    """
    Handles CLI output with structured logging.

    Separates user-facing console output from internal logging.
    All output is also logged to file for debugging.
    """

    def __init__(
        self,
        out: TextIO = sys.stdout,
        logger_name: str = "nous.ui",
    ) -> None:
        self._out = out
        self._log = get_structured_logger(logger_name)

    def _write(self, msg: str) -> None:
        """Write to output stream."""
        print(msg, file=self._out)

    # =========================================================================
    # Headers and Separators
    # =========================================================================

    def header(self, title: str, char: str = "=", width: int = 60) -> None:
        """Print a header with separator lines."""
        self._write("")
        self._write(char * width)
        self._write(title)
        self._write(char * width)
        self._log.info("header", title=title)

    def subheader(self, title: str, char: str = "-", width: int = 40) -> None:
        """Print a subheader."""
        self._write(title)
        self._write(char * width)
        self._log.info("subheader", title=title)

    def separator(self) -> None:
        """Print empty line."""
        self._write("")

    # =========================================================================
    # Status Messages
    # =========================================================================

    def info(self, msg: str, indent: int = 0, symbol: str = "→") -> None:
        """Print info message with optional indent."""
        prefix = "  " * indent
        self._write(f"{prefix}{symbol} {msg}")
        self._log.info("ui_message", message=msg, indent=indent)

    def success(self, msg: str, indent: int = 0) -> None:
        """Print success message."""
        self.info(msg, indent, symbol="✓")

    def warning(self, msg: str, indent: int = 0) -> None:
        """Print warning message."""
        self.info(msg, indent, symbol="⚠")
        self._log.warning("ui_warning", message=msg)

    def error(self, msg: str, indent: int = 0) -> None:
        """Print error message."""
        self.info(msg, indent, symbol="✗")
        self._log.error("ui_error", message=msg)

    def bullet(self, msg: str, indent: int = 1) -> None:
        """Print bullet point."""
        self.info(msg, indent, symbol="•")

    # =========================================================================
    # Stage Headers
    # =========================================================================

    def stage(
        self,
        number: int,
        name: str,
        emoji: str,
        iteration: int | None = None,
    ) -> None:
        """Print stage header."""
        iteration_label = f" (iter {iteration})" if iteration and iteration > 1 else ""
        self._write(f"{emoji} STAGE {number}: {name}{iteration_label}")
        self._write("-" * 40)
        self._log.info("stage_start", stage=number, name=name, iteration=iteration)

    # =========================================================================
    # Snapshot-specific Output
    # =========================================================================

    def snapshot_start(
        self,
        topic: str,
        session_id: str,
        sources: list[str],
        max_urls: int,
        llm_provider: str,
        social_enabled: bool = False,
    ) -> None:
        """Print snapshot start banner."""
        self.header(f"🔍 NOUS SNAPSHOT: {topic}")
        self.info(f"Session ID: {session_id[:8]}...")
        self.info(f"Sources: {', '.join(sources)}")
        self.info(f"Max URLs: {max_urls}")
        self.info(f"LLM: {llm_provider}")
        if social_enabled:
            self.info("Social snapshots: ENABLED (Twitter, LinkedIn, YouTube)")
        self.separator()

        self._log.info(
            "snapshot_start",
            topic=topic,
            session_id=session_id,
            sources=sources,
            max_urls=max_urls,
            llm=llm_provider,
        )

    def snapshot_complete(
        self,
        topic: str,
        elapsed: float,
        urls_discovered: int,
        urls_crawled: int,
        urls_failed: int,
        ideas_count: int,
        consensus_count: int,
        contention_count: int,
        source_types: dict[str, int] | None = None,
        signal_zones: dict[str, int] | None = None,
        summary: str | None = None,
    ) -> None:
        """Print snapshot completion summary."""
        self.header("✅ SNAPSHOT COMPLETE")
        self._write(f"  Topic: {topic}")
        self._write(f"  Time: {elapsed:.1f}s")
        self.separator()

        self._write("  📊 Stats:")
        self._write(f"     URLs discovered: {urls_discovered}")
        self._write(f"     URLs crawled: {urls_crawled} ({urls_failed} failed)")
        self._write(f"     Ideas extracted: {ideas_count}")
        self._write(f"     Consensus clusters: {consensus_count}")
        self._write(f"     Contention zones: {contention_count}")
        self.separator()

        if source_types:
            self._write("  📰 Source types:")
            for st, count in sorted(source_types.items(), key=lambda x: -x[1]):
                self._write(f"     {st}: {count}")
            self.separator()

        if signal_zones:
            self._write("  🎯 Signal zones:")
            for zone, count in sorted(signal_zones.items(), key=lambda x: -x[1]):
                self._write(f"     {zone}: {count}")
            self.separator()

        if summary:
            self._write("  📝 Summary:")
            lines = summary.split("\n")
            max_lines = 8
            for i, line in enumerate(lines[:max_lines]):
                if line.strip():
                    self._write(f"     {line.strip()}")
            if len(lines) > max_lines:
                self._write("     ...")
            self.separator()

        self._log.info(
            "snapshot_complete",
            topic=topic,
            elapsed_sec=elapsed,
            urls_discovered=urls_discovered,
            urls_crawled=urls_crawled,
            ideas=ideas_count,
            consensus=consensus_count,
            contention=contention_count,
        )

    # =========================================================================
    # Progress Updates
    # =========================================================================

    def discovery_result(
        self,
        url_count: int,
        domain_count: int,
        source_counts: dict[str, int],
    ) -> None:
        """Print discovery results."""
        self.separator()
        self.success(f"Found {url_count} URLs from {domain_count} domains")
        for src, count in sorted(source_counts.items(), key=lambda x: -x[1]):
            self.bullet(f"{src}: {count} URLs")
        self.separator()

        self._log.info(
            "discovery_complete",
            urls=url_count,
            domains=domain_count,
            by_source=source_counts,
        )

    def crawl_result(
        self,
        success: int,
        failed: int,
        social_count: int = 0,
    ) -> None:
        """Print crawl results."""
        total = success + failed
        yield_rate = (success / total * 100) if total > 0 else 0
        self.separator()
        self.success(f"Crawled: {success} success, {failed} failed ({yield_rate:.0f}% yield)")
        if social_count > 0:
            self.bullet(f"Social snapshots: {social_count} captured with PageSnapshotter")
        self.separator()

        self._log.info(
            "crawl_complete",
            success=success,
            failed=failed,
            yield_pct=yield_rate,
            social=social_count,
        )

    def extraction_result(self, idea_count: int) -> None:
        """Print extraction results."""
        self.separator()
        self.success(f"Total ideas extracted: {idea_count}")
        self.separator()
        self._log.info("extraction_complete", ideas=idea_count)

    def analysis_result(
        self,
        consensus_clusters: list,
        contention_zones: list,
    ) -> None:
        """Print analysis results."""
        self.bullet(f"Consensus clusters: {len(consensus_clusters)}", indent=1)
        for c in consensus_clusters[:3]:
            claim = c.representative_claim[:60]
            self.bullet(f'"{claim}..."', indent=2)

        self.bullet(f"Contention zones: {len(contention_zones)}", indent=1)
        for c in contention_zones[:3]:
            claim = c.representative_claim[:60]
            self.bullet(f'"{claim}..."', indent=2)
        self.separator()

        self._log.info(
            "analysis_complete",
            consensus=len(consensus_clusters),
            contention=len(contention_zones),
        )
