"""
Base classes for pipeline stages.

Defines the Protocol and Context that all stages share.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Protocol
from uuid import UUID

if TYPE_CHECKING:
    from ..config import SnapshotBuilderConfig
    from ..ui import ConsoleUI
    from ...domain import IdeaNode, SourceNode
    from ...infrastructure import DirectLLMClient
    from ...infrastructure.crawlers.diagnostics import CrawlDiagnostics


@dataclass
class PipelineContext:
    """
    Shared context passed through pipeline stages.

    Each stage reads what it needs and writes its outputs here.
    This replaces scattered local variables in the monolithic build() method.
    """

    # Configuration
    config: "SnapshotBuilderConfig"
    llm_client: "DirectLLMClient"
    ui: "ConsoleUI"

    # Identifiers
    topic: str
    snapshot_id: UUID

    # Query variations (Stage 0)
    queries: list[str] = field(default_factory=list)

    # Discovery outputs (Stage 1)
    discovered_urls: list[dict] = field(default_factory=list)
    used_urls: set[str] = field(default_factory=set)
    domains_searched: list[str] = field(default_factory=list)

    # Crawling outputs (Stage 2)
    sources: list["SourceNode"] = field(default_factory=list)
    crawl_diagnostics: "CrawlDiagnostics | None" = None
    urls_crawled: int = 0
    urls_failed: int = 0

    # Extraction outputs (Stage 3)
    ideas: list["IdeaNode"] = field(default_factory=list)

    # Analysis outputs (Stage 4-5)
    consensus_clusters: list = field(default_factory=list)
    contention_zones: list = field(default_factory=list)
    amplification_warnings: list = field(default_factory=list)

    # Synthesis outputs (Stage 6)
    summary: str = ""
    graph_nodes: list = field(default_factory=list)
    graph_edges: list = field(default_factory=list)

    @property
    def urls_discovered(self) -> int:
        """Total URLs discovered."""
        return len(self.discovered_urls)


class PipelineStage(Protocol):
    """
    Protocol for pipeline stages.

    Each stage transforms the context, reading inputs and writing outputs.
    Stages should be idempotent where possible.
    """

    async def execute(self, context: PipelineContext) -> PipelineContext:
        """
        Execute this stage.

        Args:
            context: Pipeline context with inputs

        Returns:
            Updated context with stage outputs
        """
        ...

    @property
    def name(self) -> str:
        """Stage name for logging."""
        ...
