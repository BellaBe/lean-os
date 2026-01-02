"""
Dependency injection container for Nous.

Provides a clean way to inject and manage dependencies
across the snapshot building pipeline.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from ..infrastructure import DirectLLMClient
    from ..infrastructure.analysis.consensus_detector import ConsensusDetector
    from ..infrastructure.crawlers.parallel_crawler import ParallelCrawler
    from ..infrastructure.extraction.idea_extractor import IdeaExtractor
    from .config import SnapshotBuilderConfig
    from .stages import (
        AnalysisStage,
        CrawlingStage,
        DiscoveryStage,
        ExtractionStage,
        PipelineStage,
        SynthesisStage,
    )
    from .ui import ConsoleUI


@dataclass
class SnapshotDependencies:
    """
    Container for all snapshot building dependencies.

    Allows injection of specific implementations for testing
    or customization. All fields are optional and will use
    default implementations if not provided.
    """

    # Core services
    llm_client: DirectLLMClient | None = None
    crawler: ParallelCrawler | None = None
    extractor: IdeaExtractor | None = None
    analyzer: ConsensusDetector | None = None

    # UI
    ui: ConsoleUI | None = None

    # Pipeline stages (override default stage implementations)
    discovery_stage: DiscoveryStage | None = None
    crawling_stage: CrawlingStage | None = None
    extraction_stage: ExtractionStage | None = None
    analysis_stage: AnalysisStage | None = None
    synthesis_stage: SynthesisStage | None = None

    def get_stages(self) -> list[PipelineStage]:
        """
        Get the ordered list of pipeline stages.

        Uses injected stages or creates defaults.
        """
        from .stages import (
            AnalysisStage,
            CrawlingStage,
            DiscoveryStage,
            ExtractionStage,
            SynthesisStage,
        )

        return [
            self.discovery_stage or DiscoveryStage(),
            self.crawling_stage or CrawlingStage(),
            self.extraction_stage or ExtractionStage(),
            self.analysis_stage or AnalysisStage(),
            self.synthesis_stage or SynthesisStage(),
        ]


def create_default_dependencies(
    config: SnapshotBuilderConfig,
) -> SnapshotDependencies:
    """
    Create dependencies with default implementations.

    Args:
        config: Snapshot builder configuration

    Returns:
        SnapshotDependencies with all defaults initialized
    """
    from ..infrastructure import DirectLLMClient, LLMConfig
    from ..infrastructure.analysis.consensus_detector import ConsensusDetector
    from ..infrastructure.crawlers.parallel_crawler import ParallelCrawler
    from ..infrastructure.extraction.idea_extractor import (
        ExtractionConfig,
        IdeaExtractor,
    )
    from .ui import ConsoleUI

    # Create LLM client
    llm_config = LLMConfig(
        provider=config.llm_provider,
        api_token=config.llm_api_key,
    )
    llm_client = DirectLLMClient(llm_config)

    # Create crawler
    crawler = ParallelCrawler(
        max_concurrent=config.max_concurrent_crawls,
        headless=True,
        timeout_per_url=config.crawl_timeout * 1000,
    )

    # Create extractor
    extraction_config = ExtractionConfig(
        provider=config.llm_provider,
        api_token=config.llm_api_key,
    )
    extractor = IdeaExtractor(extraction_config)

    # Create analyzer
    analyzer = ConsensusDetector()

    # Create UI
    ui = ConsoleUI()

    return SnapshotDependencies(
        llm_client=llm_client,
        crawler=crawler,
        extractor=extractor,
        analyzer=analyzer,
        ui=ui,
    )
