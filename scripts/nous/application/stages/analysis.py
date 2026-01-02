"""
Analysis stage for consensus and contention detection.

Handles:
- Consensus clustering (similar ideas from diverse sources)
- Contention detection (opposing stances)
- Amplification warnings
"""

from __future__ import annotations

from collections import Counter
from typing import TYPE_CHECKING

from ...infrastructure.logging import get_structured_logger
from ...infrastructure.analysis.consensus_detector import ConsensusDetector
from ...domain import (
    AmplificationWarning,
    ConsensusCluster,
    ContentionZone,
    IdeaNode,
    Stance,
)

if TYPE_CHECKING:
    from .base import PipelineContext

_log = get_structured_logger("nous.stages.analysis")


class AnalysisStage:
    """
    Pipeline stage for consensus and amplification analysis.

    Detects:
    - Consensus clusters (similar ideas from diverse sources)
    - Contention zones (ideas with opposing stances)
    - Amplification warnings (single-source dominance)
    """

    @property
    def name(self) -> str:
        return "analysis"

    async def execute(self, context: "PipelineContext") -> "PipelineContext":
        """
        Execute analysis.

        Populates context.consensus_clusters, context.contention_zones,
        and context.amplification_warnings.
        """
        _log.info("stage_start", stage=self.name, idea_count=len(context.ideas))

        if not context.ideas:
            _log.warning("no_ideas_to_analyze")
            return context

        # Consensus detection
        detector = ConsensusDetector()
        clusters, contentions = await detector.detect(context.ideas)

        context.consensus_clusters = clusters
        context.contention_zones = contentions

        _log.info(
            "consensus_detected",
            clusters=len(clusters),
            contentions=len(contentions),
        )

        # Amplification detection
        warnings = self._detect_amplification(context)
        context.amplification_warnings = warnings

        _log.info(
            "stage_complete",
            stage=self.name,
            clusters=len(clusters),
            contentions=len(contentions),
            warnings=len(warnings),
        )
        return context

    def _detect_amplification(self, context: "PipelineContext") -> list[AmplificationWarning]:
        """
        Detect amplification patterns.

        Flags cases where a single source dominates idea coverage.
        """
        warnings: list[AmplificationWarning] = []

        # Count ideas per source
        source_idea_counts: Counter[str] = Counter()
        source_urls: dict[str, str] = {}

        for idea in context.ideas:
            source_id = str(idea.source_id)
            source_idea_counts[source_id] += 1

            # Map source_id to URL
            for source in context.sources:
                if str(source.id) == source_id:
                    source_urls[source_id] = source.url
                    break

        total_ideas = len(context.ideas)
        if total_ideas < 5:
            return warnings

        # Check for dominance (>40% from single source)
        for source_id, count in source_idea_counts.most_common(3):
            ratio = count / total_ideas
            if ratio > 0.4:
                url = source_urls.get(source_id, "unknown")
                warnings.append(
                    AmplificationWarning(
                        source_id=source_id,
                        source_url=url,
                        idea_count=count,
                        total_ideas=total_ideas,
                        ratio=ratio,
                        message=f"Source dominance: {ratio:.0%} of ideas from {url}",
                    )
                )

        # Check for zone imbalance
        zone_counts: Counter[str] = Counter()
        for source in context.sources:
            zone_counts[source.zone.value] += 1

        if zone_counts:
            dominant_zone, dominant_count = zone_counts.most_common(1)[0]
            total_sources = sum(zone_counts.values())
            if total_sources >= 5 and dominant_count / total_sources > 0.7:
                warnings.append(
                    AmplificationWarning(
                        source_id="zone",
                        source_url="",
                        idea_count=dominant_count,
                        total_ideas=total_sources,
                        ratio=dominant_count / total_sources,
                        message=f"Zone imbalance: {dominant_count}/{total_sources} sources from {dominant_zone}",
                    )
                )

        return warnings
