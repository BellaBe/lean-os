"""
Synthesis stage for summary generation and graph building.

Handles:
- Summary generation via LLM
- Knowledge graph construction
- Final snapshot assembly
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from ...infrastructure.logging import get_structured_logger

if TYPE_CHECKING:
    from .base import PipelineContext

_log = get_structured_logger("nous.stages.synthesis")


class SynthesisStage:
    """
    Pipeline stage for summary and graph synthesis.

    Generates:
    - Topic summary from extracted ideas
    - Knowledge graph linking sources, ideas, and clusters
    """

    @property
    def name(self) -> str:
        return "synthesis"

    async def execute(self, context: PipelineContext) -> PipelineContext:
        """
        Execute synthesis.

        Populates context.summary, context.graph_nodes, context.graph_edges.
        """
        _log.info(
            "stage_start",
            stage=self.name,
            ideas=len(context.ideas),
            sources=len(context.sources),
        )

        # Generate summary
        summary = await self._generate_summary(context)
        context.summary = summary

        # Build graph
        nodes, edges = self._build_graph(context)
        context.graph_nodes = nodes
        context.graph_edges = edges

        _log.info(
            "stage_complete",
            stage=self.name,
            summary_length=len(summary),
            nodes=len(nodes),
            edges=len(edges),
        )
        return context

    async def _generate_summary(self, context: PipelineContext) -> str:
        """Generate topic summary from ideas and consensus."""
        if not context.ideas:
            return "No significant ideas extracted from sources."

        # Build context for LLM
        idea_texts = []
        for i, idea in enumerate(context.ideas[:20]):
            stance_emoji = {"support": "👍", "oppose": "👎", "neutral": "➖"}.get(
                idea.stance.value, "➖"
            )
            idea_texts.append(f"{i+1}. {stance_emoji} {idea.claim[:200]}")

        cluster_texts = []
        for i, cluster in enumerate(context.consensus_clusters[:5]):
            cluster_texts.append(
                f"- Cluster {i+1}: {len(cluster.idea_ids)} similar ideas from {len(cluster.source_ids)} sources"
            )

        contention_texts = []
        for i, contention in enumerate(context.contention_zones[:3]):
            contention_texts.append(f"- Contention {i+1}: {contention.description}")

        prompt = f"""Summarize the following intelligence about "{context.topic}".

Key Ideas Extracted:
{chr(10).join(idea_texts)}

{"Consensus Clusters:" + chr(10) + chr(10).join(cluster_texts) if cluster_texts else ""}

{"Points of Contention:" + chr(10) + chr(10).join(contention_texts) if contention_texts else ""}

Write a concise 2-3 paragraph summary covering:
1. Main themes and consensus views
2. Notable disagreements or controversies
3. Key implications or takeaways

Summary:"""

        try:
            summary = await context.llm_client.complete(prompt)
            return summary.strip()
        except Exception as e:
            _log.error("summary_generation_failed", error=str(e))
            return f"Summary generation failed: {e}"

    def _build_graph(self, context: PipelineContext) -> tuple[list[dict], list[dict]]:
        """Build knowledge graph from sources, ideas, and clusters."""
        nodes = []
        edges = []

        # Add source nodes
        for source in context.sources:
            nodes.append(
                {
                    "id": str(source.id),
                    "type": "source",
                    "label": source.title[:50],
                    "url": source.url,
                    "domain": source.domain,
                    "zone": source.zone.value,
                }
            )

        # Add idea nodes
        for idea in context.ideas:
            nodes.append(
                {
                    "id": str(idea.id),
                    "type": "idea",
                    "label": idea.claim[:100],
                    "stance": idea.stance.value,
                    "confidence": idea.confidence,
                }
            )

            # Edge: source -> idea
            edges.append(
                {
                    "source": str(idea.source_id),
                    "target": str(idea.id),
                    "type": "extracted_from",
                }
            )

        # Add cluster nodes
        for i, cluster in enumerate(context.consensus_clusters):
            cluster_id = f"cluster_{i}"
            nodes.append(
                {
                    "id": cluster_id,
                    "type": "cluster",
                    "label": f"Consensus {i+1}",
                    "idea_count": len(cluster.idea_ids),
                    "source_count": len(cluster.source_ids),
                }
            )

            # Edges: ideas -> cluster
            for idea_id in cluster.idea_ids:
                edges.append(
                    {
                        "source": str(idea_id),
                        "target": cluster_id,
                        "type": "member_of",
                    }
                )

        # Add contention nodes
        for i, contention in enumerate(context.contention_zones):
            contention_id = f"contention_{i}"
            nodes.append(
                {
                    "id": contention_id,
                    "type": "contention",
                    "label": (
                        contention.description[:50]
                        if contention.description
                        else f"Contention {i+1}"
                    ),
                }
            )

        return nodes, edges
