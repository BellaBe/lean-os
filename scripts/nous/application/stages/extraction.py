"""
Extraction stage for idea extraction.

Handles:
- Hybrid extraction (CSS/regex then LLM)
- Batch processing for rate limits
- Relevance filtering
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from ...infrastructure.logging import get_structured_logger
from ...infrastructure.extraction.idea_extractor import IdeaExtractor, ExtractionConfig
from ...infrastructure.extraction.hybrid_extractor import HybridExtractor
from ...domain import IdeaNode

if TYPE_CHECKING:
    from .base import PipelineContext
    from ...domain import SourceNode

_log = get_structured_logger("nous.stages.extraction")


class ExtractionStage:
    """
    Pipeline stage for idea extraction.

    Uses hybrid extraction (CSS/regex + LLM) to extract
    claims and arguments from source content.
    """

    @property
    def name(self) -> str:
        return "extraction"

    async def execute(self, context: "PipelineContext") -> "PipelineContext":
        """
        Execute idea extraction.

        Populates context.ideas from context.sources.
        """
        _log.info("stage_start", stage=self.name, source_count=len(context.sources))

        if not context.sources:
            _log.warning("no_sources_to_extract")
            return context

        # Configure extraction
        extraction_config = ExtractionConfig(
            provider=context.config.llm_provider,
            api_token=context.config.llm_api_key,
            temperature=0.1,
            max_tokens=1000,
        )

        extractor = IdeaExtractor(extraction_config)
        hybrid = HybridExtractor()

        all_ideas: list[IdeaNode] = []

        for source in context.sources:
            try:
                ideas = await self._extract_from_source(
                    context, source, extractor, hybrid
                )
                all_ideas.extend(ideas)
            except Exception as e:
                _log.warning(
                    "extraction_failed",
                    source_url=source.url,
                    error=str(e),
                )

        # Filter by relevance if enabled
        if context.config.filter_ideas_by_relevance and all_ideas:
            all_ideas = await self._filter_by_relevance(context, all_ideas)

        context.ideas = all_ideas

        _log.info(
            "stage_complete",
            stage=self.name,
            ideas_extracted=len(all_ideas),
        )
        return context

    async def _extract_from_source(
        self,
        context: "PipelineContext",
        source: "SourceNode",
        extractor: IdeaExtractor,
        hybrid: HybridExtractor,
    ) -> list[IdeaNode]:
        """Extract ideas from a single source."""
        content = source.raw_content or ""
        if not content or len(content) < 100:
            return []

        # Try hybrid extraction first
        try:
            quick = hybrid.extract(content, source.url)

            result = await extractor.extract(
                content=quick.filtered_chunks if quick.filtered_chunks else content,
                source_id=source.id,
                topic=context.topic,
                pre_extracted=quick,
            )

            return result.ideas

        except Exception as e:
            _log.debug("hybrid_extraction_failed", url=source.url, error=str(e))

            # Fallback to direct extraction
            result = await extractor.extract(
                content=content,
                source_id=source.id,
                topic=context.topic,
            )
            return result.ideas

    async def _filter_by_relevance(
        self, context: "PipelineContext", ideas: list[IdeaNode]
    ) -> list[IdeaNode]:
        """Filter ideas by topic relevance using LLM."""
        if len(ideas) <= 10:
            return ideas

        _log.info("filtering_ideas", count=len(ideas))

        # Build batch prompt
        idea_texts = [f"{i+1}. {idea.claim[:200]}" for i, idea in enumerate(ideas[:50])]
        prompt = f"""Given the topic "{context.topic}", rate each claim's relevance (1-10).
Return only the numbers of claims with relevance >= 7, comma-separated.

Claims:
{chr(10).join(idea_texts)}

Relevant claim numbers:"""

        try:
            response = await context.llm_client.complete(prompt)

            # Parse response
            relevant_indices = set()
            for part in response.replace(",", " ").split():
                try:
                    idx = int(part.strip()) - 1
                    if 0 <= idx < len(ideas):
                        relevant_indices.add(idx)
                except ValueError:
                    continue

            if relevant_indices:
                filtered = [ideas[i] for i in sorted(relevant_indices)]
                _log.info("ideas_filtered", original=len(ideas), filtered=len(filtered))
                return filtered

        except Exception as e:
            _log.warning("relevance_filter_failed", error=str(e))

        return ideas
