"""
Idea Extraction with LLM and Chunking Support

Uses Crawl4AI's LLMExtractionStrategy with automatic chunking
for processing long articles that exceed token limits.

Key features:
- Automatic chunking with overlap for context preservation
- Schema-based extraction for structured output
- Multi-provider support via LiteLLM
"""

import json
import os
from dataclasses import dataclass, field
from datetime import UTC, datetime

from pydantic import BaseModel, Field

from ...domain import IdeaId, IdeaNode, SourceId, Stance


# Pydantic schemas for LLM extraction
class ExtractedClaim(BaseModel):
    """A claim/argument extracted from content."""

    claim: str = Field(description="The main claim or argument being made")
    stance: str = Field(description="One of: support, oppose, neutral")
    confidence: float = Field(description="Confidence in this extraction (0-1)")
    evidence: str | None = Field(default=None, description="Supporting evidence if mentioned")
    context: str | None = Field(default=None, description="Surrounding context")


class ExtractedIdeas(BaseModel):
    """Collection of ideas extracted from a single source."""

    ideas: list[ExtractedClaim] = Field(description="List of extracted claims/arguments")
    summary: str | None = Field(default=None, description="Brief summary of main points")
    sentiment: str | None = Field(
        default=None, description="Overall sentiment: positive, negative, mixed, neutral"
    )


@dataclass
class ExtractionConfig:
    """Configuration for idea extraction."""

    # LLM settings
    provider: str = "ollama/llama3.3"  # Default to local
    api_token: str | None = None
    temperature: float = 0.1  # Low for consistent extraction
    max_tokens: int = 2000

    # Chunking settings
    apply_chunking: bool = True
    chunk_token_threshold: int = 2000  # Max tokens per chunk
    overlap_rate: float = 0.1  # 10% overlap between chunks

    # Input settings
    input_format: str = "markdown"  # or "html", "fit_markdown"

    # Extraction settings
    min_claim_length: int = 20
    max_claims_per_source: int = 20


@dataclass
class ExtractionResult:
    """Result of idea extraction from a source."""

    source_id: SourceId
    ideas: list[IdeaNode]
    summary: str | None = None
    sentiment: str | None = None

    # Metadata
    chunks_processed: int = 0
    tokens_used: int = 0
    extraction_time_ms: int = 0

    extracted_at: datetime = field(default_factory=lambda: datetime.now(UTC))


class IdeaExtractor:
    """
    Extracts ideas/claims from content using LLM.

    Supports:
    - Automatic chunking for long documents
    - Schema-based extraction for structured output
    - Multiple LLM providers via LiteLLM
    """

    # Extraction prompt template
    EXTRACTION_PROMPT = """Analyze the following content and extract the main claims, arguments, and positions.

For each distinct claim or argument you find:
1. State the claim clearly and concisely
2. Determine the stance (support, oppose, or neutral)
3. Rate your confidence in the extraction (0.0 to 1.0)
4. Note any supporting evidence mentioned
5. Provide brief context if helpful

Focus on:
- Factual claims and assertions
- Opinions and positions
- Arguments for or against something
- Predictions or forecasts

Ignore:
- Generic statements without substance
- Navigation or UI text
- Promotional fluff without specific claims

Topic context: {topic}

Return a JSON object matching the schema provided."""

    def __init__(self, config: ExtractionConfig | None = None):
        self.config = config or ExtractionConfig()
        self._strategy = None

    def _get_strategy(self, topic: str):
        """Get or create LLMExtractionStrategy."""
        try:
            from crawl4ai import LLMConfig, LLMExtractionStrategy

            llm_config = LLMConfig(
                provider=self.config.provider,
                api_token=self.config.api_token or os.getenv("OPENAI_API_KEY"),
            )

            return LLMExtractionStrategy(
                llm_config=llm_config,
                schema=ExtractedIdeas.model_json_schema(),
                extraction_type="schema",
                instruction=self.EXTRACTION_PROMPT.format(topic=topic),
                chunk_token_threshold=self.config.chunk_token_threshold,
                overlap_rate=self.config.overlap_rate,
                apply_chunking=self.config.apply_chunking,
                input_format=self.config.input_format,
                extra_args={
                    "temperature": self.config.temperature,
                    "max_tokens": self.config.max_tokens,
                },
                verbose=False,
            )
        except ImportError:
            return None

    async def extract(
        self,
        content: str,
        source_id: SourceId,
        topic: str,
    ) -> ExtractionResult:
        """
        Extract ideas from content.

        Args:
            content: Text content to analyze
            source_id: ID of the source
            topic: Topic context for extraction

        Returns:
            ExtractionResult with extracted IdeaNodes
        """
        import time

        start_time = time.time()

        strategy = self._get_strategy(topic)

        if strategy:
            # Use Crawl4AI strategy
            result = await self._extract_with_crawl4ai(content, strategy)
        else:
            # Fallback to direct LiteLLM
            result = await self._extract_with_litellm(content, topic)

        # Convert to IdeaNodes
        ideas = self._convert_to_idea_nodes(result, source_id)

        elapsed_ms = int((time.time() - start_time) * 1000)

        return ExtractionResult(
            source_id=source_id,
            ideas=ideas,
            summary=result.get("summary"),
            sentiment=result.get("sentiment"),
            chunks_processed=result.get("chunks", 1),
            tokens_used=result.get("tokens", 0),
            extraction_time_ms=elapsed_ms,
        )

    async def _extract_with_crawl4ai(
        self,
        content: str,
        strategy,
    ) -> dict:
        """Extract using Crawl4AI LLMExtractionStrategy."""
        try:
            from crawl4ai import AsyncWebCrawler, CrawlerRunConfig

            config = CrawlerRunConfig(
                extraction_strategy=strategy,
            )

            # Use raw:// prefix to pass content directly
            raw_url = f"raw:{content}"

            async with AsyncWebCrawler() as crawler:
                result = await crawler.arun(url=raw_url, config=config)

                if result.success and result.extracted_content:
                    data = json.loads(result.extracted_content)

                    # Get usage stats
                    strategy.show_usage()

                    # Handle both list and dict responses from LLM
                    if isinstance(data, list):
                        # LLM returned array directly
                        ideas = data
                        summary = None
                        sentiment = None
                    elif isinstance(data, dict):
                        ideas = data.get("ideas", [])
                        summary = data.get("summary")
                        sentiment = data.get("sentiment")
                    else:
                        ideas = []
                        summary = None
                        sentiment = None

                    return {
                        "ideas": ideas,
                        "summary": summary,
                        "sentiment": sentiment,
                        "tokens": getattr(strategy, "total_usage", 0),
                    }
        except Exception as e:
            print(f"Crawl4AI extraction failed: {e}")

        return {"ideas": []}

    async def _extract_with_litellm(
        self,
        content: str,
        topic: str,
    ) -> dict:
        """Fallback extraction using LiteLLM directly."""
        try:
            import litellm

            # Manual chunking if needed
            chunks = self._chunk_content(content)
            all_ideas = []
            total_tokens = 0

            for chunk in chunks:
                response = await litellm.acompletion(
                    model=self.config.provider,
                    messages=[
                        {
                            "role": "system",
                            "content": self.EXTRACTION_PROMPT.format(topic=topic),
                        },
                        {
                            "role": "user",
                            "content": f"Content to analyze:\n\n{chunk}",
                        },
                    ],
                    temperature=self.config.temperature,
                    max_tokens=self.config.max_tokens,
                    response_format={"type": "json_object"},
                )

                # Parse response
                content = response.choices[0].message.content
                data = json.loads(content)

                if "ideas" in data:
                    all_ideas.extend(data["ideas"])

                # Track tokens
                if hasattr(response, "usage"):
                    total_tokens += response.usage.total_tokens

            return {
                "ideas": all_ideas,
                "chunks": len(chunks),
                "tokens": total_tokens,
            }

        except Exception as e:
            print(f"LiteLLM extraction failed: {e}")
            return {"ideas": []}

    def _chunk_content(self, content: str) -> list[str]:
        """Split content into chunks with overlap."""
        if not self.config.apply_chunking:
            return [content]

        # Rough token estimate (words * 0.75)
        words = content.split()
        word_threshold = int(self.config.chunk_token_threshold / 0.75)
        overlap_words = int(word_threshold * self.config.overlap_rate)

        if len(words) <= word_threshold:
            return [content]

        chunks = []
        start = 0

        while start < len(words):
            end = start + word_threshold
            chunk_words = words[start:end]
            chunks.append(" ".join(chunk_words))
            start = end - overlap_words

        return chunks

    def _convert_to_idea_nodes(
        self,
        result: dict,
        source_id: SourceId,
    ) -> list[IdeaNode]:
        """Convert extraction result to IdeaNode objects."""
        ideas = []

        for item in result.get("ideas", []):
            # Parse stance
            stance_str = item.get("stance", "neutral").lower()
            if stance_str == "support":
                stance_dist = {Stance.SUPPORT: 0.8, Stance.NEUTRAL: 0.2}
            elif stance_str == "oppose":
                stance_dist = {Stance.OPPOSE: 0.8, Stance.NEUTRAL: 0.2}
            else:
                stance_dist = {Stance.NEUTRAL: 1.0}

            # Skip short claims
            claim = item.get("claim", "")
            if len(claim) < self.config.min_claim_length:
                continue

            idea = IdeaNode(
                id=IdeaId(),
                claim=claim,
                stance_distribution=stance_dist,
                source_ids=[source_id],
                behavioral_triggers=[],  # Could extract from evidence
            )

            ideas.append(idea)

            # Limit per source
            if len(ideas) >= self.config.max_claims_per_source:
                break

        return ideas


class ChunkingStrategy:
    """
    Configurable chunking strategies for content processing.

    Supports:
    - Fixed-length word chunking
    - Sliding window with overlap
    - Sentence-based chunking
    - Topic-based segmentation (requires NLTK)
    """

    @staticmethod
    def fixed_length(content: str, chunk_size: int = 500) -> list[str]:
        """Split into fixed-length word chunks."""
        words = content.split()
        return [" ".join(words[i : i + chunk_size]) for i in range(0, len(words), chunk_size)]

    @staticmethod
    def sliding_window(
        content: str,
        window_size: int = 500,
        step: int = 400,
    ) -> list[str]:
        """Split with sliding window and overlap."""
        words = content.split()
        chunks = []

        for i in range(0, len(words) - window_size + 1, step):
            chunks.append(" ".join(words[i : i + window_size]))

        # Don't forget the tail
        if len(words) > window_size and len(words) % step != 0:
            chunks.append(" ".join(words[-window_size:]))

        return chunks

    @staticmethod
    def sentence_based(content: str, sentences_per_chunk: int = 10) -> list[str]:
        """Split by sentences using simple regex."""
        import re

        # Simple sentence splitting
        sentences = re.split(r"(?<=[.!?])\s+", content)
        sentences = [s.strip() for s in sentences if s.strip()]

        chunks = []
        for i in range(0, len(sentences), sentences_per_chunk):
            chunk = " ".join(sentences[i : i + sentences_per_chunk])
            if chunk:
                chunks.append(chunk)

        return chunks

    @staticmethod
    def by_paragraphs(content: str, paragraphs_per_chunk: int = 3) -> list[str]:
        """Split by paragraphs (double newlines)."""
        paragraphs = [p.strip() for p in content.split("\n\n") if p.strip()]

        chunks = []
        for i in range(0, len(paragraphs), paragraphs_per_chunk):
            chunk = "\n\n".join(paragraphs[i : i + paragraphs_per_chunk])
            if chunk:
                chunks.append(chunk)

        return chunks


# Convenience function
async def extract_ideas(
    content: str,
    source_id: str,
    topic: str,
    provider: str = "ollama/llama3.3",
) -> list[IdeaNode]:
    """
    Quick helper to extract ideas from content.

    Example:
        ideas = await extract_ideas(
            article_text,
            "source_123",
            "AI regulation",
        )
    """
    config = ExtractionConfig(provider=provider)
    extractor = IdeaExtractor(config)
    result = await extractor.extract(content, source_id, topic)
    return result.ideas
