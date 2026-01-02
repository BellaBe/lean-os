"""
Idea Extraction with LLM and Chunking Support

Uses Crawl4AI's LLMExtractionStrategy with automatic chunking
for processing long articles that exceed token limits.

Key features:
- Automatic chunking with overlap for context preservation
- Schema-based extraction for structured output
- Multi-provider support via LiteLLM
- Integration with HybridExtractor for pre-filtered content
"""

import json
import logging
import os
import re
from dataclasses import dataclass, field
from datetime import UTC, datetime
from typing import TYPE_CHECKING

from pydantic import BaseModel, Field

log = logging.getLogger("nous.extract")

from ...domain import IdeaId, IdeaNode, SourceId, Stance

if TYPE_CHECKING:
    from .hybrid_extractor import QuickExtraction


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
    max_tokens: int = 1000  # Reduced for rate limit safety

    # Chunking settings - smaller for Groq free tier
    apply_chunking: bool = True
    chunk_token_threshold: int = 1000  # Smaller chunks for rate limits
    overlap_rate: float = 0.1  # 10% overlap between chunks

    # Input settings
    input_format: str = "markdown"  # or "html", "fit_markdown"

    # Extraction settings
    min_claim_length: int = 20
    min_claim_word_count: int = 8  # Minimum words in claim (filters metadata noise)
    max_claims_per_source: int = 10  # Reduced to limit output tokens
    filter_noise_patterns: bool = True  # Filter out metadata, UI, and off-topic noise

    # Rate limiting for Groq free tier (6000 TPM)
    tokens_per_minute: int = 6000
    token_safety_margin: float = 0.8  # Use only 80% of limit
    min_wait_between_calls: float = 2.0  # Minimum seconds between LLM calls


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
    tokens_saved: int = 0  # Tokens saved by pre-filtering
    extraction_time_ms: int = 0
    used_pre_extracted: bool = False  # Whether HybridExtractor data was used

    extracted_at: datetime = field(default_factory=lambda: datetime.now(UTC))


class IdeaExtractor:
    """
    Extracts ideas/claims from content using LLM.

    Supports:
    - Automatic chunking for long documents
    - Schema-based extraction for structured output
    - Multiple LLM providers via LiteLLM
    """

    # Noise patterns that indicate metadata, UI, or off-topic content
    NOISE_PATTERNS = [
        # Reddit/social metadata
        r"\d+\s*members?\s*online",
        r"\d+\s*(upvotes?|downvotes?|points?)",
        r"\d+\s*comments?",
        r"r/\w+\s*(has|have)",
        r"posted\s*(by|in)\s*r/",
        r"join(ed)?\s*r/",
        # Challenge/competition announcements
        r"challenge\s*(deadline|submission|winners?)",
        r"submit\s*(your|by|before)",
        r"call\s*for\s*(papers?|submissions?|proposals?)",
        # Conference/workshop logistics
        r"registration\s*(open|closes?|deadline)",
        r"workshop\s*(at|during|deadline)",
        r"accepted\s*(papers?|talks?)",
        r"keynote\s*speaker",
        # UI/navigation text
        r"click\s*here",
        r"read\s*more",
        r"subscribe\s*(to|for)",
        r"sign\s*up",
        r"follow\s*us",
        # Generic meta
        r"sponsored\s*(by|content)",
        r"advertisement",
    ]

    # Extraction prompt template
    EXTRACTION_PROMPT = """Extract claims and arguments from this content about: {topic}

For each claim found, provide:
- claim: The main statement (1-2 sentences)
- stance: "support", "oppose", or "neutral"
- confidence: 0.0 to 1.0

Focus on factual claims, opinions, predictions. Ignore navigation text and fluff.

Return JSON in this exact format:
{{"ideas": [
  {{"claim": "Example claim here", "stance": "support", "confidence": 0.8}},
  {{"claim": "Another claim", "stance": "neutral", "confidence": 0.7}}
]}}

Extract 3-10 claims. Return empty ideas array if no relevant claims found: {{"ideas": []}}"""

    def __init__(self, config: ExtractionConfig | None = None):
        self.config = config or ExtractionConfig()
        self._strategy = None
        # Pre-compile noise patterns for efficiency
        self._noise_regex = [re.compile(p, re.IGNORECASE) for p in self.NOISE_PATTERNS]

    def _is_noise_claim(self, claim: str) -> bool:
        """Check if a claim matches noise patterns (metadata, UI, off-topic)."""
        if not self.config.filter_noise_patterns:
            return False
        claim_lower = claim.lower()
        for pattern in self._noise_regex:
            if pattern.search(claim_lower):
                return True
        return False

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
        content: str | list[str],
        source_id: SourceId,
        topic: str,
        pre_extracted: "QuickExtraction | None" = None,
    ) -> ExtractionResult:
        """
        Extract ideas from content.

        Args:
            content: Text content to analyze (str or list of pre-filtered chunks)
            source_id: ID of the source
            topic: Topic context for extraction
            pre_extracted: Optional QuickExtraction from HybridExtractor

        Returns:
            ExtractionResult with extracted IdeaNodes
        """
        import time

        start_time = time.time()
        tokens_saved = 0
        used_pre_extracted = False

        # Handle pre-extracted data from HybridExtractor
        if pre_extracted is not None:
            # Check if LLM is needed
            if not pre_extracted.needs_llm:
                log.debug(f"Skipping LLM: {pre_extracted.skip_reason}")
                return ExtractionResult(
                    source_id=source_id,
                    ideas=[],
                    summary=None,
                    sentiment=None,
                    tokens_saved=pre_extracted.tokens_saved,
                    used_pre_extracted=True,
                )

            # Use pre-filtered relevant chunks
            if pre_extracted.relevant_chunks:
                content = "\n\n".join(pre_extracted.relevant_chunks)
                tokens_saved = pre_extracted.tokens_saved
                used_pre_extracted = True
                log.debug(
                    f"Using {len(pre_extracted.relevant_chunks)} pre-filtered chunks "
                    f"(saved ~{tokens_saved} tokens)"
                )

        # Handle list of chunks
        if isinstance(content, list):
            content = "\n\n".join(content)

        # Validate content
        if not content or len(content.strip()) < 100:
            return ExtractionResult(
                source_id=source_id,
                ideas=[],
                summary=None,
                sentiment=None,
                tokens_saved=tokens_saved,
                used_pre_extracted=used_pre_extracted,
            )

        # Use LiteLLM directly for text content extraction
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
            tokens_saved=tokens_saved,
            extraction_time_ms=elapsed_ms,
            used_pre_extracted=used_pre_extracted,
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
        """Extraction using LiteLLM with global Groq rate limiter."""
        try:
            import asyncio

            import litellm

            from ..llm.groq_limiter import get_groq_limiter

            limiter = get_groq_limiter()

            # Truncate content to fit token budget (max 2000 tokens for content)
            content = limiter.truncate_for_budget(content, max_tokens=2000)

            # No chunking - single request with truncated content
            # This is more reliable than multiple small chunks
            system_prompt = self.EXTRACTION_PROMPT.format(topic=topic)

            # Estimate tokens
            prompt_tokens = limiter.estimate_tokens(system_prompt + content)
            estimated_total = prompt_tokens + self.config.max_tokens

            # Wait for rate limit budget
            log.debug(f"LLM call: estimated {estimated_total} tokens")
            await limiter.wait_if_needed(estimated_total)

            try:
                log.debug(f"Calling LLM: {self.config.provider}")
                response = await litellm.acompletion(
                    model=self.config.provider,
                    messages=[
                        {"role": "system", "content": system_prompt},
                        {"role": "user", "content": f"Content to analyze:\n\n{content}"},
                    ],
                    temperature=self.config.temperature,
                    max_tokens=self.config.max_tokens,
                    response_format={"type": "json_object"},
                )

                # Record actual usage
                actual_tokens = 0
                if hasattr(response, "usage"):
                    actual_tokens = response.usage.total_tokens
                    limiter.record_usage(actual_tokens)
                    log.debug(f"LLM response: {actual_tokens} tokens used")

                # Parse response
                resp_content = response.choices[0].message.content
                log.debug(f"LLM raw response length: {len(resp_content)} chars")
                log.debug(f"LLM response preview: {resp_content[:500]}")

                try:
                    data = json.loads(resp_content)
                except json.JSONDecodeError as e:
                    log.error(f"JSON parse error: {e}")
                    log.error(f"Raw response: {resp_content[:500]}")
                    print(f"      [JSON Error] {e} - Response: {resp_content[:200]}")
                    return {"ideas": []}

                # Handle various response formats
                if isinstance(data, list):
                    ideas = data  # LLM returned array directly
                    log.debug(f"Parsed as list: {len(ideas)} items")
                elif isinstance(data, dict):
                    ideas = data.get("ideas", [])
                    log.debug(f"Parsed as dict: {len(ideas)} ideas")
                else:
                    ideas = []
                    log.warning(f"Unexpected response type: {type(data)}")

                log.info(f"Extraction complete: {len(ideas)} ideas")
                return {
                    "ideas": ideas[:self.config.max_claims_per_source],
                    "chunks": 1,
                    "tokens": actual_tokens,
                }

            except Exception as e:
                error_str = str(e).lower()
                if "rate" in error_str and "limit" in error_str:
                    # Parse wait time from Groq error
                    wait_time = limiter.parse_retry_after(str(e))
                    print(f"      [Groq] Rate limit, waiting {wait_time:.1f}s...")
                    await asyncio.sleep(wait_time)

                    # Single retry
                    try:
                        response = await litellm.acompletion(
                            model=self.config.provider,
                            messages=[
                                {"role": "system", "content": system_prompt},
                                {"role": "user", "content": f"Content to analyze:\n\n{content}"},
                            ],
                            temperature=self.config.temperature,
                            max_tokens=self.config.max_tokens,
                            response_format={"type": "json_object"},
                        )

                        if hasattr(response, "usage"):
                            limiter.record_usage(response.usage.total_tokens)

                        resp_content = response.choices[0].message.content
                        data = json.loads(resp_content)
                        ideas = data.get("ideas", []) if isinstance(data, dict) else []

                        return {"ideas": ideas[:self.config.max_claims_per_source], "chunks": 1}

                    except Exception:
                        print(f"      [Groq] Retry failed, skipping source")
                        return {"ideas": []}
                else:
                    print(f"      Extraction failed: {e}")
                    return {"ideas": []}

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

            # Skip short claims (by character count and word count)
            claim = item.get("claim", "")
            if len(claim) < self.config.min_claim_length:
                continue

            # Filter by word count to exclude metadata noise
            word_count = len(claim.split())
            if word_count < self.config.min_claim_word_count:
                log.debug(f"Skipping short claim ({word_count} words): {claim[:50]}...")
                continue

            # Filter noise patterns (metadata, UI, off-topic)
            if self._is_noise_claim(claim):
                log.debug(f"Skipping noise claim: {claim[:50]}...")
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
