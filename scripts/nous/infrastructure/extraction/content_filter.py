"""
Pre-LLM content filtering using semantic similarity.

Filters content to only include relevant chunks before sending to LLM,
reducing token usage and improving extraction quality.

Uses Crawl4AI's CosineStrategy for semantic chunking when available,
with fallback to simple keyword-based filtering.
"""

import logging
import re
from dataclasses import dataclass, field

logger = logging.getLogger(__name__)


@dataclass
class FilteredContent:
    """Result of content filtering."""

    chunks: list[str] = field(default_factory=list)
    total_words: int = 0
    relevant_words: int = 0
    relevance_ratio: float = 0.0
    tokens_saved_estimate: int = 0

    @property
    def is_relevant(self) -> bool:
        """Check if content has enough relevant material."""
        return self.relevance_ratio > 0.1 and self.relevant_words > 50

    def get_combined_text(self, max_words: int | None = None) -> str:
        """
        Get filtered content as a single string.

        Args:
            max_words: Optional word limit

        Returns:
            Combined filtered text
        """
        combined = "\n\n".join(self.chunks)
        if max_words:
            words = combined.split()
            if len(words) > max_words:
                combined = " ".join(words[:max_words]) + "..."
        return combined


class ContentFilter:
    """
    Filter content to extract only relevant portions.

    Uses semantic similarity when Crawl4AI's CosineStrategy is available,
    falls back to keyword-based filtering otherwise.

    Usage:
        filter = ContentFilter(topic="artificial intelligence", keywords=["AI", "ML"])
        result = filter.filter(markdown_content)

        if result.is_relevant:
            send_to_llm(result.get_combined_text(max_words=2000))
    """

    def __init__(
        self,
        topic: str,
        keywords: list[str] | None = None,
        similarity_threshold: float = 0.3,
        min_chunk_words: int = 50,
        max_chunk_words: int = 500,
    ):
        """
        Initialize the content filter.

        Args:
            topic: Main topic for relevance scoring
            keywords: Additional keywords to boost relevance
            similarity_threshold: Minimum similarity score (0-1)
            min_chunk_words: Minimum words per chunk
            max_chunk_words: Maximum words per chunk
        """
        self.topic = topic.lower()
        self.keywords = [kw.lower() for kw in (keywords or [])]
        self.similarity_threshold = similarity_threshold
        self.min_chunk_words = min_chunk_words
        self.max_chunk_words = max_chunk_words

        # Try to use CosineStrategy
        self._cosine_available = False
        try:
            from crawl4ai.extraction_strategy import CosineStrategy

            self._cosine_strategy = CosineStrategy(
                semantic_filter=topic,
                word_count_threshold=min_chunk_words,
                sim_threshold=similarity_threshold,
            )
            self._cosine_available = True
            logger.debug("Using CosineStrategy for content filtering")
        except ImportError:
            logger.debug("CosineStrategy not available, using keyword-based filtering")

    def filter(self, content: str) -> FilteredContent:
        """
        Filter content to extract relevant portions.

        Args:
            content: Raw markdown/text content

        Returns:
            FilteredContent with relevant chunks
        """
        if not content or not content.strip():
            return FilteredContent()

        total_words = len(content.split())

        # Try CosineStrategy first
        if self._cosine_available:
            try:
                result = self._filter_with_cosine(content)
                if result.chunks:
                    return result
            except Exception as e:
                logger.warning(f"CosineStrategy failed, falling back: {e}")

        # Fall back to keyword-based filtering
        return self._filter_with_keywords(content, total_words)

    def _filter_with_cosine(self, content: str) -> FilteredContent:
        """Filter using Crawl4AI's CosineStrategy."""
        # CosineStrategy expects HTML, so wrap markdown
        html_content = f"<div>{content}</div>"

        result = self._cosine_strategy.extract(html_content, url="")

        if not result:
            return FilteredContent()

        # Extract chunks from result
        chunks = []
        if isinstance(result, list):
            for item in result:
                if isinstance(item, dict):
                    text = item.get("content", "") or item.get("text", "")
                    if text:
                        chunks.append(text)
                elif isinstance(item, str):
                    chunks.append(item)
        elif isinstance(result, str):
            chunks = [result]

        relevant_words = sum(len(chunk.split()) for chunk in chunks)
        total_words = len(content.split())

        return FilteredContent(
            chunks=chunks,
            total_words=total_words,
            relevant_words=relevant_words,
            relevance_ratio=relevant_words / total_words if total_words > 0 else 0,
            tokens_saved_estimate=int((total_words - relevant_words) * 1.3),
        )

    def _filter_with_keywords(self, content: str, total_words: int) -> FilteredContent:
        """Filter using keyword matching."""
        # Split into paragraphs/chunks
        paragraphs = self._split_into_chunks(content)

        # Score and filter chunks
        relevant_chunks = []
        for para in paragraphs:
            score = self._calculate_relevance_score(para)
            if score >= self.similarity_threshold:
                relevant_chunks.append(para)

        relevant_words = sum(len(chunk.split()) for chunk in relevant_chunks)

        return FilteredContent(
            chunks=relevant_chunks,
            total_words=total_words,
            relevant_words=relevant_words,
            relevance_ratio=relevant_words / total_words if total_words > 0 else 0,
            tokens_saved_estimate=int((total_words - relevant_words) * 1.3),
        )

    def _split_into_chunks(self, content: str) -> list[str]:
        """Split content into manageable chunks."""
        # Split on double newlines (paragraphs)
        paragraphs = re.split(r"\n\n+", content)

        chunks = []
        current_chunk = []
        current_words = 0

        for para in paragraphs:
            para = para.strip()
            if not para:
                continue

            para_words = len(para.split())

            # Skip very short paragraphs
            if para_words < 10:
                continue

            # If adding this paragraph would exceed max, start new chunk
            if current_words + para_words > self.max_chunk_words and current_chunk:
                combined = "\n\n".join(current_chunk)
                if len(combined.split()) >= self.min_chunk_words:
                    chunks.append(combined)
                current_chunk = []
                current_words = 0

            current_chunk.append(para)
            current_words += para_words

            # If current chunk is at max, flush it
            if current_words >= self.max_chunk_words:
                combined = "\n\n".join(current_chunk)
                if len(combined.split()) >= self.min_chunk_words:
                    chunks.append(combined)
                current_chunk = []
                current_words = 0

        # Don't forget the last chunk
        if current_chunk:
            combined = "\n\n".join(current_chunk)
            if len(combined.split()) >= self.min_chunk_words:
                chunks.append(combined)

        return chunks

    def _calculate_relevance_score(self, text: str) -> float:
        """
        Calculate relevance score for a text chunk.

        Uses keyword density and topic word matching.
        """
        text_lower = text.lower()
        words = text_lower.split()
        word_count = len(words)

        if word_count == 0:
            return 0.0

        score = 0.0

        # Topic word matching
        topic_words = self.topic.split()
        topic_matches = sum(1 for tw in topic_words if tw in text_lower)
        if topic_matches > 0:
            score += min(topic_matches / len(topic_words), 0.5)

        # Keyword matching
        keyword_matches = sum(1 for kw in self.keywords if kw in text_lower)
        if keyword_matches > 0:
            score += min(keyword_matches * 0.1, 0.3)

        # Density bonus (more topic words = higher score)
        topic_density = sum(text_lower.count(tw) for tw in topic_words) / word_count
        score += min(topic_density * 10, 0.2)

        return min(score, 1.0)

    def get_relevance_summary(self, content: str) -> dict:
        """
        Get a summary of content relevance without full filtering.

        Useful for quick relevance checks.
        """
        filtered = self.filter(content)
        return {
            "total_words": filtered.total_words,
            "relevant_words": filtered.relevant_words,
            "relevance_ratio": filtered.relevance_ratio,
            "chunk_count": len(filtered.chunks),
            "tokens_saved": filtered.tokens_saved_estimate,
            "is_relevant": filtered.is_relevant,
        }


def filter_for_topic(
    content: str,
    topic: str,
    keywords: list[str] | None = None,
    threshold: float = 0.3,
) -> FilteredContent:
    """
    Convenience function for content filtering.

    Args:
        content: Text to filter
        topic: Main topic
        keywords: Additional keywords
        threshold: Minimum relevance threshold

    Returns:
        FilteredContent
    """
    filter = ContentFilter(
        topic=topic,
        keywords=keywords,
        similarity_threshold=threshold,
    )
    return filter.filter(content)
