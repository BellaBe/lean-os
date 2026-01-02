"""
Hybrid Extractor - Multi-strategy extraction pipeline.

Extraction order:
1. CSS selectors (fastest, most reliable for known sites)
2. Regex patterns (fast, catches structured data)
3. Cosine similarity (filter irrelevant content)
4. LLM (only if needed for complex extraction)

This pipeline reduces LLM costs by extracting what we can
with fast methods first.
"""

import logging
import re
from dataclasses import dataclass, field
from datetime import datetime
from typing import Any

from .content_filter import ContentFilter, FilteredContent

logger = logging.getLogger(__name__)


@dataclass
class QuickExtraction:
    """Result of quick extraction (before LLM)."""

    # Basic metadata
    title: str = ""
    author: str = ""
    date: str = ""
    date_parsed: datetime | None = None

    # Content
    content: str = ""
    word_count: int = 0

    # Extracted data points
    citations: list[str] = field(default_factory=list)
    percentages: list[str] = field(default_factory=list)
    quotes: list[str] = field(default_factory=list)
    urls: list[str] = field(default_factory=list)
    numbers: list[str] = field(default_factory=list)

    # Filtered content for LLM
    relevant_chunks: list[str] = field(default_factory=list)
    relevance_ratio: float = 0.0

    # LLM decision
    needs_llm: bool = True
    skip_reason: str | None = None

    # Extraction stats
    tokens_saved: int = 0
    extraction_method: str = "none"

    def to_dict(self) -> dict[str, Any]:
        """Convert to dictionary for serialization."""
        return {
            "title": self.title,
            "author": self.author,
            "date": self.date,
            "word_count": self.word_count,
            "citation_count": len(self.citations),
            "percentage_count": len(self.percentages),
            "quote_count": len(self.quotes),
            "relevance_ratio": self.relevance_ratio,
            "needs_llm": self.needs_llm,
            "skip_reason": self.skip_reason,
            "tokens_saved": self.tokens_saved,
            "extraction_method": self.extraction_method,
        }


# CSS extraction schemas for different site types
CSS_SCHEMAS: dict[str, dict[str, str]] = {
    "news": {
        "title": "h1, .headline, .article-title, [data-testid='headline']",
        "author": ".author, .byline, [rel='author'], .article-author",
        "date": "time, .date, .published, [datetime], .article-date",
        "content": "article, .article-body, .story-body, .post-content",
    },
    "academic": {
        "title": "h1, .title, .paper-title, .article-title",
        "author": ".author, .authors, .contributor, [class*='author']",
        "date": ".date, .pub-date, [class*='date'], time",
        "content": ".abstract, .content, article, .paper-content",
        "abstract": ".abstract, #abstract, [class*='abstract']",
        "doi": "[class*='doi'], .doi, a[href*='doi.org']",
    },
    "social": {
        "title": "h1, .post-title, .tweet-text, [data-testid='tweetText']",
        "author": ".username, .author, [data-testid='User-Name']",
        "date": "time, .timestamp, [datetime]",
        "content": ".post-content, .tweet, .status, article",
    },
    "forum": {
        "title": "h1, .thread-title, .topic-title",
        "author": ".username, .author, .poster",
        "date": "time, .timestamp, .post-date",
        "content": ".post-body, .message, .comment-body",
    },
    "blog": {
        "title": "h1, .post-title, .entry-title",
        "author": ".author, .byline, [rel='author']",
        "date": "time, .date, .published, .post-date",
        "content": "article, .post-content, .entry-content, .blog-post",
    },
}

# Regex patterns for structured data extraction
REGEX_PATTERNS: dict[str, re.Pattern] = {
    # Citations and references
    "doi": re.compile(r"10\.\d{4,}/[^\s]+"),
    "arxiv_id": re.compile(r"arXiv:\d{4}\.\d{4,5}(?:v\d+)?", re.IGNORECASE),
    "url": re.compile(r"https?://[^\s<>\"')\]]+"),
    # Numbers and statistics
    "percentage": re.compile(r"\d+(?:\.\d+)?%"),
    "currency": re.compile(
        r"\$\d+(?:,\d{3})*(?:\.\d{2})?(?:\s*(?:million|billion|trillion))?",
        re.IGNORECASE,
    ),
    "large_number": re.compile(
        r"\d+(?:,\d{3})+|\d+\s*(?:million|billion|trillion)", re.IGNORECASE
    ),
    # Quotes
    "quote": re.compile(r'"([^"]{20,})"'),
    "quote_smart": re.compile(r'"([^"]{20,})"'),
    # Social signals
    "upvotes": re.compile(
        r"(\d+(?:,\d{3})*)\s*(?:upvotes?|points?|likes?)", re.IGNORECASE
    ),
    "comments": re.compile(r"(\d+(?:,\d{3})*)\s*comments?", re.IGNORECASE),
    # Dates
    "date_iso": re.compile(r"\d{4}-\d{2}-\d{2}"),
    "date_relative": re.compile(
        r"(\d+)\s*(?:hours?|days?|weeks?|months?)\s*ago", re.IGNORECASE
    ),
    # Author patterns
    "author_by": re.compile(
        r"(?:by|author:?)\s+([A-Z][a-z]+(?:\s+[A-Z][a-z]+)+)", re.IGNORECASE
    ),
}


class HybridExtractor:
    """
    Multi-strategy content extractor.

    Extracts structured data using:
    1. CSS selectors for known site patterns
    2. Regex for structured data (URLs, numbers, quotes)
    3. Semantic filtering for relevance
    4. LLM only when needed

    Usage:
        extractor = HybridExtractor(topic="AI safety")
        result = extractor.extract(html_content, url)

        if result.needs_llm:
            # Send result.relevant_chunks to LLM
            llm_ideas = await idea_extractor.extract(result.relevant_chunks)
        else:
            # Use quick extraction data directly
            process_quick_data(result)
    """

    def __init__(
        self,
        topic: str,
        keywords: list[str] | None = None,
        min_relevance: float = 0.2,
        min_word_count: int = 100,
    ):
        """
        Initialize the hybrid extractor.

        Args:
            topic: Topic for relevance filtering
            keywords: Additional keywords
            min_relevance: Minimum relevance ratio to process
            min_word_count: Minimum words to process
        """
        self.topic = topic
        self.keywords = keywords or []
        self.min_relevance = min_relevance
        self.min_word_count = min_word_count

        self.content_filter = ContentFilter(
            topic=topic,
            keywords=keywords,
            similarity_threshold=0.3,
        )

    def extract(
        self,
        content: str,
        url: str = "",
        html: str | None = None,
        site_type: str | None = None,
    ) -> QuickExtraction:
        """
        Extract structured data from content.

        Args:
            content: Markdown content
            url: Source URL (for site type detection)
            html: Optional raw HTML for CSS extraction
            site_type: Optional site type hint

        Returns:
            QuickExtraction with extracted data
        """
        result = QuickExtraction()
        result.word_count = len(content.split()) if content else 0

        # Check minimum content
        if result.word_count < self.min_word_count:
            result.needs_llm = False
            result.skip_reason = "Content too short"
            return result

        # Detect site type if not provided
        if not site_type:
            site_type = self._detect_site_type(url)

        # 1. CSS extraction (if HTML available)
        if html:
            css_data = self._css_extract(html, site_type)
            result.title = css_data.get("title", "")
            result.author = css_data.get("author", "")
            result.date = css_data.get("date", "")
            if css_data:
                result.extraction_method = "css"

        # 2. Regex extraction
        regex_data = self._regex_extract(content)
        result.citations = regex_data.get("citations", [])
        result.percentages = regex_data.get("percentages", [])
        result.quotes = regex_data.get("quotes", [])
        result.urls = regex_data.get("urls", [])
        result.numbers = regex_data.get("numbers", [])

        if not result.author and regex_data.get("author"):
            result.author = regex_data["author"]

        if regex_data:
            result.extraction_method = result.extraction_method or "regex"

        # 3. Parse date if found
        if result.date:
            result.date_parsed = self._parse_date(result.date)

        # 4. Content filtering for relevance
        filtered = self._filter_relevant_chunks(content)
        result.relevant_chunks = filtered.chunks
        result.relevance_ratio = filtered.relevance_ratio
        result.tokens_saved = filtered.tokens_saved_estimate
        result.content = filtered.get_combined_text(max_words=3000)

        # 5. Decide if LLM is needed
        result.needs_llm = self._should_use_llm(result)

        return result

    def _detect_site_type(self, url: str) -> str:
        """Detect site type from URL."""
        url_lower = url.lower()

        if any(
            x in url_lower
            for x in ["arxiv", "scholar", "pubmed", ".edu", "nature.com", "science.org"]
        ):
            return "academic"

        if any(x in url_lower for x in ["reddit.com", "x.com", "linkedin.com"]):
            return "social"

        if any(
            x in url_lower
            for x in ["forum", "discuss", "community", "news.ycombinator"]
        ):
            return "forum"

        if any(x in url_lower for x in ["medium.com", "substack", "blog", "wordpress"]):
            return "blog"

        if any(
            x in url_lower
            for x in ["nytimes", "bbc", "reuters", "wsj", "bloomberg", "cnn"]
        ):
            return "news"

        return "news"  # Default

    def _css_extract(self, html: str, site_type: str) -> dict[str, str]:
        """Extract using CSS selectors."""
        try:
            from bs4 import BeautifulSoup
        except ImportError:
            logger.debug("BeautifulSoup not available for CSS extraction")
            return {}

        schema = CSS_SCHEMAS.get(site_type, CSS_SCHEMAS["news"])
        soup = BeautifulSoup(html, "html.parser")

        extracted = {}
        for field_name, selectors in schema.items():
            for selector in selectors.split(", "):
                try:
                    element = soup.select_one(selector)
                    if element:
                        text = element.get_text(strip=True)
                        if text and len(text) > 2:
                            extracted[field_name] = text
                            break
                except Exception:
                    continue

        return extracted

    def _regex_extract(self, content: str) -> dict[str, Any]:
        """Extract structured data using regex patterns."""
        extracted: dict[str, Any] = {
            "citations": [],
            "percentages": [],
            "quotes": [],
            "urls": [],
            "numbers": [],
        }

        # DOIs and arxiv IDs
        dois = REGEX_PATTERNS["doi"].findall(content)
        arxiv_ids = REGEX_PATTERNS["arxiv_id"].findall(content)
        extracted["citations"] = list(set(dois + arxiv_ids))

        # URLs (limit to avoid spam)
        urls = REGEX_PATTERNS["url"].findall(content)
        extracted["urls"] = list(set(urls))[:20]

        # Percentages
        percentages = REGEX_PATTERNS["percentage"].findall(content)
        extracted["percentages"] = list(set(percentages))

        # Large numbers and currency
        currency = REGEX_PATTERNS["currency"].findall(content)
        large_nums = REGEX_PATTERNS["large_number"].findall(content)
        extracted["numbers"] = list(set(currency + large_nums))

        # Quotes
        quotes = REGEX_PATTERNS["quote"].findall(content)
        quotes += REGEX_PATTERNS["quote_smart"].findall(content)
        # Filter out very long quotes (probably not real quotes)
        extracted["quotes"] = [q for q in set(quotes) if len(q) < 500][:10]

        # Author
        author_match = REGEX_PATTERNS["author_by"].search(content[:1000])
        if author_match:
            extracted["author"] = author_match.group(1)

        return extracted

    def _filter_relevant_chunks(self, content: str) -> FilteredContent:
        """Filter content to relevant chunks."""
        return self.content_filter.filter(content)

    def _parse_date(self, date_str: str) -> datetime | None:
        """Try to parse a date string."""
        # Try ISO format first
        iso_match = REGEX_PATTERNS["date_iso"].search(date_str)
        if iso_match:
            try:
                return datetime.fromisoformat(iso_match.group())
            except ValueError:
                pass

        # Try relative dates
        rel_match = REGEX_PATTERNS["date_relative"].search(date_str)
        if rel_match:
            # Just return None for relative dates - they need more context
            return None

        # Try common formats
        common_formats = [
            "%B %d, %Y",
            "%b %d, %Y",
            "%d %B %Y",
            "%d %b %Y",
            "%m/%d/%Y",
            "%d/%m/%Y",
        ]
        for fmt in common_formats:
            try:
                return datetime.strptime(date_str.strip(), fmt)
            except ValueError:
                continue

        return None

    def _should_use_llm(self, result: QuickExtraction) -> bool:
        """
        Decide if LLM extraction is needed.

        LLM is NOT needed if:
        - Content is too short
        - Relevance is too low
        - We already have enough structured data

        LLM IS needed if:
        - We need to extract ideas/insights
        - Content is relevant but unstructured
        """
        # Skip if content too short
        if result.word_count < self.min_word_count:
            result.skip_reason = "Content too short"
            return False

        # Skip if relevance too low
        if result.relevance_ratio < self.min_relevance:
            result.skip_reason = f"Low relevance ({result.relevance_ratio:.2f})"
            return False

        # Skip if no relevant chunks
        if not result.relevant_chunks:
            result.skip_reason = "No relevant content"
            return False

        # Need LLM for idea extraction
        return True

    def get_extraction_stats(self, result: QuickExtraction) -> dict:
        """Get stats about the extraction."""
        return {
            "method": result.extraction_method,
            "word_count": result.word_count,
            "relevance_ratio": result.relevance_ratio,
            "tokens_saved": result.tokens_saved,
            "needs_llm": result.needs_llm,
            "skip_reason": result.skip_reason,
            "data_points": {
                "citations": len(result.citations),
                "percentages": len(result.percentages),
                "quotes": len(result.quotes),
                "urls": len(result.urls),
            },
        }


def quick_extract(
    content: str,
    topic: str,
    url: str = "",
    html: str | None = None,
) -> QuickExtraction:
    """
    Convenience function for quick extraction.

    Args:
        content: Markdown content
        topic: Topic for relevance
        url: Source URL
        html: Optional HTML

    Returns:
        QuickExtraction result
    """
    extractor = HybridExtractor(topic=topic)
    return extractor.extract(content, url=url, html=html)
