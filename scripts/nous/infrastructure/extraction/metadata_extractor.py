"""
Fast Metadata Extraction using Regex Patterns

Uses Crawl4AI's RegexExtractionStrategy for instant extraction of:
- Publication dates
- Authors
- Citations/references
- Social signals (hashtags, handles)

No LLM needed - pattern-based extraction is instant and free.
"""

import json
import re
from dataclasses import dataclass, field
from datetime import datetime
from enum import IntFlag, auto


@dataclass
class ExtractedMetadata:
    """Metadata extracted from content using regex patterns."""

    url: str

    # Temporal
    dates: list[str] = field(default_factory=list)
    iso_dates: list[str] = field(default_factory=list)

    # Attribution
    authors: list[str] = field(default_factory=list)
    emails: list[str] = field(default_factory=list)

    # References
    urls: list[str] = field(default_factory=list)
    citations: list[str] = field(default_factory=list)

    # Social signals
    twitter_handles: list[str] = field(default_factory=list)
    hashtags: list[str] = field(default_factory=list)

    # Numeric
    percentages: list[str] = field(default_factory=list)
    currencies: list[str] = field(default_factory=list)

    extracted_at: datetime = field(default_factory=datetime.utcnow)


class MetadataPatterns(IntFlag):
    """Patterns to extract - can be combined with |"""

    NONE = 0
    DATE_ISO = auto()
    DATE_US = auto()
    EMAIL = auto()
    URL = auto()
    TWITTER = auto()
    HASHTAG = auto()
    PERCENTAGE = auto()
    CURRENCY = auto()
    PHONE = auto()

    # Convenience combinations
    DATES = DATE_ISO | DATE_US
    SOCIAL = TWITTER | HASHTAG
    ATTRIBUTION = EMAIL | TWITTER
    NUMERIC = PERCENTAGE | CURRENCY
    ALL = DATE_ISO | DATE_US | EMAIL | URL | TWITTER | HASHTAG | PERCENTAGE | CURRENCY | PHONE


# Custom patterns for content analysis
CUSTOM_PATTERNS = {
    # Author patterns (common formats)
    "author": r"(?:by|author|written by|posted by)[\s:]+([A-Z][a-z]+(?:\s+[A-Z][a-z]+){1,2})",
    # Citation patterns
    "citation_bracket": r"\[(\d{1,3})\]",  # [1], [23]
    "citation_paren": r"\(([A-Z][a-z]+(?:\s+et\s+al\.?)?,?\s*\d{4})\)",  # (Smith, 2023)
    # Academic identifiers
    "doi": r"(?:doi[:\s]*)?10\.\d{4,}/[^\s]+",
    "arxiv": r"arXiv:\d{4}\.\d{4,5}(?:v\d+)?",
    # Quote detection (for claim extraction)
    "quoted_text": r'"([^"]{20,200})"',
}


class MetadataExtractor:
    """
    Fast metadata extraction using regex patterns.

    Uses Crawl4AI's RegexExtractionStrategy when available,
    falls back to native Python regex.
    """

    def __init__(self, use_crawl4ai: bool = True):
        """
        Args:
            use_crawl4ai: Try to use Crawl4AI's optimized extractor
        """
        self.use_crawl4ai = use_crawl4ai
        self._strategy = None

    def _get_crawl4ai_strategy(self, patterns: MetadataPatterns):
        """Get Crawl4AI RegexExtractionStrategy if available."""
        if not self.use_crawl4ai:
            return None

        try:
            from crawl4ai import RegexExtractionStrategy

            # Map our patterns to Crawl4AI patterns
            c4a_pattern = 0

            if patterns & MetadataPatterns.DATE_ISO:
                c4a_pattern |= RegexExtractionStrategy.DateIso
            if patterns & MetadataPatterns.DATE_US:
                c4a_pattern |= RegexExtractionStrategy.DateUS
            if patterns & MetadataPatterns.EMAIL:
                c4a_pattern |= RegexExtractionStrategy.Email
            if patterns & MetadataPatterns.URL:
                c4a_pattern |= RegexExtractionStrategy.Url
            if patterns & MetadataPatterns.TWITTER:
                c4a_pattern |= RegexExtractionStrategy.TwitterHandle
            if patterns & MetadataPatterns.HASHTAG:
                c4a_pattern |= RegexExtractionStrategy.Hashtag
            if patterns & MetadataPatterns.PERCENTAGE:
                c4a_pattern |= RegexExtractionStrategy.Percentage
            if patterns & MetadataPatterns.CURRENCY:
                c4a_pattern |= RegexExtractionStrategy.Currency
            if patterns & MetadataPatterns.PHONE:
                c4a_pattern |= RegexExtractionStrategy.PhoneUS

            return RegexExtractionStrategy(pattern=c4a_pattern)

        except ImportError:
            return None

    def extract(
        self,
        content: str,
        url: str = "",
        patterns: MetadataPatterns = MetadataPatterns.ALL,
        include_custom: bool = True,
    ) -> ExtractedMetadata:
        """
        Extract metadata from content using regex patterns.

        Args:
            content: Text content to analyze
            url: Source URL for reference
            patterns: Which patterns to extract
            include_custom: Include custom patterns (authors, citations)

        Returns:
            ExtractedMetadata with all extracted values
        """
        metadata = ExtractedMetadata(url=url)

        # Try Crawl4AI strategy first
        strategy = self._get_crawl4ai_strategy(patterns)
        if strategy:
            try:
                # Strategy can run on content directly
                results = strategy.run("", [content])
                if results:
                    data = json.loads(results) if isinstance(results, str) else results
                    self._parse_c4a_results(data, metadata)
            except Exception:
                pass  # Fall back to native extraction

        # Native extraction (always run for completeness)
        self._extract_native(content, patterns, metadata)

        # Custom patterns
        if include_custom:
            self._extract_custom(content, metadata)

        return metadata

    def _parse_c4a_results(self, results: list, metadata: ExtractedMetadata):
        """Parse Crawl4AI RegexExtractionStrategy results."""
        for item in results:
            label = item.get("label", "")
            value = item.get("value", "")

            if label == "email":
                metadata.emails.append(value)
            elif label == "url":
                metadata.urls.append(value)
            elif label == "date_iso":
                metadata.iso_dates.append(value)
            elif label == "date_us":
                metadata.dates.append(value)
            elif label == "twitter_handle":
                metadata.twitter_handles.append(value)
            elif label == "hashtag":
                metadata.hashtags.append(value)
            elif label == "percentage":
                metadata.percentages.append(value)
            elif label == "currency":
                metadata.currencies.append(value)

    def _extract_native(
        self,
        content: str,
        patterns: MetadataPatterns,
        metadata: ExtractedMetadata,
    ):
        """Native Python regex extraction."""

        if patterns & MetadataPatterns.DATE_ISO:
            # ISO format: 2024-01-15, 2024/01/15
            iso_pattern = r"\b(\d{4}[-/]\d{2}[-/]\d{2})\b"
            for match in re.finditer(iso_pattern, content):
                if match.group(1) not in metadata.iso_dates:
                    metadata.iso_dates.append(match.group(1))

        if patterns & MetadataPatterns.DATE_US:
            # US format: January 15, 2024 or 01/15/2024
            us_patterns = [
                r"\b((?:January|February|March|April|May|June|July|August|September|October|November|December)\s+\d{1,2},?\s+\d{4})\b",
                r"\b(\d{1,2}/\d{1,2}/\d{2,4})\b",
            ]
            for pattern in us_patterns:
                for match in re.finditer(pattern, content, re.IGNORECASE):
                    if match.group(1) not in metadata.dates:
                        metadata.dates.append(match.group(1))

        if patterns & MetadataPatterns.EMAIL:
            email_pattern = r"\b([a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,})\b"
            for match in re.finditer(email_pattern, content):
                if match.group(1) not in metadata.emails:
                    metadata.emails.append(match.group(1))

        if patterns & MetadataPatterns.URL:
            url_pattern = r"https?://[^\s<>\"'{}|\\^`\[\]]+"
            for match in re.finditer(url_pattern, content):
                url = match.group(0).rstrip(".,;:!?)")
                if url not in metadata.urls:
                    metadata.urls.append(url)

        if patterns & MetadataPatterns.TWITTER:
            twitter_pattern = r"@([a-zA-Z_][a-zA-Z0-9_]{0,14})\b"
            for match in re.finditer(twitter_pattern, content):
                handle = f"@{match.group(1)}"
                if handle not in metadata.twitter_handles:
                    metadata.twitter_handles.append(handle)

        if patterns & MetadataPatterns.HASHTAG:
            hashtag_pattern = r"#([a-zA-Z][a-zA-Z0-9_]*)\b"
            for match in re.finditer(hashtag_pattern, content):
                tag = f"#{match.group(1)}"
                if tag not in metadata.hashtags:
                    metadata.hashtags.append(tag)

        if patterns & MetadataPatterns.PERCENTAGE:
            pct_pattern = r"\b(\d+(?:\.\d+)?%)\b"
            for match in re.finditer(pct_pattern, content):
                if match.group(1) not in metadata.percentages:
                    metadata.percentages.append(match.group(1))

        if patterns & MetadataPatterns.CURRENCY:
            # USD, EUR, GBP formats
            currency_pattern = r"(?:\$|€|£|USD|EUR|GBP)\s*\d{1,3}(?:,\d{3})*(?:\.\d{2})?"
            for match in re.finditer(currency_pattern, content):
                if match.group(0) not in metadata.currencies:
                    metadata.currencies.append(match.group(0))

    def _extract_custom(self, content: str, metadata: ExtractedMetadata):
        """Extract using custom patterns."""

        # Authors
        author_pattern = CUSTOM_PATTERNS["author"]
        for match in re.finditer(author_pattern, content, re.IGNORECASE):
            author = match.group(1).strip()
            if author not in metadata.authors and len(author) < 50:
                metadata.authors.append(author)

        # Academic citations
        for pattern_name in ["citation_bracket", "citation_paren"]:
            pattern = CUSTOM_PATTERNS[pattern_name]
            for match in re.finditer(pattern, content):
                citation = match.group(0)
                if citation not in metadata.citations:
                    metadata.citations.append(citation)

        # DOIs and arXiv
        for pattern_name in ["doi", "arxiv"]:
            pattern = CUSTOM_PATTERNS[pattern_name]
            for match in re.finditer(pattern, content, re.IGNORECASE):
                ref = match.group(0)
                if ref not in metadata.citations:
                    metadata.citations.append(ref)


class QuoteExtractor:
    """Extract quoted text that may represent claims or key statements."""

    def __init__(self, min_length: int = 20, max_length: int = 500):
        self.min_length = min_length
        self.max_length = max_length

    def extract(self, content: str) -> list[str]:
        """
        Extract quoted statements from content.

        These are often direct claims or key positions.
        """
        quotes = []

        # Double quotes
        for match in re.finditer(r'"([^"]+)"', content):
            quote = match.group(1).strip()
            if self.min_length <= len(quote) <= self.max_length:
                quotes.append(quote)

        # Single quotes (be more conservative)
        for match in re.finditer(r"'([^']{30,})'", content):
            quote = match.group(1).strip()
            if self.min_length <= len(quote) <= self.max_length:
                # Avoid common contractions and possessives
                if not any(word in quote.lower() for word in ["it's", "don't", "can't"]):
                    quotes.append(quote)

        return quotes


# Convenience function
def extract_metadata(
    content: str,
    url: str = "",
    patterns: MetadataPatterns = MetadataPatterns.ALL,
) -> ExtractedMetadata:
    """
    Quick helper to extract metadata from content.

    Example:
        metadata = extract_metadata(article_text)
        print(f"Found {len(metadata.dates)} dates")
        print(f"Authors: {metadata.authors}")
    """
    extractor = MetadataExtractor()
    return extractor.extract(content, url, patterns)
