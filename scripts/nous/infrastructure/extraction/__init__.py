"""Extraction infrastructure for Nous."""

from .idea_extractor import (
    ChunkingStrategy,
    ExtractionConfig,
    ExtractionResult,
    IdeaExtractor,
    extract_ideas,
)
from .metadata_extractor import (
    CUSTOM_PATTERNS,
    ExtractedMetadata,
    MetadataExtractor,
    MetadataPatterns,
    QuoteExtractor,
    extract_metadata,
)

__all__ = [
    # Metadata extraction
    "MetadataExtractor",
    "ExtractedMetadata",
    "MetadataPatterns",
    "QuoteExtractor",
    "extract_metadata",
    "CUSTOM_PATTERNS",
    # Idea extraction
    "IdeaExtractor",
    "ExtractionConfig",
    "ExtractionResult",
    "ChunkingStrategy",
    "extract_ideas",
]
