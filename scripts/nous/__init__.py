"""
Nous - Noosphere Snapshot Engine

Automated knowledge synthesis tool that crawls, extracts, and maps
the ideological landscape around any topic.

Enhanced with Crawl4AI for:
- Parallel crawling with domain batching
- Zone-aware configuration (Institutional/Grassroots/Speculative)
- Hybrid extraction (CSS → Regex → Cosine → LLM)
- Site-specific social/tech discovery (Twitter, LinkedIn, YCombinator)
- PageSnapshotter for social content (JavaScript rendering, screenshots)
"""

from .application import (
    SnapshotBuilder,
    SnapshotBuilderConfig,
)
from .domain import (
    IdeaNode,
    SearchResponse,
    SearchResult,
    SignalZone,
    Snapshot,
    SourceNode,
    SourceType,
    Stance,
)

# Crawl4AI-enhanced infrastructure
from .infrastructure.crawlers.diagnostics import CrawlDiagnostics, DropReason
from .infrastructure.crawlers.link_expander import (
    CitationChain,
    ExpansionResult,
    LinkExpander,
    LinkExpansionConfig,
)
from .infrastructure.crawlers.parallel_crawler import (
    BatchCrawlResult,
    ParallelCrawler,
)
from .infrastructure.crawlers.zone_config import (
    ZoneCrawlProfile,
    build_crawl_config,
    get_zone_for_domain,
)
from .infrastructure.crawlers.url_seeder import (
    generate_site_queries,
    SOCIAL_SITE_SEARCHES,
    TECH_SITE_SEARCHES,
    YC_DOMAINS,
)
from .infrastructure.crawlers.page_snapshot import (
    PageSnapshot,
    PageSnapshotter,
    PageSnapshotConfig,
    PageComparison,
    TemporalArchive,
    capture_page_snapshot,
)
from .infrastructure.extraction.content_filter import ContentFilter, FilteredContent
from .infrastructure.extraction.hybrid_extractor import HybridExtractor, QuickExtraction
from .infrastructure.crawlers.screenshot_extractor import (
    ExtractedArticle,
    HumanBehaviorConfig,
    ScreenshotExtractionResult,
    ScreenshotExtractor,
    extract_fallback_news,
)
from .infrastructure.crawlers.search_api import SCREENSHOT_FALLBACK_SITES

__version__ = "0.4.2"  # Quality filters: stricter relevance, word count, multi-source consensus, noise patterns, contention detection

__all__ = [
    # Domain
    "SourceType",
    "SignalZone",
    "Stance",
    "SourceNode",
    "IdeaNode",
    "Snapshot",
    "SearchResult",
    "SearchResponse",
    # Application - SnapshotBuilder (full pipeline)
    "SnapshotBuilder",
    "SnapshotBuilderConfig",
    # Crawl4AI Infrastructure - Crawlers
    "ParallelCrawler",
    "BatchCrawlResult",
    "CrawlDiagnostics",
    "DropReason",
    "LinkExpander",
    "LinkExpansionConfig",
    "ExpansionResult",
    "CitationChain",
    # Crawl4AI Infrastructure - Zone Config
    "get_zone_for_domain",
    "build_crawl_config",
    "ZoneCrawlProfile",
    # Site-specific discovery
    "generate_site_queries",
    "SOCIAL_SITE_SEARCHES",
    "TECH_SITE_SEARCHES",
    "YC_DOMAINS",
    # Page Snapshots (social content, evidence preservation)
    "PageSnapshot",
    "PageSnapshotter",
    "PageSnapshotConfig",
    "PageComparison",
    "TemporalArchive",
    "capture_page_snapshot",
    # Crawl4AI Infrastructure - Extraction
    "HybridExtractor",
    "QuickExtraction",
    "ContentFilter",
    "FilteredContent",
    # Screenshot extraction (for blocked sites: Reuters, Bloomberg, etc.)
    "ScreenshotExtractor",
    "ScreenshotExtractionResult",
    "ExtractedArticle",
    "HumanBehaviorConfig",
    "extract_fallback_news",
    "SCREENSHOT_FALLBACK_SITES",
]
