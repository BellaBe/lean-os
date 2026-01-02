"""Configuration for snapshot building."""


from dataclasses import dataclass, field


@dataclass
class SnapshotBuilderConfig:
    """Configuration for snapshot building."""

    # Discovery via Search APIs
    # Sources: "news", "academic", "social", "web", "all"
    # Providers: rss (news, 20+ feeds), arxiv (academic), reddit (social), duckduckgo (web)
    sources: list[str] = field(default_factory=lambda: ["news", "academic", "social", "web"])
    max_urls: int = 20
    max_results_per_source: int = 50

    # Site-specific discovery (Twitter, LinkedIn, YouTube, YCombinator, etc.)
    # Uses DuckDuckGo site: queries to find content on platforms without APIs
    use_site_specific_search: bool = True  # Enable site-specific social/tech searches

    # Region/Geolocation
    region: str | None = None  # Single region: "us", "de", "fr", "gb", "jp", etc.
    regions: list[str] | None = None  # Multi-region: ["us", "de", "gb"]

    # Multi-language support
    target_languages: list[str] | None = None  # Languages to search: ["en", "de", "fr"]
    translate_queries: bool = False  # Use LLM to translate queries

    # Query augmentation
    augment_queries: bool = True  # Generate multiple query variations
    max_query_variations: int = 3  # Number of query variations to generate

    # Pipeline control (NEW - for consolidation)
    discovery_only: bool = False  # Skip extraction/analysis, return URLs only
    skip_crawling: bool = False  # Return discovered URLs without crawling
    use_pipeline_stages: bool = False  # Use new modular pipeline stages
    expand_domains: bool = True  # Expand discovered domains via seeding

    # Pre-crawl relevance filtering
    filter_relevance: bool = True  # Enable LLM-based relevance filtering
    relevance_threshold: int = 6  # Minimum score (1-10) to keep URL
    relevance_batch_size: int = 30  # URLs to score per LLM call
    max_urls_to_filter: int = 60  # Limit URLs sent to filter (saves API calls)

    # Post-extraction idea filtering
    filter_ideas: bool = True  # Filter extracted ideas by topic relevance
    idea_relevance_threshold: int = 7  # Minimum score (1-10) to keep idea (raised from 6 for stricter quality)
    min_idea_word_count: int = 8  # Minimum words in a claim (filters out metadata noise like "46 members online")
    min_relevant_ideas: int = 5  # Minimum relevant ideas before re-search
    max_search_iterations: int = 2  # Max re-search attempts with new queries

    # Crawling (Crawl4AI-enhanced)
    max_concurrent_crawls: int = 10  # Increased for parallel crawler
    crawl_timeout: int = 60
    max_content_chars: int = 15000  # Limit content per source for LLM processing
    use_parallel_crawler: bool = True  # Use ParallelCrawler with domain batching
    use_zone_config: bool = True  # Apply zone-aware crawl settings
    show_diagnostics: bool = True  # Show crawl diagnostics in output

    # Human-like behavior (avoid detection/blocking)
    use_human_delays: bool = True  # Add random delays between requests
    min_crawl_delay: float = 1.0  # Minimum delay between requests (seconds)
    max_crawl_delay: float = 3.0  # Maximum delay between requests (seconds)

    # Screenshot fallback (for blocked sites: Reuters, Bloomberg, WSJ, FT)
    use_screenshot_fallback: bool = False  # Extract from blocked sites via screenshot
    screenshot_llm_provider: str = "groq/llama-3.2-90b-vision-preview"  # Vision LLM

    # Pre-LLM Extraction (Crawl4AI-enhanced)
    use_hybrid_extraction: bool = True  # Pre-filter content before LLM
    hybrid_min_relevance: float = 0.3  # Minimum relevance for content chunks

    # Domain Expansion via URL Seeding (Crawl4AI AsyncUrlSeeder)
    use_domain_expansion: bool = True  # Expand discovered domains via sitemap/CC
    expansion_max_per_domain: int = 10  # Max URLs to add per domain
    expansion_score_threshold: float = 0.3  # BM25 relevance threshold
    expansion_source: str = "sitemap"  # "sitemap", "cc", or "sitemap+cc"
    expansion_extract_head: bool = True  # Get metadata for better filtering
    expansion_max_domains: int = 5  # Limit domains to expand (top by URL count)

    # Extraction
    llm_provider: str = "groq/llama-3.1-8b-instant"
    llm_api_key: str | None = None
    max_ideas_per_source: int = 10
    chunk_token_threshold: int = 1500  # Smaller chunks for rate-limited APIs

    # Analysis
    consensus_threshold: float = 0.7
    contention_threshold: float = 0.4
    min_cluster_size: int = 2

    # Social Page Snapshots (Twitter, LinkedIn, YouTube, etc.)
    use_social_snapshots: bool = True  # Use PageSnapshotter for social URLs
    social_snapshot_screenshot: bool = True  # Capture screenshots
    social_snapshot_delay: float = 2.0  # Wait for dynamic content to load
    social_snapshot_output_dir: str | None = None  # Directory to save snapshots (None = don't save)

    # Output
    generate_summary: bool = True
    build_graph: bool = True
