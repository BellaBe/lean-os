# Nous - Noosphere Snapshot Engine

Automated knowledge synthesis tool that crawls, extracts, and maps the ideological landscape around any topic. Generates point-in-time snapshots of collective human thought.

## Directory Structure

```
nous/
├── pyproject.toml
├── README.md
├── __init__.py
├── domain/
│   ├── __init__.py
│   └── entities.py
├── application/
│   ├── __init__.py
│   ├── seeded_discovery.py      # PRIMARY - Use this
│   └── source_discovery.py      # DEPRECATED - SERP-based, hits anti-bot
├── infrastructure/
│   ├── __init__.py
│   ├── analysis/
│   │   ├── __init__.py
│   │   └── consensus_detector.py
│   ├── crawlers/
│   │   ├── __init__.py
│   │   ├── browser_config.py    # Anti-bot evasion
│   │   ├── content_crawler.py
│   │   ├── link_analyzer.py
│   │   ├── schema_manager.py
│   │   ├── serp_crawler.py      # DEPRECATED - hits anti-bot
│   │   ├── session_manager.py   # Auth persistence
│   │   ├── snapshot_capture.py  # PDF/Screenshot/MHTML
│   │   └── url_seeder.py        # PRIMARY - Bulk URL discovery
│   ├── extraction/
│   │   ├── __init__.py
│   │   ├── idea_extractor.py
│   │   └── metadata_extractor.py
│   └── llm/
│       ├── __init__.py
│       └── client.py
├── interface/
│   ├── __init__.py
│   └── cli.py
└── examples/
    └── quick_start.py
```

## Prerequisites

- **Python**: 3.12+
- **OS**: Linux, macOS, Windows (WSL recommended)

## Installation

```bash
# Clone/download the project
cd nous

# Install with all dependencies
pip install -e ".[all]"

# Set up browser automation (for content crawling)
crawl4ai-setup
```

### Dependency Groups

```bash
pip install -e "."           # Core only (pydantic)
pip install -e ".[crawl]"    # + crawl4ai
pip install -e ".[llm]"      # + litellm
pip install -e ".[all]"      # Everything
pip install -e ".[dev]"      # + pytest, ruff, mypy
```

## Quick Start

### Basic Usage (Recommended)

```python
import asyncio
from nous import discover_news

async def main():
    # Discover sources about AI regulation from news sites
    result = await discover_news("AI regulation EU", max_urls=50)
    
    print(f"URLs discovered: {result.urls_discovered}")
    print(f"Sources crawled: {result.urls_crawled}")
    print(f"Average relevance: {result.avg_relevance_score:.2f}")
    
    for source in result.sources[:10]:
        score = source.metadata.get("relevance_score", 0)
        print(f"  [{score:.2f}] {source.title[:60]}")
        print(f"          {source.url}")

asyncio.run(main())
```

### Full Pipeline with Idea Extraction

```python
import asyncio
from nous import discover_news
from nous.infrastructure import (
    IdeaExtractor,
    ExtractionConfig,
    ConsensusDetector,
)

async def full_analysis(topic: str):
    # 1. Discover sources
    print(f"Discovering sources for: {topic}")
    result = await discover_news(topic, max_urls=30)
    print(f"Found {len(result.sources)} sources")
    
    # 2. Extract ideas from each source
    config = ExtractionConfig(provider="ollama/llama3.3")
    extractor = IdeaExtractor(config)
    
    all_ideas = []
    for source in result.sources:
        if source.content_markdown:
            extraction = await extractor.extract(
                source.content_markdown,
                str(source.id),
                topic,
            )
            all_ideas.extend(extraction.ideas)
            print(f"  Extracted {len(extraction.ideas)} ideas from {source.origin}")
    
    # 3. Detect consensus/contention
    detector = ConsensusDetector()
    contents = {str(s.id): s.content_markdown for s in result.sources if s.content_markdown}
    analysis = await detector.analyze(topic, all_ideas, contents)
    
    # 4. Output results
    print(f"\n=== RESULTS ===")
    print(f"Total ideas: {len(all_ideas)}")
    print(f"Consensus ratio: {analysis.consensus_ratio:.1%}")
    print(f"Contention ratio: {analysis.contention_ratio:.1%}")
    
    print(f"\nConsensus clusters ({len(analysis.consensus_clusters)}):")
    for cluster in analysis.consensus_clusters[:3]:
        print(f"  • {cluster.ideas[0].claim[:80]}...")
    
    print(f"\nContention zones ({len(analysis.contention_zones)}):")
    for zone in analysis.contention_zones[:3]:
        print(f"  ⚡ {zone.ideas[0].claim[:80]}...")

asyncio.run(full_analysis("AI regulation EU"))
```

## CLI Usage

```bash
# Search for sources (uses seeded discovery)
nous search "Bitcoin ETF" --results 20

# Full discovery with idea extraction
nous discover "climate policy" --ideas --llm ollama/llama3.3

# Crawl a specific URL
nous crawl https://example.com/article --content

# Output as JSON
nous search "AI safety" --json
```

## API Reference

### Discovery Functions

```python
from nous import (
    # Seeded discovery (RECOMMENDED - no anti-bot issues)
    discover_seeded,    # Full control over domains/config
    discover_news,      # News domains only
    discover_tech,      # Tech news domains only
    discover_academic,  # Academic domains only
    discover_all,       # All domain types
    
    # SERP-based (DEPRECATED - hits Google anti-bot)
    quick_discover,
)

# Examples
result = await discover_news("topic", max_urls=50)
result = await discover_seeded("topic", domains=["reuters.com"], max_urls=100)
```

### Domain Lists

```python
from nous.infrastructure import (
    NEWS_DOMAINS,       # reuters, bbc, nytimes, wsj, bloomberg...
    TECH_NEWS_DOMAINS,  # techcrunch, theverge, wired, arstechnica...
    ACADEMIC_DOMAINS,   # arxiv, semanticscholar, nature, science
    SOCIAL_DOMAINS,     # reddit, news.ycombinator
)
```

### Infrastructure Components

```python
from nous.infrastructure import (
    # Content crawling
    ContentCrawler,
    ProtectedSiteCrawler,  # For Cloudflare/DataDome sites
    AuthenticatedCrawler,  # For auth-required sites
    
    # URL discovery
    UrlSeeder,
    seed_topic,
    
    # Analysis
    ConsensusDetector,
    
    # Extraction
    MetadataExtractor,
    extract_metadata,
    IdeaExtractor,
    ExtractionConfig,
    
    # Archival
    SnapshotCapturer,
    capture_snapshot,
    TemporalArchive,
    
    # Anti-bot
    ProtectionLevel,
    PROFILE_STEALTH,
    PROFILE_UNDETECTED,
)
```

## Expected Output Format

### SeededDiscoveryResult

```python
SeededDiscoveryResult(
    topic="AI regulation EU",
    discovered_at=datetime(2024, 12, 31, ...),
    urls_discovered=150,
    urls_crawled=47,
    urls_failed=3,
    avg_relevance_score=0.62,
    crawl_time_seconds=45.3,
    domains_searched=["reuters.com", "bbc.com", ...],
    sources=[
        SourceNode(
            id=SourceId(...),
            url="https://reuters.com/...",
            title="EU AI Act: What You Need to Know",
            origin="reuters.com",
            source_type=SourceType.NEWS,
            signal_zone=SignalZone.INSTITUTIONAL,
            content_markdown="# EU AI Act...",
            metadata={"relevance_score": 0.85},
        ),
        ...
    ],
)
```

### ConsensusAnalysis

```python
ConsensusAnalysis(
    topic="AI regulation EU",
    consensus_clusters=[
        IdeaCluster(
            cluster_type=ClusterType.CONSENSUS,
            ideas=[IdeaNode(claim="Risk-based approach is correct", ...)],
            avg_similarity=0.82,
            source_ids=[...],
        ),
    ],
    contention_zones=[
        IdeaCluster(
            cluster_type=ClusterType.CONTENTION,
            ideas=[IdeaNode(claim="Will stifle innovation", ...)],
            avg_similarity=0.35,
        ),
    ],
    consensus_ratio=0.65,
    contention_ratio=0.20,
)
```

## Architecture

```
┌─────────────┐     ┌──────────────────┐     ┌─────────────────┐
│   Topic     │────▶│   URL Seeding    │────▶│  Content Crawl  │
│   Input     │     │  (Sitemap + CC)  │     │  (w/ Stealth)   │
└─────────────┘     └──────────────────┘     └─────────────────┘
                           │                         │
                    No browser needed         Browser only for
                    BM25 relevance            protected sites
                                                     │
                                                     ▼
┌─────────────┐     ┌──────────────────┐     ┌─────────────────┐
│  Snapshot   │◀────│    Consensus     │◀────│  Idea Extract   │
│  Output     │     │    Detection     │     │  (LLM-powered)  │
└─────────────┘     └──────────────────┘     └─────────────────┘
```

## Why Seeded Discovery?

| Problem | SERP Approach | Seeded Approach |
|---------|---------------|-----------------|
| Google anti-bot | Frequent blocks | **No Google needed** |
| Browser required | Always | Only for content crawl |
| Discovery speed | ~1 URL/sec | **1000s URLs/sec** |
| Relevance | Position-based | **BM25 semantic** |

## License

MIT License. See `LICENSE` file for details.