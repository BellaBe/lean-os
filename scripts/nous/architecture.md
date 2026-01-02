# Nous — Noosphere Snapshot Engine

## Complete Architecture & Pipeline Documentation

---

## 1. The Problem

When researching any topic, you face five fundamental challenges:

| Problem | Description |
|---------|-------------|
| **Fragmentation** | Ideas scattered across news, papers, Reddit, Twitter, blogs, forums |
| **Source Opacity** | Unclear which voices are actually shaping the narrative |
| **Temporal Blindness** | No way to capture "what the world thinks now" vs 6 months ago |
| **Bias Invisibility** | Hard to see which perspectives dominate vs are suppressed |
| **Amplification Noise** | Echo chambers create false consensus through repetition |

**Key Insight**: High repetition ≠ genuine consensus. When 50 sources say the same thing, they might be:
- Independently arriving at the same conclusion (real consensus)
- All copying from one original source (amplification)
- Part of a coordinated narrative (manipulation)

Nous distinguishes between these patterns.

---

## 2. The Solution

Nous constructs a **structured, point-in-time snapshot** of how humanity collectively thinks about a subject.

**It is NOT:**
- A search engine (doesn't just find links)
- A summarizer (doesn't just condense text)
- An aggregator (doesn't just collect sources)

**It IS:**
- A **worldview compiler** that maps the ideological landscape
- A **consensus detector** that identifies agreement vs contention
- An **amplification tracker** that distinguishes signal from echo

---

## 3. Core Domain Model

```
Snapshot
├── Topic: "AI regulation EU"
├── Scope
│   ├── time_range: "2024-01-01 to now"
│   ├── source_types: [news, academic, social, government]
│   └── languages: [en, de, fr]
│
├── SourceNodes[]
│   ├── url, title, origin
│   ├── source_type: news | academic | social | government | blog | forum
│   ├── signal_zone: institutional | grassroots | speculative
│   ├── content_markdown
│   └── metadata: {relevance_score, crawled_at, ...}
│
├── IdeaNodes[]
│   ├── claim: "Risk-based AI classification is correct"
│   ├── stance_distribution: {support: 0.72, oppose: 0.15, neutral: 0.13}
│   ├── source_ids: [which sources contribute this idea]
│   ├── cluster: consensus | contention | emerging | fragmented
│   └── confidence: 0.85
│
├── ConsensusClusters[]
│   ├── ideas: [grouped similar ideas]
│   ├── avg_similarity: 0.82
│   └── unique_sources: 47
│
├── ContentionZones[]
│   ├── ideas: [conflicting positions]
│   ├── opposing_pairs: [(idea1, idea2, opposition_score)]
│   └── key_disagreement: "Tech industry vs regulators"
│
└── AmplificationWarnings[]
    ├── original_url
    ├── amplifier_count: 34
    └── similar_titles: ["EU AI Act...", "AI Act..."]
```

### Signal Zones

Sources are classified by their position in the information ecosystem:

| Zone | Examples | Characteristics |
|------|----------|-----------------|
| **Institutional** | Reuters, BBC, Nature, .gov sites | High credibility, editorial standards, slow to publish |
| **Grassroots** | Reddit, blogs, personal sites | Diverse perspectives, fast, variable quality |
| **Speculative** | Crypto Twitter, fringe blogs, 4chan | Early signals, high noise, low verification |

**Why this matters**: Real consensus spans multiple signal zones. If institutional AND grassroots sources agree independently, that's stronger than 100 speculative sources echoing each other.

---

## 4. Complete Pipeline

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           NOUS PIPELINE                                      │
└─────────────────────────────────────────────────────────────────────────────┘

┌──────────────┐    ┌──────────────┐    ┌──────────────┐    ┌──────────────┐
│   STAGE 1    │    │   STAGE 2    │    │   STAGE 3    │    │   STAGE 4    │
│    INPUT     │───▶│  DISCOVERY   │───▶│   CRAWLING   │───▶│  EXTRACTION  │
│              │    │              │    │              │    │              │
│ Topic+Scope  │    │  URL Seeding │    │   Content    │    │  Metadata +  │
│              │    │  Link Graph  │    │   Fetching   │    │    Ideas     │
└──────────────┘    └──────────────┘    └──────────────┘    └──────────────┘
                                                                    │
                                                                    ▼
┌──────────────┐    ┌──────────────┐    ┌──────────────┐    ┌──────────────┐
│   STAGE 7    │    │   STAGE 6    │    │   STAGE 5    │    │   STAGE 4b   │
│   OUTPUT     │◀───│  SNAPSHOT    │◀───│  CONSENSUS   │◀───│  RELATION    │
│              │    │  GENERATION  │    │  DETECTION   │    │   MAPPING    │
│   Artifact   │    │   Assembly   │    │  Clustering  │    │  Idea Graph  │
└──────────────┘    └──────────────┘    └──────────────┘    └──────────────┘
```

---

## 5. Pipeline Stages in Detail

### Stage 1: Topic Input

**Input**: User provides topic + optional scope constraints

```python
from nous import discover_news

result = await discover_news(
    "AI regulation EU",      # Topic
    max_urls=100,            # Scope: how many sources
)

# Or with full control:
from nous import discover_seeded, SeededDiscoveryConfig

config = SeededDiscoveryConfig(
    domains=["reuters.com", "bbc.com", "nature.com"],
    max_urls_per_domain=50,
    min_relevance_score=0.4,
    use_sitemap=True,
    use_common_crawl=True,
)
result = await discover_seeded("AI regulation EU", config=config)
```

**What happens**:
- Topic is parsed and prepared for BM25 relevance scoring
- Scope constraints are applied to filter discovery

---

### Stage 2: Source Discovery

**Goal**: Find every relevant source discussing this topic WITHOUT hitting Google's anti-bot measures.

**Method**: URL Seeding (not SERP crawling)

```
┌─────────────────────────────────────────────────────────────────┐
│                    URL SEEDING PROCESS                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────┐     ┌─────────────┐     ┌─────────────┐       │
│  │  Sitemap    │     │   Common    │     │    BM25     │       │
│  │  Fetching   │────▶│   Crawl     │────▶│   Scoring   │       │
│  │             │     │   Index     │     │             │       │
│  └─────────────┘     └─────────────┘     └─────────────┘       │
│        │                   │                   │                │
│        └───────────────────┴───────────────────┘                │
│                            │                                    │
│                            ▼                                    │
│                   ┌─────────────────┐                          │
│                   │  Ranked URLs    │                          │
│                   │  by Relevance   │                          │
│                   └─────────────────┘                          │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

**How it works**:

1. **Sitemap Discovery**
   - Fetches sitemap.xml from curated domains
   - Extracts all URLs (thousands per domain)
   - No browser needed, instant

2. **Common Crawl Index**
   - Queries Common Crawl's index for domain URLs
   - Access to historical crawl data
   - Finds URLs not in sitemap

3. **BM25 Relevance Scoring**
   - Scores each URL against the topic
   - Uses title, description, URL path
   - Filters by threshold (default 0.3)

**Code Path**:
```python
# infrastructure/crawlers/url_seeder.py
class UrlSeeder:
    async def discover(domain, topic, config) -> list[SeededUrl]
    
# Each SeededUrl contains:
SeededUrl(
    url="https://reuters.com/technology/ai-regulation-eu-2024",
    relevance_score=0.85,      # BM25 score
    title="EU AI Act: What You Need to Know",
    description="The European Union's landmark AI regulation...",
    status="valid",
)
```

**Pre-defined Domain Lists**:
```python
NEWS_DOMAINS = ["reuters.com", "bbc.com", "nytimes.com", "wsj.com", ...]
TECH_NEWS_DOMAINS = ["techcrunch.com", "theverge.com", "wired.com", ...]
ACADEMIC_DOMAINS = ["arxiv.org", "nature.com", "science.org", ...]
SOCIAL_DOMAINS = ["reddit.com", "news.ycombinator.com"]
```

**Why this beats SERP crawling**:

| Aspect | SERP Crawling | URL Seeding |
|--------|---------------|-------------|
| Speed | ~1 URL/second | 1000s URLs/second |
| Anti-bot | Frequent blocks | None |
| Browser needed | Always | Never |
| Relevance | Position-based | BM25 semantic |
| Coverage | Limited to top results | Full sitemap |

---

### Stage 3: Content Crawling

**Goal**: Fetch content from discovered URLs, handling protection as needed.

```
┌─────────────────────────────────────────────────────────────────┐
│                  CONTENT CRAWLING FLOW                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  URLs ───▶ ┌─────────────────┐                                 │
│            │ Protection      │                                 │
│            │ Detection       │                                 │
│            └────────┬────────┘                                 │
│                     │                                          │
│         ┌──────────┴──────────┐                               │
│         ▼                     ▼                                │
│  ┌─────────────┐      ┌─────────────┐                         │
│  │   Regular   │      │  Protected  │                         │
│  │   Crawler   │      │   Crawler   │                         │
│  │             │      │  (Stealth)  │                         │
│  └──────┬──────┘      └──────┬──────┘                         │
│         │                    │                                 │
│         └────────┬───────────┘                                 │
│                  ▼                                             │
│         ┌─────────────────┐                                   │
│         │ HTML → Markdown │                                   │
│         │   Conversion    │                                   │
│         └─────────────────┘                                   │
│                                                                │
└─────────────────────────────────────────────────────────────────┘
```

**Protection Levels**:

| Level | Method | Use Case |
|-------|--------|----------|
| `NONE` | Regular browser | Unprotected sites |
| `BASIC` | Stealth mode (playwright-stealth) | Simple checks |
| `ADVANCED` | Undetected browser | Cloudflare, DataDome |
| `MAXIMUM` | All + slow_mo + viewport randomization | Maximum evasion |

**Auto-detection by domain**:
```python
# Known protected sites get automatic stealth
get_profile_for_site("medium.com")     # → PROFILE_UNDETECTED
get_profile_for_site("nytimes.com")    # → PROFILE_STEALTH
get_profile_for_site("example.com")    # → PROFILE_BASIC
```

**Code Path**:
```python
# infrastructure/crawlers/content_crawler.py
class ContentCrawler:
    async def crawl(url) -> CrawlResult
    async def crawl_many(urls, max_concurrent=5) -> list[CrawlResult]

# infrastructure/crawlers/browser_config.py
class ProtectedSiteCrawler:
    # For Cloudflare/DataDome protected sites
    async def crawl(url, wait_for=None, delay=0.5) -> CrawlResult

# CrawlResult contains:
CrawlResult(
    url="...",
    success=True,
    html="<html>...",
    markdown="# Article Title\n\nContent...",
    title="Article Title",
    metadata={...},
)
```

**Session Persistence** (for auth-required sites):
```python
# Save session after manual login
manager = SessionManager(Path("~/.nous/sessions"))
manager.create_manual_session("nytimes", cookies=[...])

# Reuse session
async with AuthenticatedCrawler("nytimes") as crawler:
    result = await crawler.crawl("https://nytimes.com/premium-article")
```

---

### Stage 4: Extraction

**Goal**: Extract structured data from raw content.

#### 4a: Metadata Extraction (Fast, No LLM)

```python
# infrastructure/extraction/metadata_extractor.py
from nous.infrastructure import extract_metadata, MetadataPatterns

metadata = extract_metadata(
    content=article_markdown,
    url="https://example.com/article",
    patterns=MetadataPatterns.ALL,
)

# Returns:
ExtractedMetadata(
    dates=["January 15, 2024", "2024-01-15"],
    authors=["John Smith", "Jane Doe"],
    emails=["contact@example.com"],
    urls=["https://cited-source.com/paper"],
    citations=["[1]", "[2]", "(Smith, 2023)"],
    twitter_handles=["@AINewsDaily"],
    hashtags=["#AIRegulation", "#EUAIAct"],
    percentages=["72%", "15%"],
    currencies=["$1.5 billion", "€2 million"],
    quotes=["This is a direct quote from the article"],
)
```

**Pattern Categories**:
- `DATES` — ISO dates, US dates, written dates
- `ATTRIBUTION` — Authors, emails, citations
- `SOCIAL` — Twitter handles, hashtags
- `NUMERIC` — Percentages, currencies
- `ALL` — Everything

**Why no LLM**: Regex extraction is instant and free. Use it for structured metadata, save LLM for semantic tasks.

#### 4b: Idea Extraction (LLM-Powered)

```python
# infrastructure/extraction/idea_extractor.py
from nous.infrastructure import IdeaExtractor, ExtractionConfig

config = ExtractionConfig(
    provider="ollama/llama3.3",        # or "openai/gpt-4"
    chunk_token_threshold=2000,        # Split long articles
    overlap_rate=0.1,                  # Context preservation
    max_claims_per_source=10,
)

extractor = IdeaExtractor(config)
result = await extractor.extract(
    content=article_markdown,
    source_id="source_123",
    topic="AI regulation EU",
)

# Returns:
ExtractionResult(
    source_id="source_123",
    ideas=[
        IdeaNode(
            claim="Risk-based AI classification is the correct regulatory approach",
            stance_distribution={Stance.SUPPORT: 0.72, Stance.OPPOSE: 0.15, Stance.NEUTRAL: 0.13},
            confidence=0.85,
            evidence=["EU AI Act Article 6", "OECD guidelines"],
            context="The article argues that...",
        ),
        IdeaNode(
            claim="Foundation model obligations are too restrictive",
            stance_distribution={Stance.SUPPORT: 0.41, Stance.OPPOSE: 0.48, Stance.NEUTRAL: 0.11},
            confidence=0.72,
            evidence=["OpenAI statement", "Industry coalition letter"],
        ),
    ],
    summary="The article discusses EU AI Act implementation...",
    sentiment="cautiously optimistic",
    chunks_processed=3,
    tokens_used=4500,
    extraction_time_ms=2340,
)
```

**Chunking Strategies** (for long articles):
```python
ChunkingStrategy.fixed_length(content, chunk_size=2000)
ChunkingStrategy.sliding_window(content, window_size=2000, step=1800)
ChunkingStrategy.sentence_based(content, sentences_per_chunk=20)
ChunkingStrategy.by_paragraphs(content, paragraphs_per_chunk=5)
```

---

### Stage 5: Relation Mapping

**Goal**: Build graph structure showing how ideas relate.

#### Link Analysis (Citation Tracking)

```python
# infrastructure/crawlers/link_analyzer.py
from nous.infrastructure import LinkAnalyzer

async with LinkAnalyzer() as analyzer:
    result = await analyzer.analyze(
        url="https://reuters.com/ai-article",
        topic="AI regulation",
        max_links=50,
        score_threshold=0.5,
    )
    
# Returns:
LinkAnalysisResult(
    source_url="https://reuters.com/ai-article",
    internal_links=[...],         # Links within same domain
    external_links=[              # Citations to other sources
        DiscoveredLink(
            url="https://eu.commission.eu/ai-act",
            text="EU AI Act",
            page_title="Artificial Intelligence Act",
            score=LinkScore(
                intrinsic=8.5,    # URL quality (0-10)
                contextual=0.92,  # BM25 relevance (0-1)
                total=0.89,       # Combined
            ),
        ),
    ],
    link_count=47,
    external_link_count=23,
    avg_relevance_score=0.67,
)

# Find high-value citations
citations = analyzer.find_high_value_citations(result, min_score=0.7)

# Detect amplification patterns
amplified = analyzer.detect_amplification_candidates(
    analyses=[result1, result2, result3],
    similarity_threshold=0.8,  # Group similar titles
)
# Returns: [("https://original-source.com", ["amplifier1", "amplifier2", ...])]
```

**Amplification Detection**:
- Groups URLs referenced by multiple sources (exact match)
- Groups similar page titles across sources (fuzzy match via Jaccard)
- Identifies potential echo chambers vs genuine multi-source consensus

---

### Stage 6: Consensus Detection

**Goal**: Cluster ideas to identify consensus vs contention.

```
┌─────────────────────────────────────────────────────────────────┐
│                 CONSENSUS DETECTION FLOW                        │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Ideas ───▶ ┌─────────────────┐                                │
│             │  TF-IDF + Topic │                                │
│             │   Vectorization │                                │
│             └────────┬────────┘                                │
│                      │                                         │
│                      ▼                                         │
│             ┌─────────────────┐                                │
│             │ Cosine          │                                │
│             │ Similarity      │                                │
│             │ Matrix          │                                │
│             └────────┬────────┘                                │
│                      │                                         │
│                      ▼                                         │
│             ┌─────────────────┐                                │
│             │ Agglomerative   │                                │
│             │ Clustering      │                                │
│             └────────┬────────┘                                │
│                      │                                         │
│         ┌───────────┼───────────┐                             │
│         ▼           ▼           ▼                              │
│  ┌───────────┐ ┌───────────┐ ┌───────────┐                    │
│  │ CONSENSUS │ │CONTENTION │ │ EMERGING  │                    │
│  │ sim > 0.7 │ │ sim < 0.4 │ │ few srcs  │                    │
│  └───────────┘ └───────────┘ └───────────┘                    │
│                                                                │
└─────────────────────────────────────────────────────────────────┘
```

```python
# infrastructure/analysis/consensus_detector.py
from nous.infrastructure import ConsensusDetector

detector = ConsensusDetector(
    consensus_threshold=0.7,    # Similarity above this = consensus
    contention_threshold=0.4,   # Similarity below this = contention
    min_cluster_size=2,
)

# Prepare source contents for context-aware clustering
source_contents = {
    source.id: source.content_markdown 
    for source in sources 
    if source.content_markdown
}

analysis = await detector.analyze(
    topic="AI regulation EU",
    ideas=all_extracted_ideas,
    source_contents=source_contents,  # Used for context enrichment
)

# Returns:
ConsensusAnalysis(
    topic="AI regulation EU",
    total_ideas=47,
    total_sources=23,
    
    consensus_clusters=[
        IdeaCluster(
            cluster_type=ClusterType.CONSENSUS,
            ideas=[idea1, idea2, idea3],  # Similar ideas grouped
            avg_similarity=0.82,
            min_similarity=0.75,
            max_similarity=0.91,
            unique_sources=12,            # Different sources agree
            representative_claim="Risk-based classification is correct",
        ),
    ],
    
    contention_zones=[
        IdeaCluster(
            cluster_type=ClusterType.CONTENTION,
            ideas=[idea_pro, idea_con],
            avg_similarity=0.31,          # Low = disagreement
            unique_sources=8,
        ),
    ],
    
    emerging_ideas=[...],  # Too few sources to classify
    
    consensus_ratio=0.65,   # 65% of ideas in consensus
    contention_ratio=0.20,  # 20% of ideas contested
)
```

**How Clustering Works**:

1. **Topic-Boosted Vectorization**:
   ```python
   # Prepend topic to each claim for better matching
   enriched_claim = f"{topic} {claim} {source_context[:200]}"
   ```

2. **TF-IDF with Bigrams**:
   ```python
   vectorizer = TfidfVectorizer(ngram_range=(1, 2))  # Captures "AI regulation" as phrase
   ```

3. **Cosine Similarity Matrix**:
   - Compare every idea to every other idea
   - Similarity 0.0 = completely different
   - Similarity 1.0 = identical

4. **Agglomerative Clustering**:
   - Groups similar ideas together
   - Calculates intra-cluster similarity

5. **Classification**:
   - `avg_similarity > 0.7` → **CONSENSUS**
   - `avg_similarity < 0.4` → **CONTENTION**
   - `cluster_size < min_size` → **EMERGING**
   - Otherwise → **FRAGMENTED**

**Contention Analysis**:
```python
from nous.infrastructure import ContentionAnalyzer

analyzer = ContentionAnalyzer()
opposing_pairs = analyzer.find_opposing_pairs(contention_zone)

# Returns pairs of directly opposing ideas:
[
    (idea1, idea2, 0.85),  # 85% opposition strength
    (idea3, idea4, 0.72),
]
```

---

### Stage 7: Snapshot Generation

**Goal**: Produce structured artifact capturing the ideological landscape.

```yaml
snapshot:
  id: "550e8400-e29b-41d4-a716-446655440000"
  topic: "AI regulation in the EU"
  generated_at: "2024-12-31T14:30:00Z"
  
  scope:
    time_range: "2024-01-01 to 2024-12-31"
    source_types: [news, academic, social, government]
    domains_searched: [reuters.com, bbc.com, nature.com, ...]
    languages: [en]
  
  stats:
    urls_discovered: 847
    urls_crawled: 312
    urls_failed: 23
    ideas_extracted: 156
    avg_relevance_score: 0.67
    crawl_time_seconds: 245
  
  summary: |
    The EU AI Act dominates discourse, with strong consensus on 
    risk-based classification but significant contention around 
    foundation model obligations and innovation impact.
    
    Key finding: 65% of ideas show consensus across sources,
    while 20% are actively contested between industry and regulators.

  consensus_clusters:
    - representative_claim: "Risk-based AI classification is the correct approach"
      cluster_type: consensus
      avg_similarity: 0.82
      idea_count: 12
      source_count: 47
      signal_zone_distribution:
        institutional: 31
        grassroots: 12
        speculative: 4
      top_sources:
        - origin: "Financial Times"
          url: "https://ft.com/..."
          credibility_score: 0.89
        - origin: "Nature"
          url: "https://nature.com/..."
          credibility_score: 0.95

  contention_zones:
    - representative_claim: "AI Act will stifle European innovation"
      cluster_type: contention
      avg_similarity: 0.31
      idea_count: 8
      source_count: 23
      opposing_views:
        pro: "Innovation requires regulatory clarity"
        con: "Compliance costs will drive startups away"
      key_disagreement: "Tech industry vs EU regulators"

  amplification_warnings:
    - original_url: "https://ec.europa.eu/ai-act-press-release"
      amplifier_count: 34
      note: "Many sources quoted press release without original analysis"
    - similar_titles_group: "EU AI Act: What You Need to Know"
      source_count: 12
      note: "Near-identical headlines suggest coordinated coverage"

  sources:
    - id: "source_012"
      url: "https://ft.com/content/..."
      title: "EU AI Act: The Business Impact"
      origin: "Financial Times"
      source_type: news
      signal_zone: institutional
      relevance_score: 0.89
      ideas_contributed: ["idea_001", "idea_005", "idea_012"]
      
  ideas:
    - id: "idea_001"
      claim: "Risk-based AI classification is the correct regulatory approach"
      stance_distribution:
        support: 0.72
        oppose: 0.15
        neutral: 0.13
      cluster: consensus
      confidence: 0.85
      source_ids: ["source_012", "source_045", "source_078"]
      evidence:
        - "EU AI Act Article 6"
        - "OECD AI Principles"

  graph:
    nodes: [...]  # Full node data for visualization
    edges: [...]  # Relationships: supports, contradicts, amplifies
```

---

## 6. Temporal Diff (Archival)

Nous supports capturing snapshots for later comparison:

```python
from nous.infrastructure import TemporalArchive, capture_snapshot

# One-time capture
snapshot = await capture_snapshot(
    url="https://reuters.com/ai-article",
    output_dir=Path("./archives"),
    formats=["screenshot", "mhtml", "pdf"],
)

# Managed archive with diff detection
archive = TemporalArchive(Path("./archives/ai_regulation"))

# Capture today
await archive.capture_snapshot("https://key-source.com/article")

# Later, compare
comparison = await archive.capture_and_compare("https://key-source.com/article")

if comparison.content_changed:
    print(f"Content changed! Delta: {comparison.time_delta_seconds}s")
    # Analyze what changed...
```

**Capture Formats**:
- **Screenshot (PNG)** — Visual record of page appearance
- **PDF** — Printable document format
- **MHTML** — Complete page with all resources (CSS, images, scripts)
- **HTML** — Raw HTML with content hash for diff detection

---

## 7. Complete Usage Example

```python
import asyncio
from pathlib import Path
from nous import discover_news
from nous.infrastructure import (
    IdeaExtractor,
    ExtractionConfig,
    ConsensusDetector,
    extract_metadata,
    MetadataPatterns,
)

async def analyze_topic(topic: str):
    print(f"═══════════════════════════════════════")
    print(f"  NOUS: Analyzing '{topic}'")
    print(f"═══════════════════════════════════════\n")
    
    # ─────────────────────────────────────────
    # STAGE 1-3: Discovery + Crawling
    # ─────────────────────────────────────────
    print("[1/4] Discovering and crawling sources...")
    result = await discover_news(topic, max_urls=50)
    
    print(f"      URLs discovered: {result.urls_discovered}")
    print(f"      URLs crawled:    {result.urls_crawled}")
    print(f"      URLs failed:     {result.urls_failed}")
    print(f"      Avg relevance:   {result.avg_relevance_score:.2f}")
    print()
    
    # ─────────────────────────────────────────
    # STAGE 4a: Fast Metadata Extraction
    # ─────────────────────────────────────────
    print("[2/4] Extracting metadata...")
    for source in result.sources[:3]:
        if source.content_markdown:
            meta = extract_metadata(
                source.content_markdown, 
                source.url,
                MetadataPatterns.DATES | MetadataPatterns.ATTRIBUTION,
            )
            print(f"      {source.origin}: {len(meta.dates)} dates, {len(meta.authors)} authors")
    print()
    
    # ─────────────────────────────────────────
    # STAGE 4b: LLM Idea Extraction
    # ─────────────────────────────────────────
    print("[3/4] Extracting ideas (LLM)...")
    config = ExtractionConfig(provider="ollama/llama3.3")
    extractor = IdeaExtractor(config)
    
    all_ideas = []
    source_contents = {}
    
    for source in result.sources:
        if source.content_markdown:
            source_contents[source.id] = source.content_markdown
            try:
                extraction = await extractor.extract(
                    source.content_markdown,
                    str(source.id),
                    topic,
                )
                all_ideas.extend(extraction.ideas)
                print(f"      {source.origin}: {len(extraction.ideas)} ideas")
            except Exception as e:
                print(f"      {source.origin}: Failed - {e}")
    
    print(f"      Total ideas: {len(all_ideas)}")
    print()
    
    # ─────────────────────────────────────────
    # STAGE 5-6: Consensus Detection
    # ─────────────────────────────────────────
    print("[4/4] Detecting consensus/contention...")
    detector = ConsensusDetector()
    analysis = await detector.analyze(topic, all_ideas, source_contents)
    
    # ─────────────────────────────────────────
    # STAGE 7: Output
    # ─────────────────────────────────────────
    print()
    print(f"═══════════════════════════════════════")
    print(f"  RESULTS")
    print(f"═══════════════════════════════════════")
    print(f"  Topic:            {topic}")
    print(f"  Sources analyzed: {len(result.sources)}")
    print(f"  Ideas extracted:  {len(all_ideas)}")
    print(f"  Consensus ratio:  {analysis.consensus_ratio:.1%}")
    print(f"  Contention ratio: {analysis.contention_ratio:.1%}")
    print()
    
    if analysis.consensus_clusters:
        print(f"  CONSENSUS ({len(analysis.consensus_clusters)} clusters):")
        for cluster in analysis.consensus_clusters[:3]:
            print(f"    ✓ {cluster.representative_claim[:70]}...")
            print(f"      Similarity: {cluster.avg_similarity:.2f} | Sources: {cluster.unique_sources}")
        print()
    
    if analysis.contention_zones:
        print(f"  CONTENTION ({len(analysis.contention_zones)} zones):")
        for zone in analysis.contention_zones[:3]:
            print(f"    ⚡ {zone.representative_claim[:70]}...")
            print(f"      Similarity: {zone.avg_similarity:.2f} | Sources: {zone.unique_sources}")
        print()
    
    return analysis

# Run it
if __name__ == "__main__":
    asyncio.run(analyze_topic("AI regulation EU"))
```

**Expected Output**:
```
═══════════════════════════════════════
  NOUS: Analyzing 'AI regulation EU'
═══════════════════════════════════════

[1/4] Discovering and crawling sources...
      URLs discovered: 847
      URLs crawled:    312
      URLs failed:     23
      Avg relevance:   0.67

[2/4] Extracting metadata...
      reuters.com: 3 dates, 2 authors
      bbc.com: 2 dates, 1 authors
      ft.com: 4 dates, 3 authors

[3/4] Extracting ideas (LLM)...
      reuters.com: 5 ideas
      bbc.com: 3 ideas
      ft.com: 7 ideas
      Total ideas: 156

[4/4] Detecting consensus/contention...

═══════════════════════════════════════
  RESULTS
═══════════════════════════════════════
  Topic:            AI regulation EU
  Sources analyzed: 312
  Ideas extracted:  156
  Consensus ratio:  65.0%
  Contention ratio: 20.0%

  CONSENSUS (4 clusters):
    ✓ Risk-based AI classification is the correct regulatory approach...
      Similarity: 0.82 | Sources: 47
    ✓ Transparency requirements for AI systems are necessary...
      Similarity: 0.78 | Sources: 31
    ✓ The EU is leading global AI governance efforts...
      Similarity: 0.75 | Sources: 28

  CONTENTION (2 zones):
    ⚡ AI Act will stifle European innovation compared to US/China...
      Similarity: 0.31 | Sources: 23
    ⚡ Foundation model obligations are appropriately balanced...
      Similarity: 0.35 | Sources: 18
```

---

## 8. Architecture Summary

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                              NOUS ARCHITECTURE                               │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                           INTERFACE LAYER                            │   │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────────────┐  │   │
│  │  │    CLI      │  │  Python API │  │  (Future) FastAPI REST      │  │   │
│  │  └─────────────┘  └─────────────┘  └─────────────────────────────┘  │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                    │                                        │
│                                    ▼                                        │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                         APPLICATION LAYER                            │   │
│  │  ┌───────────────────────────┐  ┌───────────────────────────────┐   │   │
│  │  │    SnapshotBuilder        │  │    SeededDiscovery            │   │   │
│  │  │    (Full Pipeline)        │  │    (Search API Discovery)     │   │   │
│  │  └───────────────────────────┘  └───────────────────────────────┘   │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                    │                                        │
│                                    ▼                                        │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                       INFRASTRUCTURE LAYER                           │   │
│  │                                                                      │   │
│  │  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐     │   │
│  │  │    CRAWLERS     │  │    EXTRACTION   │  │    ANALYSIS     │     │   │
│  │  ├─────────────────┤  ├─────────────────┤  ├─────────────────┤     │   │
│  │  │ UrlSeeder       │  │ MetadataExtract │  │ ConsensusDetect │     │   │
│  │  │ ContentCrawler  │  │ IdeaExtractor   │  │ ContentionAnalyz│     │   │
│  │  │ LinkAnalyzer    │  │ ChunkingStrategy│  │                 │     │   │
│  │  │ ProtectedCrawler│  │                 │  │                 │     │   │
│  │  │ SessionManager  │  │                 │  │                 │     │   │
│  │  │ SnapshotCapture │  │                 │  │                 │     │   │
│  │  └─────────────────┘  └─────────────────┘  └─────────────────┘     │   │
│  │                                                                      │   │
│  │  ┌─────────────────┐                                                │   │
│  │  │      LLM        │                                                │   │
│  │  ├─────────────────┤                                                │   │
│  │  │ DirectLLMClient │  ◄── LiteLLM (ollama, openai, anthropic, ...) │   │
│  │  │ SchemaGenerator │                                                │   │
│  │  └─────────────────┘                                                │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                    │                                        │
│                                    ▼                                        │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                           DOMAIN LAYER                               │   │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  ┌───────────┐  │   │
│  │  │ SourceNode  │  │  IdeaNode   │  │ SignalZone  │  │  Stance   │  │   │
│  │  │ SourceType  │  │  IdeaCluster│  │ ClusterType │  │           │  │   │
│  │  └─────────────┘  └─────────────┘  └─────────────┘  └───────────┘  │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 9. Key Differentiators

| Aspect | Traditional Search | Nous |
|--------|-------------------|------|
| **Output** | Links | Structured knowledge graph |
| **Analysis** | Popularity-based ranking | Consensus vs contention mapping |
| **Temporal** | Point-in-time only | Diff-capable archives |
| **Sources** | Treats all equal | Signal zone classification |
| **Amplification** | Counts as authority | Detects as potential echo |
| **Discovery** | SERP (anti-bot issues) | Sitemap seeding (reliable) |

**Core Innovation**: Nous doesn't just find information—it maps the *shape* of collective thought, distinguishing genuine consensus from coordinated amplification.