"""
Nous Domain Entities

Core domain objects with no external dependencies.
"""

from dataclasses import dataclass, field
from datetime import UTC, datetime
from enum import Enum
from uuid import UUID, uuid4


class SourceType(str, Enum):
    NEWS = "news"
    ACADEMIC = "academic"
    SOCIAL = "social"
    GOVERNMENT = "government"
    BLOG = "blog"
    FORUM = "forum"
    VIDEO = "video"
    UNKNOWN = "unknown"


class SignalZone(str, Enum):
    """Where the source sits in the information ecosystem."""

    INSTITUTIONAL = "institutional"  # NYT, Reuters, .gov
    GRASSROOTS = "grassroots"  # Reddit, Twitter, blogs
    SPECULATIVE = "speculative"  # Crypto Twitter, 4chan


class Stance(str, Enum):
    SUPPORT = "support"
    OPPOSE = "oppose"
    NEUTRAL = "neutral"


@dataclass(frozen=True)
class SourceId:
    """Value object for source identification."""

    value: UUID = field(default_factory=uuid4)

    def __str__(self) -> str:
        return str(self.value)


@dataclass(frozen=True)
class IdeaId:
    """Value object for idea identification."""

    value: UUID = field(default_factory=uuid4)

    def __str__(self) -> str:
        return str(self.value)


@dataclass
class SourceNode:
    """An origin point contributing ideas to the noosphere."""

    id: SourceId
    url: str
    title: str
    source_type: SourceType
    signal_zone: SignalZone
    origin: str  # e.g., "Financial Times", "Reddit/r/technology"
    published_at: datetime | None = None
    crawled_at: datetime = field(default_factory=lambda: datetime.now(UTC))
    content_markdown: str | None = None
    credibility_score: float = 0.5  # 0-1, computed later
    ideas_contributed: list[IdeaId] = field(default_factory=list)
    metadata: dict = field(default_factory=dict)


@dataclass
class IdeaNode:
    """A distinct claim/argument/position extracted from sources."""

    id: IdeaId
    claim: str
    stance_distribution: dict[Stance, float] = field(default_factory=dict)
    source_ids: list[SourceId] = field(default_factory=list)
    decay_rate: float = 0.0  # temporal durability
    behavioral_triggers: list[str] = field(default_factory=list)
    extracted_at: datetime = field(default_factory=lambda: datetime.now(UTC))
    cluster: str | None = None  # "consensus" or "contention"
    metadata: dict = field(default_factory=dict)


@dataclass
class SearchResult:
    """A single result from a search engine."""

    title: str
    url: str
    snippet: str
    position: int
    date: str | None = None
    site_links: list[dict] = field(default_factory=list)


@dataclass
class SearchResponse:
    """Complete response from a search query."""

    query: str
    results: list[SearchResult]
    top_stories: list[dict] = field(default_factory=list)
    related_queries: list[str] = field(default_factory=list)
    searched_at: datetime = field(default_factory=lambda: datetime.now(UTC))
    source: str = "google"  # google, duckduckgo, etc.


# ============================================================================
# Snapshot structures (per architecture.md)
# ============================================================================


@dataclass
class ConsensusCluster:
    """A group of ideas that show agreement across sources."""

    representative_claim: str
    cluster_type: str = "consensus"
    avg_similarity: float = 0.0
    idea_count: int = 0
    source_count: int = 0
    signal_zone_distribution: dict[str, int] = field(default_factory=dict)
    top_sources: list[dict] = field(default_factory=list)
    idea_ids: list[str] = field(default_factory=list)


@dataclass
class ContentionZone:
    """A topic where sources actively disagree."""

    representative_claim: str
    cluster_type: str = "contention"
    avg_similarity: float = 0.0
    idea_count: int = 0
    source_count: int = 0
    opposing_views: dict[str, str] = field(default_factory=dict)  # {pro: "...", con: "..."}
    key_disagreement: str = ""
    idea_ids: list[str] = field(default_factory=list)


@dataclass
class AmplificationWarning:
    """Detection of content being amplified/copied without original analysis."""

    original_url: str
    amplifier_count: int = 0
    similar_titles: list[str] = field(default_factory=list)
    note: str = ""


@dataclass
class SnapshotScope:
    """Scope parameters for a snapshot."""

    time_range: str  # "2024-01-01 to 2024-12-31"
    source_types: list[str] = field(default_factory=list)
    domains_searched: list[str] = field(default_factory=list)
    languages: list[str] = field(default_factory=lambda: ["en"])


@dataclass
class SnapshotStats:
    """Statistics for a snapshot."""

    urls_discovered: int = 0
    urls_crawled: int = 0
    urls_failed: int = 0
    ideas_extracted: int = 0
    avg_relevance_score: float = 0.0
    crawl_time_seconds: float = 0.0


@dataclass
class GraphEdge:
    """An edge in the idea/source graph."""

    source_id: str
    target_id: str
    relationship: str  # supports, contradicts, amplifies, cites
    weight: float = 1.0


@dataclass
class Snapshot:
    """A point-in-time capture of the noosphere on a topic."""

    id: UUID
    topic: str
    generated_at: datetime

    # Scope and stats
    scope: SnapshotScope
    stats: SnapshotStats

    # LLM-generated summary
    summary: str = ""

    # Clustering results
    consensus_clusters: list[ConsensusCluster] = field(default_factory=list)
    contention_zones: list[ContentionZone] = field(default_factory=list)
    amplification_warnings: list[AmplificationWarning] = field(default_factory=list)

    # Raw data
    sources: list[SourceNode] = field(default_factory=list)
    ideas: list[IdeaNode] = field(default_factory=list)

    # Graph structure
    graph_nodes: list[dict] = field(default_factory=list)
    graph_edges: list[GraphEdge] = field(default_factory=list)
