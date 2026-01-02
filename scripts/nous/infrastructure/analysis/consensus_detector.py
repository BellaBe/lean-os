"""
Consensus and Contention Detection

Uses Crawl4AI's CosineStrategy for similarity-based clustering to identify:
- Consensus Clusters: High agreement across sources
- Contention Zones: Conflicting positions across sources

This maps directly to our domain model's core concepts.

Enhanced with:
- Zone distribution tracking
- Origin diversity metrics (Shannon entropy)
- Amplification score for echo chamber detection
"""

import math
from dataclasses import dataclass, field
from datetime import datetime
from enum import Enum

from ...domain import IdeaNode, SignalZone, SourceId, Stance


class ClusterType(str, Enum):
    """Type of idea cluster based on similarity analysis."""

    CONSENSUS = "consensus"  # High agreement (sim > 0.7)
    CONTENTION = "contention"  # Conflicting positions (sim < 0.4)
    EMERGING = "emerging"  # Few sources, unclear consensus
    FRAGMENTED = "fragmented"  # Many varied positions


@dataclass
class IdeaCluster:
    """A cluster of related ideas with consensus metrics."""

    cluster_id: str
    cluster_type: ClusterType
    ideas: list[IdeaNode]

    # Similarity metrics
    avg_similarity: float = 0.0
    min_similarity: float = 0.0
    max_similarity: float = 0.0

    # Source diversity
    unique_sources: int = 0
    signal_zone_distribution: dict = field(default_factory=dict)

    # Enhanced zone tracking (from Crawl4AI upgrade)
    zone_distribution: dict[SignalZone, int] = field(default_factory=dict)
    origin_diversity: float = 0.0  # Shannon entropy of zone distribution
    amplification_score: float = 0.0  # Echo chamber detection
    potential_origin_urls: list[str] = field(default_factory=list)

    # Representative claim (highest scoring idea)
    representative_claim: str | None = None

    analyzed_at: datetime = field(default_factory=datetime.utcnow)

    @property
    def is_echo_chamber(self) -> bool:
        """Check if cluster shows echo chamber characteristics."""
        # Low diversity + high amplification = echo chamber
        return self.origin_diversity < 0.5 and self.amplification_score > 0.7

    @property
    def is_diverse(self) -> bool:
        """Check if cluster has diverse origins."""
        return self.origin_diversity > 0.8


@dataclass
class ConsensusAnalysis:
    """Result of consensus/contention analysis on a topic."""

    topic: str
    total_ideas: int
    total_sources: int

    consensus_clusters: list[IdeaCluster]
    contention_zones: list[IdeaCluster]
    emerging_ideas: list[IdeaCluster]

    # Overall metrics
    consensus_ratio: float = 0.0  # % of ideas in consensus
    contention_ratio: float = 0.0  # % of ideas in contention

    analyzed_at: datetime = field(default_factory=datetime.utcnow)


class ConsensusDetector:
    """
    Detects consensus and contention patterns in extracted ideas.

    Uses Crawl4AI's CosineStrategy for semantic clustering, then
    classifies clusters based on similarity thresholds.
    """

    def __init__(
        self,
        consensus_threshold: float = 0.7,
        contention_threshold: float = 0.4,
        min_cluster_size: int = 2,
        min_consensus_sources: int = 2,  # Require 2+ sources for true consensus
        model_name: str = "sentence-transformers/all-MiniLM-L6-v2",
    ):
        """
        Args:
            consensus_threshold: Similarity above this = consensus
            contention_threshold: Similarity below this = contention
            min_cluster_size: Minimum ideas to form a cluster
            min_consensus_sources: Minimum unique sources for consensus (prevents single-source "consensus")
            model_name: Sentence transformer model for embeddings
        """
        self.consensus_threshold = consensus_threshold
        self.contention_threshold = contention_threshold
        self.min_cluster_size = min_cluster_size
        self.min_consensus_sources = min_consensus_sources
        self.model_name = model_name
        self._strategy = None

    def _get_strategy(self, topic: str):
        """Lazy initialization of CosineStrategy."""
        if self._strategy is None:
            try:
                from crawl4ai import CosineStrategy

                self._strategy = CosineStrategy(
                    semantic_filter=topic,
                    word_count_threshold=10,
                    sim_threshold=0.3,  # Low threshold to capture all clusters
                    top_k=50,  # Get many clusters for analysis
                    model_name=self.model_name,
                    verbose=False,
                )
            except ImportError:
                raise ImportError("crawl4ai not installed. Run: pip install crawl4ai")
        return self._strategy

    async def analyze(
        self,
        topic: str,
        ideas: list[IdeaNode],
        source_contents: dict[SourceId, str],
    ) -> ConsensusAnalysis:
        """
        Analyze ideas for consensus and contention patterns.

        Args:
            topic: The topic being analyzed
            ideas: List of extracted IdeaNode objects
            source_contents: Map of source_id -> content for context-aware clustering

        Returns:
            ConsensusAnalysis with classified clusters
        """
        if not ideas:
            return ConsensusAnalysis(
                topic=topic,
                total_ideas=0,
                total_sources=0,
                consensus_clusters=[],
                contention_zones=[],
                emerging_ideas=[],
            )

        # Build text corpus from idea claims
        claim_texts = [idea.claim for idea in ideas]

        # Build context map: idea index -> source content excerpt
        idea_contexts = {}
        for idx, idea in enumerate(ideas):
            context_parts = []
            for source_id in idea.source_ids:
                if source_id in source_contents:
                    # Get excerpt around the claim (first 500 chars as context)
                    content = source_contents[source_id]
                    context_parts.append(content[:500] if content else "")
            idea_contexts[idx] = " ".join(context_parts)

        # Use internal clustering (sklearn-based) with topic and context
        clusters = self._cluster_claims(claim_texts, topic, idea_contexts)

        # Classify clusters
        consensus_clusters = []
        contention_zones = []
        emerging_ideas = []

        for cluster_id, cluster_data in clusters.items():
            idea_cluster = self._build_cluster(
                cluster_id=cluster_id,
                cluster_data=cluster_data,
                ideas=ideas,
            )

            if idea_cluster.cluster_type == ClusterType.CONSENSUS:
                consensus_clusters.append(idea_cluster)
            elif idea_cluster.cluster_type == ClusterType.CONTENTION:
                contention_zones.append(idea_cluster)
            else:
                emerging_ideas.append(idea_cluster)

        # Calculate ratios
        total = len(ideas)
        consensus_count = sum(len(c.ideas) for c in consensus_clusters)
        contention_count = sum(len(c.ideas) for c in contention_zones)

        return ConsensusAnalysis(
            topic=topic,
            total_ideas=total,
            total_sources=len(set(sid for idea in ideas for sid in idea.source_ids)),
            consensus_clusters=consensus_clusters,
            contention_zones=contention_zones,
            emerging_ideas=emerging_ideas,
            consensus_ratio=consensus_count / total if total > 0 else 0.0,
            contention_ratio=contention_count / total if total > 0 else 0.0,
        )

    def _cluster_claims(
        self,
        claims: list[str],
        topic: str,
        idea_contexts: dict[int, str] | None = None,
    ) -> dict[str, dict]:
        """
        Cluster claims using TF-IDF and cosine similarity.

        Args:
            claims: List of claim texts to cluster
            topic: Topic for vocabulary boosting
            idea_contexts: Optional map of claim index -> source context for enrichment

        Falls back to sklearn if CosineStrategy unavailable.
        """
        try:
            import numpy as np
            from sklearn.cluster import AgglomerativeClustering
            from sklearn.feature_extraction.text import TfidfVectorizer
            from sklearn.metrics.pairwise import cosine_similarity
        except ImportError:
            raise ImportError("sklearn required. Run: pip install scikit-learn")

        if len(claims) < 2:
            return {"0": {"indices": list(range(len(claims))), "similarities": [1.0]}}

        # Enrich claims with context if available
        enriched_claims = []
        for idx, claim in enumerate(claims):
            if idea_contexts and idx in idea_contexts and idea_contexts[idx]:
                # Combine claim with context excerpt for better semantic matching
                enriched_claims.append(f"{claim} {idea_contexts[idx][:200]}")
            else:
                enriched_claims.append(claim)

        # Add topic terms to boost relevance (prepend to each claim)
        topic_boosted_claims = [f"{topic} {claim}" for claim in enriched_claims]

        # Vectorize claims with topic-aware vocabulary
        vectorizer = TfidfVectorizer(
            stop_words="english",
            max_features=1000,
            ngram_range=(1, 2),  # Include bigrams for better topic matching
        )
        tfidf_matrix = vectorizer.fit_transform(topic_boosted_claims)

        # Compute similarity matrix
        sim_matrix = cosine_similarity(tfidf_matrix)

        # Convert to distance matrix for clustering
        distance_matrix = 1 - sim_matrix
        np.fill_diagonal(distance_matrix, 0)

        # Cluster using agglomerative clustering
        n_clusters = min(len(claims) // 2 + 1, 10)  # Reasonable cluster count
        clustering = AgglomerativeClustering(
            n_clusters=n_clusters,
            metric="precomputed",
            linkage="average",
        )
        labels = clustering.fit_predict(distance_matrix)

        # Group by cluster
        clusters = {}
        for idx, label in enumerate(labels):
            cluster_id = str(label)
            if cluster_id not in clusters:
                clusters[cluster_id] = {"indices": [], "similarities": []}
            clusters[cluster_id]["indices"].append(idx)

        # Calculate intra-cluster similarities
        for cluster_id, data in clusters.items():
            indices = data["indices"]
            if len(indices) > 1:
                sims = []
                for i in range(len(indices)):
                    for j in range(i + 1, len(indices)):
                        sims.append(sim_matrix[indices[i], indices[j]])
                data["similarities"] = sims
            else:
                data["similarities"] = [1.0]

        return clusters

    def _build_cluster(
        self,
        cluster_id: str,
        cluster_data: dict,
        ideas: list[IdeaNode],
        source_zones: dict[SourceId, SignalZone] | None = None,
    ) -> IdeaCluster:
        """Build an IdeaCluster from clustering results."""
        indices = cluster_data["indices"]
        similarities = cluster_data["similarities"]

        cluster_ideas = [ideas[i] for i in indices]

        # Calculate similarity metrics
        avg_sim = sum(similarities) / len(similarities) if similarities else 0.0
        min_sim = min(similarities) if similarities else 0.0
        max_sim = max(similarities) if similarities else 0.0

        # Get unique sources first (needed for cluster type determination)
        all_sources = set()
        for idea in cluster_ideas:
            all_sources.update(idea.source_ids)

        # Check for opposing stances (contention detection enhancement)
        has_opposing_stances = self._has_opposing_stances(cluster_ideas)

        # Determine cluster type
        # Note: Consensus requires both high similarity AND multiple sources AND no opposing stances
        # Single-source "consensus" is just an echo chamber, not true agreement
        if has_opposing_stances:
            # Ideas with opposing stances = contention, regardless of similarity
            cluster_type = ClusterType.CONTENTION
        elif (
            avg_sim >= self.consensus_threshold
            and len(all_sources) >= self.min_consensus_sources
        ):
            cluster_type = ClusterType.CONSENSUS
        elif (
            avg_sim >= self.consensus_threshold
            and len(all_sources) < self.min_consensus_sources
        ):
            # High similarity but single source = emerging (potential consensus, not confirmed)
            cluster_type = ClusterType.EMERGING
        elif avg_sim <= self.contention_threshold:
            cluster_type = ClusterType.CONTENTION
        elif len(cluster_ideas) < self.min_cluster_size:
            cluster_type = ClusterType.EMERGING
        else:
            cluster_type = ClusterType.FRAGMENTED

        # Calculate zone distribution
        zone_distribution: dict[SignalZone, int] = {}
        if source_zones:
            for source_id in all_sources:
                if source_id in source_zones:
                    zone = source_zones[source_id]
                    zone_distribution[zone] = zone_distribution.get(zone, 0) + 1

        # Calculate origin diversity using Shannon entropy
        origin_diversity = self._calculate_origin_diversity(zone_distribution)

        # Calculate amplification score
        amplification_score = self._calculate_amplification_score(
            cluster_ideas, zone_distribution
        )

        # Find representative claim (could use centrality, for now use first)
        representative = cluster_ideas[0].claim if cluster_ideas else None

        return IdeaCluster(
            cluster_id=cluster_id,
            cluster_type=cluster_type,
            ideas=cluster_ideas,
            avg_similarity=avg_sim,
            min_similarity=min_sim,
            max_similarity=max_sim,
            unique_sources=len(all_sources),
            zone_distribution=zone_distribution,
            origin_diversity=origin_diversity,
            amplification_score=amplification_score,
            representative_claim=representative,
        )

    def _calculate_origin_diversity(
        self,
        zone_distribution: dict[SignalZone, int],
    ) -> float:
        """
        Calculate origin diversity using Shannon entropy.

        Higher values = more diverse origins.
        Range: 0 (single zone) to 1 (perfectly balanced across all zones)

        Args:
            zone_distribution: Map of zone to count

        Returns:
            Normalized Shannon entropy (0-1)
        """
        if not zone_distribution:
            return 0.0

        total = sum(zone_distribution.values())
        if total == 0:
            return 0.0

        # Calculate Shannon entropy
        entropy = 0.0
        for count in zone_distribution.values():
            if count > 0:
                p = count / total
                entropy -= p * math.log2(p)

        # Normalize by max possible entropy (log2 of number of zones)
        max_entropy = math.log2(len(SignalZone)) if len(SignalZone) > 1 else 1.0
        return entropy / max_entropy if max_entropy > 0 else 0.0

    def _calculate_amplification_score(
        self,
        ideas: list[IdeaNode],
        zone_distribution: dict[SignalZone, int],
    ) -> float:
        """
        Calculate amplification score for echo chamber detection.

        High score indicates:
        - Ideas appear in many sources
        - Sources are concentrated in non-institutional zones
        - Low unique source per idea ratio

        Args:
            ideas: Ideas in the cluster
            zone_distribution: Zone distribution

        Returns:
            Amplification score (0-1)
        """
        if not ideas:
            return 0.0

        # Factor 1: Average sources per idea (more = more amplification)
        total_sources = sum(len(idea.source_ids) for idea in ideas)
        avg_sources_per_idea = total_sources / len(ideas) if ideas else 1
        sources_factor = min(avg_sources_per_idea / 5.0, 1.0)  # Normalize to 5

        # Factor 2: Non-institutional concentration
        total_count = sum(zone_distribution.values()) if zone_distribution else 1
        institutional_count = zone_distribution.get(SignalZone.INSTITUTIONAL, 0)
        non_institutional_ratio = (
            1.0 - (institutional_count / total_count) if total_count else 0.5
        )

        # Factor 3: Grassroots/Speculative dominance
        grassroots = zone_distribution.get(SignalZone.GRASSROOTS, 0)
        speculative = zone_distribution.get(SignalZone.SPECULATIVE, 0)
        echo_zones = (grassroots + speculative) / total_count if total_count else 0

        # Combined score (weighted average)
        amplification = (
            0.3 * sources_factor + 0.3 * non_institutional_ratio + 0.4 * echo_zones
        )

        return min(amplification, 1.0)

    def _has_opposing_stances(
        self,
        ideas: list[IdeaNode],
    ) -> bool:
        """
        Check if ideas in a cluster have opposing stances.

        Returns True if:
        - At least one idea primarily supports and another primarily opposes
        - Stance distributions show clear polarity

        Args:
            ideas: Ideas in the cluster

        Returns:
            True if opposing stances detected
        """
        if len(ideas) < 2:
            return False

        has_support = False
        has_oppose = False

        for idea in ideas:
            dist = idea.stance_distribution
            support_weight = dist.get(Stance.SUPPORT, 0)
            oppose_weight = dist.get(Stance.OPPOSE, 0)

            # Consider it a clear stance if one significantly outweighs the other
            if support_weight > 0.5:
                has_support = True
            if oppose_weight > 0.5:
                has_oppose = True

            # Early exit if we found both
            if has_support and has_oppose:
                return True

        return has_support and has_oppose


class ContentionAnalyzer:
    """
    Specialized analyzer for contention zones.

    Identifies:
    - Opposing stance pairs
    - Evidence conflicts
    - Source polarization
    """

    def find_opposing_pairs(
        self,
        contention_zone: IdeaCluster,
    ) -> list[tuple[IdeaNode, IdeaNode, float]]:
        """
        Find pairs of ideas that directly oppose each other.

        Returns:
            List of (idea1, idea2, opposition_score) tuples
        """
        pairs = []
        ideas = contention_zone.ideas

        for i in range(len(ideas)):
            for j in range(i + 1, len(ideas)):
                idea1, idea2 = ideas[i], ideas[j]

                # Check if stances oppose
                if self._stances_oppose(idea1, idea2):
                    # Calculate opposition strength
                    opposition = self._calculate_opposition(idea1, idea2)
                    pairs.append((idea1, idea2, opposition))

        # Sort by opposition strength
        pairs.sort(key=lambda x: x[2], reverse=True)
        return pairs

    def _stances_oppose(self, idea1: IdeaNode, idea2: IdeaNode) -> bool:
        """Check if two ideas have opposing stance distributions."""
        dist1 = idea1.stance_distribution
        dist2 = idea2.stance_distribution

        # Opposition: one supports, other opposes
        support_diff = abs(dist1.get(Stance.SUPPORT, 0) - dist2.get(Stance.SUPPORT, 0))
        oppose_diff = abs(dist1.get(Stance.OPPOSE, 0) - dist2.get(Stance.OPPOSE, 0))

        return support_diff > 0.4 or oppose_diff > 0.4

    def _calculate_opposition(self, idea1: IdeaNode, idea2: IdeaNode) -> float:
        """Calculate opposition strength between two ideas (0-1)."""
        dist1 = idea1.stance_distribution
        dist2 = idea2.stance_distribution

        # Simple opposition metric: difference in support/oppose ratios
        ratio1 = dist1.get(Stance.SUPPORT, 0) - dist1.get(Stance.OPPOSE, 0)
        ratio2 = dist2.get(Stance.SUPPORT, 0) - dist2.get(Stance.OPPOSE, 0)

        return min(abs(ratio1 - ratio2), 1.0)
