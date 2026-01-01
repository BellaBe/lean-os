"""
Snapshot Builder - Orchestrates full topic analysis pipeline.

Takes only a topic as input, produces a complete Snapshot per architecture.md:
1. URL Discovery via Search APIs (GDELT, Semantic Scholar, Reddit, HackerNews, arXiv)
2. Content Crawling (ContentCrawler)
3. Idea Extraction (IdeaExtractor)
4. Consensus Detection (ConsensusDetector)
5. Amplification Detection
6. Summary Generation (LLM)
7. Graph Building

Usage:
    builder = SnapshotBuilder()
    snapshot = await builder.build("AI regulation EU")
"""

import asyncio
import json
import time
from dataclasses import dataclass, field
from datetime import datetime, timezone
from typing import Any
from urllib.parse import urlparse
from uuid import uuid4

from ..domain import (
    AmplificationWarning,
    ConsensusCluster,
    ContentionZone,
    GraphEdge,
    IdeaId,
    IdeaNode,
    Snapshot,
    SnapshotScope,
    SnapshotStats,
    SourceNode,
    Stance,
)
from ..infrastructure import (
    ConsensusDetector,
    ContentCrawler,
    DirectLLMClient,
    ExtractionConfig,
    IdeaExtractor,
    LLMConfig,
)
from ..infrastructure.crawlers.search_api import (
    MultiSourceSearch,
    SearchAPIConfig,
)


@dataclass
class SnapshotBuilderConfig:
    """Configuration for snapshot building."""

    # Discovery via Search APIs
    # Sources: "news", "academic", "social", "all" or specific providers
    # Providers: "gdelt", "newsapi", "semantic_scholar", "arxiv", "reddit", "hackernews"
    sources: list[str] = field(default_factory=lambda: ["news", "academic", "social"])
    max_urls: int = 20
    max_results_per_source: int = 50
    newsapi_key: str | None = None  # Optional: enables NewsAPI provider

    # Query augmentation
    augment_queries: bool = True  # Generate multiple query variations
    max_query_variations: int = 3  # Number of query variations to generate

    # Pre-crawl relevance filtering
    filter_relevance: bool = True  # Enable LLM-based relevance filtering
    relevance_threshold: int = 6  # Minimum score (1-10) to keep URL
    relevance_batch_size: int = 30  # URLs to score per LLM call
    max_urls_to_filter: int = 60  # Limit URLs sent to filter (saves API calls)

    # Post-extraction idea filtering
    filter_ideas: bool = True  # Filter extracted ideas by topic relevance
    idea_relevance_threshold: int = 6  # Minimum score (1-10) to keep idea
    min_relevant_ideas: int = 5  # Minimum relevant ideas before re-search
    max_search_iterations: int = 2  # Max re-search attempts with new queries

    # Crawling
    max_concurrent_crawls: int = 5
    crawl_timeout: int = 30
    max_content_chars: int = 15000  # Limit content per source for LLM processing

    # Extraction
    llm_provider: str = "groq/llama-3.1-8b-instant"
    llm_api_key: str | None = None
    max_ideas_per_source: int = 10
    chunk_token_threshold: int = 1500  # Smaller chunks for rate-limited APIs

    # Analysis
    consensus_threshold: float = 0.7
    contention_threshold: float = 0.4
    min_cluster_size: int = 2

    # Output
    generate_summary: bool = True
    build_graph: bool = True


class SnapshotBuilder:
    """
    Builds complete Snapshot from a topic.

    Orchestrates all infrastructure components to produce
    the full snapshot structure per architecture.md.
    """

    def __init__(self, config: SnapshotBuilderConfig | None = None):
        self.config = config or SnapshotBuilderConfig()
        self._llm_client: DirectLLMClient | None = None

    def _get_llm_client(self) -> DirectLLMClient:
        """Get or create LLM client."""
        if self._llm_client is None:
            llm_config = LLMConfig(
                provider=self.config.llm_provider,
                api_token=self.config.llm_api_key,
            )
            self._llm_client = DirectLLMClient(llm_config)
        return self._llm_client

    async def build(self, topic: str) -> Snapshot:
        """
        Build a complete snapshot for a topic.

        Args:
            topic: Topic to analyze

        Returns:
            Complete Snapshot entity
        """
        start_time = time.time()
        snapshot_id = uuid4()

        print(f"\n{'=' * 70}")
        print(f"  SNAPSHOT BUILDER: {topic}")
        print(f"{'=' * 70}\n")

        # Track stats
        urls_discovered = 0
        urls_crawled = 0
        urls_failed = 0
        domains_searched: list[str] = []
        all_sources: list = []
        all_ideas: list = []
        used_urls: set[str] = set()

        # ─────────────────────────────────────────────────────────────────
        # Stage 0: Query Augmentation (optional)
        # ─────────────────────────────────────────────────────────────────
        queries = [topic]
        if self.config.augment_queries:
            print("[0/6] Generating search query variations...")
            queries = await self._augment_query(topic)
            print(f"      Queries: {queries}")

        # ─────────────────────────────────────────────────────────────────
        # Iterative Discovery Loop (with re-search if needed)
        # ─────────────────────────────────────────────────────────────────
        for iteration in range(self.config.max_search_iterations):
            iteration_label = f" (iteration {iteration + 1})" if iteration > 0 else ""

            # ─────────────────────────────────────────────────────────────
            # Stage 1: URL Discovery
            # ─────────────────────────────────────────────────────────────
            print(f"\n[1/6] Discovering URLs{iteration_label}...")

            discovered_urls = []
            for query in queries:
                query_urls = await self._discover_urls(query)
                # Filter out already-used URLs
                new_urls = [u for u in query_urls if u["url"] not in used_urls]
                discovered_urls.extend(new_urls)
                for u in new_urls:
                    used_urls.add(u["url"])

            urls_discovered += len(discovered_urls)

            if discovered_urls:
                new_domains = list(set(u["domain"] for u in discovered_urls))
                domains_searched = list(set(domains_searched + new_domains))
                print(f"      Found {len(discovered_urls)} URLs from {len(new_domains)} domains")
            else:
                if iteration == 0:
                    print("      No URLs found")
                    return self._empty_snapshot(snapshot_id, topic, start_time)
                else:
                    print("      No new URLs found, using existing results")
                    break

            # ─────────────────────────────────────────────────────────────
            # Stage 1.5: URL Relevance Filtering (optional)
            # ─────────────────────────────────────────────────────────────
            urls_to_crawl = discovered_urls
            if self.config.filter_relevance:
                urls_to_filter = discovered_urls[:self.config.max_urls_to_filter]
                print(f"\n[1.5/6] Filtering {len(urls_to_filter)} URLs by relevance (threshold: {self.config.relevance_threshold}/10)...")
                urls_to_crawl = await self._filter_by_relevance(urls_to_filter, topic)
                filtered_count = len(urls_to_filter) - len(urls_to_crawl)
                print(f"      Kept {len(urls_to_crawl)} relevant URLs, filtered out {filtered_count}")

                if not urls_to_crawl and iteration == 0:
                    print("      No relevant URLs found after filtering")
                    return self._empty_snapshot(snapshot_id, topic, start_time)

            # ─────────────────────────────────────────────────────────────
            # Stage 2: Content Crawling
            # ─────────────────────────────────────────────────────────────
            if urls_to_crawl:
                print(f"\n[2/6] Crawling content from {min(len(urls_to_crawl), self.config.max_urls)} URLs{iteration_label}...")

                sources, crawled, failed = await self._crawl_content(
                    urls_to_crawl[: self.config.max_urls]
                )
                urls_crawled += crawled
                urls_failed += failed
                all_sources.extend(sources)

                print(f"      Crawled: {crawled}, Failed: {failed}")

            # ─────────────────────────────────────────────────────────────
            # Stage 3: Idea Extraction
            # ─────────────────────────────────────────────────────────────
            if sources:
                print(f"\n[3/6] Extracting ideas from {len(sources)} sources{iteration_label}...")

                ideas = await self._extract_ideas(sources, topic)
                print(f"      Extracted {len(ideas)} ideas")

                # ─────────────────────────────────────────────────────────
                # Stage 3.5: Idea Relevance Filtering (optional)
                # ─────────────────────────────────────────────────────────
                if self.config.filter_ideas and ideas:
                    print(f"\n[3.5/6] Filtering ideas by topic relevance (threshold: {self.config.idea_relevance_threshold}/10)...")
                    relevant_ideas = await self._filter_ideas_by_relevance(ideas, topic)
                    filtered_count = len(ideas) - len(relevant_ideas)
                    print(f"      Kept {len(relevant_ideas)} relevant ideas, filtered out {filtered_count}")
                    ideas = relevant_ideas

                all_ideas.extend(ideas)

            # Check if we have enough relevant ideas
            if len(all_ideas) >= self.config.min_relevant_ideas:
                print(f"\n      ✓ Found {len(all_ideas)} relevant ideas, proceeding to analysis")
                break
            elif iteration < self.config.max_search_iterations - 1:
                print(f"\n      ⚠ Only {len(all_ideas)} relevant ideas found (minimum: {self.config.min_relevant_ideas})")
                print("      Generating new queries for re-search...")
                # Generate new queries for next iteration
                new_queries = await self._augment_query(f"{topic} latest news trends")
                queries = [q for q in new_queries if q not in queries][:2]
                if queries:
                    print(f"      New queries: {queries}")
                else:
                    print("      No new queries generated, using existing results")
                    break

        # Use accumulated results
        sources = all_sources
        ideas = all_ideas

        # Link ideas to sources
        for source in sources:
            source.ideas_contributed = [
                idea.id for idea in ideas if source.id in idea.source_ids
            ]

        # ─────────────────────────────────────────────────────────────────
        # Stage 4: Consensus Detection
        # ─────────────────────────────────────────────────────────────────
        print("\n[4/6] Analyzing consensus and contention...")

        consensus_clusters, contention_zones = await self._analyze_consensus(
            ideas, sources, topic
        )
        print(f"      Consensus clusters: {len(consensus_clusters)}")
        print(f"      Contention zones: {len(contention_zones)}")

        # ─────────────────────────────────────────────────────────────────
        # Stage 5: Amplification Detection
        # ─────────────────────────────────────────────────────────────────
        print("\n[5/6] Detecting amplification patterns...")

        amplification_warnings = self._detect_amplification(sources)
        print(f"      Amplification warnings: {len(amplification_warnings)}")

        # ─────────────────────────────────────────────────────────────────
        # Stage 6: Summary Generation & Graph Building
        # ─────────────────────────────────────────────────────────────────
        print("\n[6/6] Generating summary and building graph...")

        summary = ""
        if self.config.generate_summary and ideas:
            summary = await self._generate_summary(topic, ideas, consensus_clusters, contention_zones)
            print(f"      Summary generated ({len(summary)} chars)")

        graph_nodes, graph_edges = [], []
        if self.config.build_graph:
            graph_nodes, graph_edges = self._build_graph(sources, ideas)
            print(f"      Graph: {len(graph_nodes)} nodes, {len(graph_edges)} edges")

        # ─────────────────────────────────────────────────────────────────
        # Build Snapshot
        # ─────────────────────────────────────────────────────────────────
        elapsed = time.time() - start_time

        # Calculate average relevance
        relevance_scores = [
            s.metadata.get("relevance_score", 0)
            for s in sources
            if s.metadata and s.metadata.get("relevance_score")
        ]
        avg_relevance = sum(relevance_scores) / len(relevance_scores) if relevance_scores else 0

        scope = SnapshotScope(
            time_range=f"{datetime.now(timezone.utc).strftime('%Y-%m-%d')}",
            source_types=list(set(s.source_type.value for s in sources)),
            domains_searched=domains_searched,
            languages=["en"],
        )

        stats = SnapshotStats(
            urls_discovered=urls_discovered,
            urls_crawled=urls_crawled,
            urls_failed=urls_failed,
            ideas_extracted=len(ideas),
            avg_relevance_score=round(avg_relevance, 2),
            crawl_time_seconds=round(elapsed, 1),
        )

        snapshot = Snapshot(
            id=snapshot_id,
            topic=topic,
            generated_at=datetime.now(timezone.utc),
            scope=scope,
            stats=stats,
            summary=summary,
            consensus_clusters=consensus_clusters,
            contention_zones=contention_zones,
            amplification_warnings=amplification_warnings,
            sources=sources,
            ideas=ideas,
            graph_nodes=graph_nodes,
            graph_edges=graph_edges,
        )

        print(f"\n{'=' * 70}")
        print("  SNAPSHOT COMPLETE")
        print(f"  ID: {snapshot_id}")
        print(f"  Time: {elapsed:.1f}s")
        print(f"{'=' * 70}\n")

        return snapshot

    async def _discover_urls(self, topic: str) -> list[dict]:
        """Discover URLs via Search APIs (GDELT, Semantic Scholar, Reddit, etc.)."""
        # Create search client
        api_config = SearchAPIConfig(
            newsapi_key=self.config.newsapi_key,
            max_results_per_provider=self.config.max_results_per_source,
        )
        search = MultiSourceSearch(api_config)

        # Search all configured sources
        print(f"      Searching via {self.config.sources}...")
        api_results = await search.search(
            topic,
            sources=self.config.sources,
            max_results_per_source=self.config.max_results_per_source,
        )

        # Log results by source
        source_counts: dict[str, int] = {}
        for r in api_results:
            source_counts[r.source] = source_counts.get(r.source, 0) + 1
        for src, count in source_counts.items():
            print(f"      {src}: {count} results")

        # Convert to dict format for compatibility with crawling
        all_urls = []
        for r in api_results:
            domain = urlparse(r.url).netloc.replace("www.", "")
            all_urls.append({
                "url": r.url,
                "title": r.title,
                "snippet": r.snippet,
                "domain": domain,
                "relevance_score": r.relevance_score,
                "source_type": r.source_type.value if r.source_type else "news",
                "api_source": r.source,
                "source_name": r.source_name,
                "published_at": r.published_at.isoformat() if r.published_at else None,
            })

        return all_urls

    async def _augment_query(self, topic: str) -> list[str]:
        """
        Generate multiple query variations for better search coverage.

        Returns list of queries including original + variations.
        """
        client = self._get_llm_client()

        prompt = f"""Generate {self.config.max_query_variations} alternative search queries for the topic: "{topic}"

Requirements:
- Each query should find different relevant content
- Include industry-specific terms, synonyms, related concepts
- Make queries specific enough to avoid generic results
- One query should focus on news/recent developments
- One query should focus on companies/startups in this space
- One query should focus on trends/analysis

Return ONLY a JSON array of strings, like: ["query 1", "query 2", "query 3"]
No explanation needed."""

        try:
            response = await client.complete(
                prompt,
                system_prompt="You are a search query optimizer. Return only valid JSON."
            )

            # Parse response
            response = response.strip()
            if response.startswith("```"):
                response = response.split("```")[1]
                if response.startswith("json"):
                    response = response[4:]
            response = response.strip()

            variations = json.loads(response)
            if isinstance(variations, list):
                # Return original + variations
                return [topic] + [v for v in variations if isinstance(v, str)][:self.config.max_query_variations]
        except Exception as e:
            print(f"      (Query augmentation failed: {e})")

        return [topic]  # Fallback to original only

    async def _filter_ideas_by_relevance(
        self, ideas: list, topic: str
    ) -> list:
        """
        Filter extracted ideas by topic relevance.

        Scores each idea and keeps only those above threshold.
        """
        if not ideas:
            return []

        client = self._get_llm_client()
        relevant_ideas = []
        threshold = self.config.idea_relevance_threshold

        # Build scoring prompt
        idea_data = [
            {"idx": i, "claim": idea.claim[:200]}
            for i, idea in enumerate(ideas)
        ]

        prompt = f"""Score each idea's relevance to the topic "{topic}" on a scale of 1-10.

Ideas to score:
{json.dumps(idea_data, indent=2)}

Scoring criteria:
- 9-10: Directly about the topic, highly relevant claim
- 7-8: Clearly related to the topic
- 5-6: Tangentially related
- 3-4: Weak connection
- 1-2: Not relevant at all (off-topic)

Be STRICT: if an idea is about a different subject (e.g., crypto when topic is fashion), score it 1-2.

Return ONLY a JSON array with scores: [{{"idx": 0, "score": 8}}, {{"idx": 1, "score": 2}}]"""

        try:
            response = await client.complete(
                prompt,
                system_prompt="You are a relevance scorer. Be strict. Return only valid JSON."
            )

            # Parse response
            response = response.strip()
            if response.startswith("```"):
                response = response.split("```")[1]
                if response.startswith("json"):
                    response = response[4:]
            response = response.strip()

            scores = json.loads(response)

            # Filter by threshold
            for score_item in scores:
                idx = score_item.get("idx", -1)
                score = score_item.get("score", 0)
                if 0 <= idx < len(ideas) and score >= threshold:
                    relevant_ideas.append(ideas[idx])

        except Exception as e:
            print(f"      (Idea filtering failed: {e}, keeping all)")
            return ideas

        return relevant_ideas

    async def _filter_by_relevance(
        self, urls: list[dict], topic: str
    ) -> list[dict]:
        """
        Filter URLs by topic relevance using LLM scoring.

        Scores each URL based on title/snippet relevance to topic.
        Returns only URLs scoring >= relevance_threshold.
        """
        if not urls:
            return []

        client = self._get_llm_client()
        relevant_urls = []
        threshold = self.config.relevance_threshold
        batch_size = self.config.relevance_batch_size

        # Process in batches
        total_batches = (len(urls) + batch_size - 1) // batch_size
        for batch_num, i in enumerate(range(0, len(urls), batch_size)):
            batch = urls[i:i + batch_size]

            # Rate limit protection: delay between batches
            if batch_num > 0:
                await asyncio.sleep(2)

            # Build scoring prompt
            url_data = [
                {
                    "idx": j,
                    "title": u.get("title", "")[:100],
                    "snippet": u.get("snippet", "")[:150],
                    "domain": u.get("domain", ""),
                }
                for j, u in enumerate(batch)
            ]

            prompt = f"""Score each URL's relevance to the topic "{topic}" on a scale of 1-10.

URLs to score:
{json.dumps(url_data, indent=2)}

Scoring criteria:
- 9-10: Directly about the topic, highly relevant
- 7-8: Related to the topic, good relevance
- 5-6: Tangentially related, some relevance
- 3-4: Weak connection to topic
- 1-2: Not relevant at all

Return ONLY a JSON array with scores, like: [{{"idx": 0, "score": 8}}, {{"idx": 1, "score": 3}}]
Include ALL URLs from the input. No explanation needed."""

            try:
                response = await client.complete(
                    prompt,
                    system_prompt="You are a relevance scorer. Return only valid JSON."
                )

                # Parse scores
                # Handle potential markdown code blocks
                response = response.strip()
                if response.startswith("```"):
                    response = response.split("```")[1]
                    if response.startswith("json"):
                        response = response[4:]
                response = response.strip()

                scores = json.loads(response)

                # Filter by threshold
                for score_item in scores:
                    idx = score_item.get("idx", -1)
                    score = score_item.get("score", 0)
                    if 0 <= idx < len(batch) and score >= threshold:
                        batch[idx]["relevance_score"] = score / 10.0  # Normalize to 0-1
                        relevant_urls.append(batch[idx])

            except json.JSONDecodeError as e:
                # If scoring fails, include all URLs in batch with lower confidence
                print(f"      (Relevance scoring failed for batch, including all: {e})")
                for u in batch:
                    u["relevance_score"] = 0.5
                    relevant_urls.append(u)
            except Exception as e:
                print(f"      (Relevance filter error: {e})")
                # On error, include batch to avoid losing data
                relevant_urls.extend(batch)

        return relevant_urls

    async def _crawl_content(
        self, urls: list[dict]
    ) -> tuple[list[SourceNode], int, int]:
        """Crawl content and convert to SourceNodes."""
        sources = []
        crawled = 0
        failed = 0

        async with ContentCrawler() as crawler:
            for item in urls:
                url = item["url"]
                domain = item.get("domain", urlparse(url).netloc)

                try:
                    result = await crawler.crawl(url)

                    if result.success and result.markdown and len(result.markdown) > 200:
                        source = crawler.result_to_source_node(result)
                        if source:
                            # Preserve API metadata
                            source.metadata = source.metadata or {}
                            source.metadata["relevance_score"] = item.get("relevance_score", 0)
                            source.metadata["snippet"] = item.get("snippet", "")
                            source.metadata["api_source"] = item.get("api_source", "")
                            source.metadata["source_name"] = item.get("source_name", "")
                            source.metadata["published_at"] = item.get("published_at")

                            # Use API-provided title if available and crawler didn't find one
                            if not source.title or source.title == domain:
                                source.title = item.get("title") or source.title

                            # Use API-provided origin name if more descriptive
                            if item.get("source_name") and item["source_name"] != domain:
                                source.origin = item["source_name"]

                            sources.append(source)
                            crawled += 1
                            api_src = item.get("api_source", "")
                            print(f"      [{crawled}] {domain} via {api_src} ({len(result.markdown):,} chars)")
                    else:
                        failed += 1

                except Exception as e:
                    failed += 1
                    print(f"      {domain}: Failed - {e}")

        return sources, crawled, failed

    async def _extract_ideas(
        self, sources: list[SourceNode], topic: str
    ) -> list[IdeaNode]:
        """Extract ideas from sources using LLM."""
        all_ideas = []

        extraction_config = ExtractionConfig(
            provider=self.config.llm_provider,
            api_token=self.config.llm_api_key,
            max_claims_per_source=self.config.max_ideas_per_source,
            chunk_token_threshold=self.config.chunk_token_threshold,
        )
        extractor = IdeaExtractor(extraction_config)

        for source in sources:
            if not source.content_markdown:
                continue

            # Limit content length to avoid rate limits
            content = source.content_markdown
            if len(content) > self.config.max_content_chars:
                content = content[:self.config.max_content_chars]
                print(f"      (Truncated {source.origin} from {len(source.content_markdown):,} to {self.config.max_content_chars:,} chars)")

            try:
                result = await extractor.extract(
                    content=content,
                    source_id=source.id,
                    topic=topic,
                )

                for idea in result.ideas:
                    # Ensure proper ID
                    if not idea.id:
                        idea.id = IdeaId()
                    all_ideas.append(idea)

                print(f"      {source.origin}: {len(result.ideas)} ideas")

            except Exception as e:
                print(f"      {source.origin}: Extraction failed - {e}")

        return all_ideas

    async def _analyze_consensus(
        self,
        ideas: list[IdeaNode],
        sources: list[SourceNode],
        topic: str,
    ) -> tuple[list[ConsensusCluster], list[ContentionZone]]:
        """Analyze ideas for consensus and contention."""
        if len(ideas) < 2:
            return [], []

        detector = ConsensusDetector(
            consensus_threshold=self.config.consensus_threshold,
            contention_threshold=self.config.contention_threshold,
            min_cluster_size=self.config.min_cluster_size,
        )

        # Build source content map
        source_contents = {
            source.id: source.content_markdown or ""
            for source in sources
        }

        analysis = await detector.analyze(topic, ideas, source_contents)

        # Convert to domain entities
        consensus_clusters = []
        for cluster in analysis.consensus_clusters:
            # Build signal zone distribution
            zone_dist: dict[str, int] = {}
            for idea in cluster.ideas:
                for sid in idea.source_ids:
                    source = next((s for s in sources if s.id == sid), None)
                    if source:
                        zone = source.signal_zone.value
                        zone_dist[zone] = zone_dist.get(zone, 0) + 1

            # Get top sources
            top_sources = []
            source_ids_in_cluster = set()
            for idea in cluster.ideas:
                source_ids_in_cluster.update(idea.source_ids)

            for sid in list(source_ids_in_cluster)[:3]:
                source = next((s for s in sources if s.id == sid), None)
                if source:
                    top_sources.append({
                        "origin": source.origin,
                        "url": source.url,
                        "credibility_score": source.credibility_score,
                    })

            consensus_clusters.append(ConsensusCluster(
                representative_claim=cluster.representative_claim or "",
                cluster_type="consensus",
                avg_similarity=cluster.avg_similarity,
                idea_count=len(cluster.ideas),
                source_count=cluster.unique_sources,
                signal_zone_distribution=zone_dist,
                top_sources=top_sources,
                idea_ids=[str(idea.id) for idea in cluster.ideas],
            ))

        contention_zones = []
        for cluster in analysis.contention_zones:
            # Find opposing views
            opposing_views = {"pro": "", "con": ""}
            support_ideas = [i for i in cluster.ideas if i.stance_distribution.get(Stance.SUPPORT, 0) > 0.5]
            oppose_ideas = [i for i in cluster.ideas if i.stance_distribution.get(Stance.OPPOSE, 0) > 0.5]

            if support_ideas:
                opposing_views["pro"] = support_ideas[0].claim[:200]
            if oppose_ideas:
                opposing_views["con"] = oppose_ideas[0].claim[:200]

            contention_zones.append(ContentionZone(
                representative_claim=cluster.representative_claim or "",
                cluster_type="contention",
                avg_similarity=cluster.avg_similarity,
                idea_count=len(cluster.ideas),
                source_count=cluster.unique_sources,
                opposing_views=opposing_views,
                key_disagreement="",
                idea_ids=[str(idea.id) for idea in cluster.ideas],
            ))

        return consensus_clusters, contention_zones

    def _detect_amplification(
        self, sources: list[SourceNode]
    ) -> list[AmplificationWarning]:
        """Detect amplification patterns in sources."""
        warnings = []

        # Group by similar titles
        title_groups: dict[str, list[SourceNode]] = {}
        for source in sources:
            if source.title:
                # Normalize title for grouping
                normalized = source.title.lower().strip()
                words = set(normalized.split()[:5])  # First 5 words
                key = " ".join(sorted(words))

                if key not in title_groups:
                    title_groups[key] = []
                title_groups[key].append(source)

        # Find groups with multiple sources
        for key, group in title_groups.items():
            if len(group) > 1:
                warnings.append(AmplificationWarning(
                    original_url=group[0].url,
                    amplifier_count=len(group) - 1,
                    similar_titles=[s.title for s in group if s.title],
                    note=f"{len(group)} sources with similar titles",
                ))

        return warnings

    async def _generate_summary(
        self,
        topic: str,
        ideas: list[IdeaNode],
        consensus_clusters: list[ConsensusCluster],
        contention_zones: list[ContentionZone],
    ) -> str:
        """Generate natural language summary using LLM."""
        client = self._get_llm_client()

        # Build summary prompt
        consensus_text = "\n".join([
            f"- {c.representative_claim} (agreed by {c.source_count} sources)"
            for c in consensus_clusters[:3]
        ]) or "No clear consensus found."

        contention_text = "\n".join([
            f"- {c.representative_claim}"
            for c in contention_zones[:3]
        ]) or "No major contentions found."

        stance_counts = {"support": 0, "oppose": 0, "neutral": 0}
        for idea in ideas:
            max_stance = max(idea.stance_distribution.items(), key=lambda x: x[1], default=(Stance.NEUTRAL, 0))
            stance_counts[max_stance[0].value if isinstance(max_stance[0], Stance) else max_stance[0]] += 1

        prompt = f"""Summarize the discourse on "{topic}" based on this analysis:

Total ideas extracted: {len(ideas)}
Stance distribution: {stance_counts}

Key consensus points:
{consensus_text}

Areas of contention:
{contention_text}

Write a 2-3 sentence summary capturing the main findings and any notable patterns.
Focus on what the sources agree on, what they disagree on, and the overall sentiment."""

        try:
            summary = await client.complete(prompt, system_prompt="You are a research analyst. Be concise and factual.")
            return summary.strip()
        except Exception as e:
            return f"Summary generation failed: {e}"

    def _build_graph(
        self,
        sources: list[SourceNode],
        ideas: list[IdeaNode],
    ) -> tuple[list[dict], list[GraphEdge]]:
        """Build graph nodes and edges for visualization."""
        nodes = []
        edges = []

        # Add source nodes
        for source in sources:
            nodes.append({
                "id": str(source.id),
                "type": "source",
                "label": source.origin,
                "url": source.url,
                "signal_zone": source.signal_zone.value,
            })

        # Add idea nodes
        for idea in ideas:
            max_stance = max(idea.stance_distribution.items(), key=lambda x: x[1], default=(Stance.NEUTRAL, 0))
            nodes.append({
                "id": str(idea.id),
                "type": "idea",
                "label": idea.claim[:50] + "..." if len(idea.claim) > 50 else idea.claim,
                "stance": max_stance[0].value if isinstance(max_stance[0], Stance) else max_stance[0],
                "cluster": idea.cluster,
            })

            # Add edges from sources to ideas
            for source_id in idea.source_ids:
                edges.append(GraphEdge(
                    source_id=str(source_id),
                    target_id=str(idea.id),
                    relationship="contributes",
                    weight=1.0,
                ))

        return nodes, edges

    def _empty_snapshot(
        self,
        snapshot_id: Any,
        topic: str,
        start_time: float,
    ) -> Snapshot:
        """Create empty snapshot for error cases."""
        elapsed = time.time() - start_time
        return Snapshot(
            id=snapshot_id,
            topic=topic,
            generated_at=datetime.now(timezone.utc),
            scope=SnapshotScope(time_range="", source_types=[], domains_searched=[]),
            stats=SnapshotStats(crawl_time_seconds=round(elapsed, 1)),
            summary="No data collected.",
            consensus_clusters=[],
            contention_zones=[],
            amplification_warnings=[],
            sources=[],
            ideas=[],
            graph_nodes=[],
            graph_edges=[],
        )


# Convenience function
async def build_snapshot(
    topic: str,
    max_urls: int = 20,
    llm_provider: str = "groq/llama-3.1-8b-instant",
    llm_api_key: str | None = None,
) -> Snapshot:
    """
    Quick helper to build a snapshot.

    Example:
        snapshot = await build_snapshot("AI regulation EU")
    """
    config = SnapshotBuilderConfig(
        max_urls=max_urls,
        llm_provider=llm_provider,
        llm_api_key=llm_api_key,
    )
    builder = SnapshotBuilder(config)
    return await builder.build(topic)
