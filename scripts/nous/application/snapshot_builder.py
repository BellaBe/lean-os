"""
Snapshot Builder - Orchestrates full topic analysis pipeline.

Takes only a topic as input, produces a complete Snapshot:
1. URL Discovery via Search APIs (GDELT, arXiv, Reddit, DuckDuckGo)
2. Site-specific social/tech searches (Twitter, LinkedIn, YCombinator)
3. Content Crawling with PageSnapshotter for dynamic content
4. Idea Extraction (hybrid: CSS/regex then LLM)
5. Consensus Detection
6. Amplification Detection
7. Summary Generation
8. Graph Building

Usage:
    builder = SnapshotBuilder()
    snapshot = await builder.build("AI regulation EU")
"""

import asyncio
import json
import logging
import time

from datetime import datetime, timezone
from typing import Any
from urllib.parse import urlparse
from uuid import uuid4

from .config import SnapshotBuilderConfig

from ..infrastructure.logging import init_session_logging

from ..domain import (
    AmplificationWarning,
    ConsensusCluster,
    ContentionZone,
    GraphEdge,
    IdeaId,
    IdeaNode,
    SignalZone,
    Snapshot,
    SnapshotScope,
    SnapshotStats,
    SourceId,
    SourceNode,
    SourceType,
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
# Search APIs - direct integration
from ..infrastructure.crawlers.search_api import (
    APISearchResult,
    MultiSourceSearch,
    SearchAPIConfig,
)
from ..infrastructure.crawlers.url_seeder import (
    UrlSeeder,
    SeedingConfig,
    generate_site_queries,
    SOCIAL_SITE_SEARCHES,
    TECH_SITE_SEARCHES,
    YC_DOMAINS,
)
from ..infrastructure.crawlers.page_snapshot import (
    PageSnapshotter,
    PageSnapshotConfig,
    PageSnapshot,
)
# Crawl4AI-enhanced components
from ..infrastructure.crawlers.parallel_crawler import ParallelCrawler
from ..infrastructure.crawlers.diagnostics import CrawlDiagnostics
from ..infrastructure.crawlers.zone_config import get_zone_for_domain
from ..infrastructure.extraction.hybrid_extractor import HybridExtractor, QuickExtraction

# Initialize logging
log = logging.getLogger("nous.snapshot")


def _story(msg: str, indent: int = 0, symbol: str = "→") -> None:
    """Print a story-telling message to stdout for real-time feedback."""
    prefix = "  " * indent
    print(f"{prefix}{symbol} {msg}")

# Social platform domains that benefit from PageSnapshotter
SOCIAL_SNAPSHOT_DOMAINS = {
    "x.com",
    "linkedin.com",
    "youtube.com",
    "facebook.com",
    "instagram.com",
    "tiktok.com",
    "threads.net",
    "mastodon.social",
}


def _is_social_url(url: str) -> bool:
    """Check if URL is from a social platform that needs PageSnapshotter."""
    try:
        domain = urlparse(url).netloc.replace("www.", "").lower()
        # Check exact match or subdomain match
        for social_domain in SOCIAL_SNAPSHOT_DOMAINS:
            if domain == social_domain or domain.endswith(f".{social_domain}"):
                return True
        return False
    except Exception:
        return False


def _classify_source_type(url: str, domain: str) -> SourceType:
    """Classify source type from URL/domain."""
    domain_lower = domain.lower()
    url_lower = url.lower()

    # Check domain-based classification first
    if any(
        d in domain_lower
        for d in ["arxiv", "nature.com", "science.org", "springer", "ieee"]
    ):
        return SourceType.ACADEMIC
    if any(d in domain_lower for d in ["reddit", "twitter", "x.com", "mastodon", "threads", "linkedin"]):
        return SourceType.SOCIAL
    if any(d in domain_lower for d in [".gov", "europa.eu", "gov.uk", "whitehouse"]):
        return SourceType.GOVERNMENT
    if any(d in domain_lower for d in ["substack", "medium", "wordpress", "blogger", "ghost", "dev.to"]):
        return SourceType.BLOG
    if any(d in domain_lower for d in ["ycombinator", "producthunt", "techcrunch", "theverge"]):
        return SourceType.NEWS  # Tech news

    # Path-based detection
    if any(p in url_lower for p in ["/research/", "/paper/", "/publication/", "/abstract/", ".pdf"]):
        return SourceType.ACADEMIC
    if any(p in url_lower for p in ["/blog/", "/posts/", "/article/"]) and "news" not in domain_lower:
        return SourceType.BLOG
    if any(p in url_lower for p in ["/forum/", "/thread/", "/discussion/", "/comments/"]):
        return SourceType.FORUM
    if any(p in url_lower for p in ["/video/", "/watch/", "/embed/", "youtube.com"]):
        return SourceType.VIDEO

    return SourceType.NEWS


class SnapshotBuilder:
    """
    Builds complete Snapshot from a topic.

    Orchestrates all infrastructure components to produce
    the full snapshot structure per architecture.md.
    """

    def __init__(self, config: SnapshotBuilderConfig, llm_client: DirectLLMClient):
        self.config = config
        self.llm_client = llm_client

    async def build(self, topic: str) -> Snapshot:
        """
        Build a complete snapshot for a topic.

        Args:
            topic: Topic to analyze

        Returns:
            Complete Snapshot entity
        """
        # Initialize session logging
        log_file = init_session_logging()

        start_time = time.time()
        snapshot_id = uuid4()

        # ─────────────────────────────────────────────────────────────────
        # Story: Begin
        # ─────────────────────────────────────────────────────────────────
        print("\n" + "=" * 60)
        print(f"🔍 NOUS SNAPSHOT: {topic}")
        print("=" * 60)
        _story(f"Session ID: {str(snapshot_id)[:8]}...")
        _story(f"Sources: {', '.join(self.config.sources)}")
        _story(f"Max URLs: {self.config.max_urls}")
        _story(f"LLM: {self.config.llm_provider}")
        if self.config.use_social_snapshots:
            _story("Social snapshots: ENABLED (Twitter, LinkedIn, YouTube)")
        print()

        log.info(f"SNAPSHOT BUILD START: {topic}")
        log.info(f"Snapshot ID: {snapshot_id}")

        # Track stats
        urls_discovered = 0
        urls_crawled = 0
        urls_failed = 0
        domains_searched: list[str] = []
        all_sources: list[SourceNode] = []
        all_ideas: list[IdeaNode] = []
        used_urls: set[str] = set()

        # ─────────────────────────────────────────────────────────────────
        # Stage 0: Query Augmentation (optional)
        # ─────────────────────────────────────────────────────────────────
        queries = [topic]
        if self.config.augment_queries:
            _story("Generating search query variations...", symbol="🔄")
            queries = await self._augment_query(topic)
            for i, q in enumerate(queries):
                _story(f"Query {i+1}: {q}", indent=1, symbol="•")
            print()

        # ─────────────────────────────────────────────────────────────────
        # Iterative Discovery Loop (with re-search if needed)
        # ─────────────────────────────────────────────────────────────────
        for iteration in range(self.config.max_search_iterations):
            iteration_label = f" (round {iteration + 1})" if iteration > 0 else ""

            # ─────────────────────────────────────────────────────────────
            # Stage 1: URL Discovery
            # ─────────────────────────────────────────────────────────────
            print(f"📡 STAGE 1: DISCOVERY{iteration_label}")
            print("-" * 40)

            discovered_urls = []
            for query in queries:
                _story(f"Searching: \"{query[:50]}{'...' if len(query) > 50 else ''}\"")
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

                # Count by source type
                source_counts: dict[str, int] = {}
                for u in discovered_urls:
                    src = u.get("api_source", "unknown")
                    source_counts[src] = source_counts.get(src, 0) + 1

                print()
                _story(f"Found {len(discovered_urls)} URLs from {len(new_domains)} domains", symbol="✓")
                for src, count in sorted(source_counts.items(), key=lambda x: -x[1]):
                    _story(f"{src}: {count} URLs", indent=1, symbol="•")
                print()
            else:
                if iteration == 0:
                    _story("No URLs found - cannot proceed", symbol="✗")
                    return self._empty_snapshot(snapshot_id, topic, start_time)
                else:
                    _story("No new URLs found, using existing results", symbol="⚠")
                    break

            # ─────────────────────────────────────────────────────────────
            # Stage 1.2: Domain Expansion via URL Seeding (optional)
            # ─────────────────────────────────────────────────────────────
            if self.config.use_domain_expansion and discovered_urls:
                _story("Expanding top domains via sitemap/Common Crawl...", symbol="🔗")
                expanded_urls = await self._expand_domains(discovered_urls, topic)
                if expanded_urls:
                    # Add expanded URLs (filter out already-used)
                    for u in expanded_urls:
                        if u["url"] not in used_urls:
                            discovered_urls.append(u)
                            used_urls.add(u["url"])
                    urls_discovered += len(expanded_urls)
                    _story(f"Added {len(expanded_urls)} URLs from domain expansion", indent=1, symbol="+")

            # ─────────────────────────────────────────────────────────────
            # Stage 1.5: URL Relevance Filtering (optional)
            # ─────────────────────────────────────────────────────────────
            urls_to_crawl = discovered_urls
            if self.config.filter_relevance:
                urls_to_filter = discovered_urls[:self.config.max_urls_to_filter]
                _story(f"Filtering {len(urls_to_filter)} URLs by relevance (threshold: {self.config.relevance_threshold}/10)...", symbol="🎯")
                urls_to_crawl = await self._filter_by_relevance(urls_to_filter, topic)
                filtered_count = len(urls_to_filter) - len(urls_to_crawl)
                _story(f"Kept {len(urls_to_crawl)} relevant, filtered out {filtered_count}", indent=1, symbol="✓")
                print()

                if not urls_to_crawl and iteration == 0:
                    _story("No relevant URLs found after filtering", symbol="✗")
                    return self._empty_snapshot(snapshot_id, topic, start_time)

            # ─────────────────────────────────────────────────────────────
            # Stage 2: Content Crawling
            # ─────────────────────────────────────────────────────────────
            sources: list[SourceNode] = []
            if urls_to_crawl:
                num_to_crawl = min(len(urls_to_crawl), self.config.max_urls)
                print(f"🌐 STAGE 2: CRAWLING{iteration_label}")
                print("-" * 40)
                _story(f"Crawling {num_to_crawl} URLs...")

                sources, crawled, failed, crawl_diagnostics = await self._crawl_content(
                    urls_to_crawl[: self.config.max_urls]
                )
                urls_crawled += crawled
                urls_failed += failed
                all_sources.extend(sources)

                # Show crawl summary
                print()
                yield_rate = crawled / num_to_crawl * 100 if num_to_crawl > 0 else 0
                _story(f"Crawled: {crawled} success, {failed} failed ({yield_rate:.0f}% yield)", symbol="✓")

                # Count social vs regular
                social_count = sum(1 for s in sources if s.metadata and s.metadata.get("captured_via") == "page_snapshot")
                if social_count > 0:
                    _story(f"Social snapshots: {social_count} captured with PageSnapshotter", indent=1, symbol="📸")
                print()

            # ─────────────────────────────────────────────────────────────
            # Stage 3: Idea Extraction
            # ─────────────────────────────────────────────────────────────
            if sources:
                print(f"🧠 STAGE 3: EXTRACTION{iteration_label}")
                print("-" * 40)
                _story(f"Extracting ideas from {len(sources)} sources...")

                ideas = await self._extract_ideas(sources, topic)

                # ─────────────────────────────────────────────────────────
                # Stage 3.5: Idea Relevance Filtering (optional)
                # ─────────────────────────────────────────────────────────
                if self.config.filter_ideas and ideas:
                    _story(f"Filtering {len(ideas)} ideas by topic relevance...", symbol="🎯")
                    relevant_ideas = await self._filter_ideas_by_relevance(ideas, topic)
                    filtered_count = len(ideas) - len(relevant_ideas)
                    _story(f"Kept {len(relevant_ideas)} relevant, filtered out {filtered_count}", indent=1, symbol="✓")
                    ideas = relevant_ideas

                all_ideas.extend(ideas)
                print()
                _story(f"Total ideas extracted: {len(ideas)}", symbol="✓")
                print()

            # Check if we have enough relevant ideas
            if len(all_ideas) >= self.config.min_relevant_ideas:
                _story(f"Found {len(all_ideas)} relevant ideas, proceeding to analysis", symbol="✓")
                break
            elif iteration < self.config.max_search_iterations - 1:
                _story(f"Only {len(all_ideas)} ideas (need {self.config.min_relevant_ideas}), searching again...", symbol="⚠")
                # Generate new queries for next iteration
                new_queries = await self._augment_query(f"{topic} latest news trends")
                queries = [q for q in new_queries if q not in queries][:2]
                if queries:
                    for q in queries:
                        _story(f"New query: {q}", indent=1, symbol="•")
                else:
                    _story("No new queries generated, using existing results", symbol="⚠")
                    break
                print()

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
        print("🔬 STAGE 4: ANALYSIS")
        print("-" * 40)
        _story("Analyzing consensus and contention patterns...")

        consensus_clusters, contention_zones = await self._analyze_consensus(
            ideas, sources, topic
        )

        if consensus_clusters:
            _story(f"Consensus clusters: {len(consensus_clusters)}", indent=1, symbol="🤝")
            for i, c in enumerate(consensus_clusters[:3]):
                _story(f"\"{c.representative_claim[:60]}...\"", indent=2, symbol="•")
        if contention_zones:
            _story(f"Contention zones: {len(contention_zones)}", indent=1, symbol="⚔️")
            for c in contention_zones[:2]:
                _story(f"\"{c.representative_claim[:60]}...\"", indent=2, symbol="•")
        print()

        # ─────────────────────────────────────────────────────────────────
        # Stage 5: Amplification Detection
        # ─────────────────────────────────────────────────────────────────
        _story("Detecting amplification patterns...", symbol="📢")

        amplification_warnings = self._detect_amplification(sources)
        if amplification_warnings:
            _story(f"Amplification warnings: {len(amplification_warnings)}", indent=1, symbol="⚠")
        else:
            _story("No amplification detected", indent=1, symbol="✓")
        print()

        # ─────────────────────────────────────────────────────────────────
        # Stage 6: Summary Generation & Graph Building
        # ─────────────────────────────────────────────────────────────────
        print("📝 STAGE 5: SYNTHESIS")
        print("-" * 40)

        summary = ""
        if self.config.generate_summary and ideas:
            _story("Generating executive summary...")
            summary = await self._generate_summary(topic, ideas, consensus_clusters, contention_zones)
            _story(f"Summary: {len(summary)} chars", indent=1, symbol="✓")

        graph_nodes, graph_edges = [], []
        if self.config.build_graph:
            _story("Building knowledge graph...")
            graph_nodes, graph_edges = self._build_graph(sources, ideas)
            _story(f"Graph: {len(graph_nodes)} nodes, {len(graph_edges)} edges", indent=1, symbol="✓")
        print()

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

        # Determine languages used
        languages_used = ["en"]
        if self.config.target_languages:
            languages_used = list(set(["en"] + self.config.target_languages))

        scope = SnapshotScope(
            time_range=f"{datetime.now(timezone.utc).strftime('%Y-%m-%d')}",  # noqa: UP017
            source_types=list(set(s.source_type.value for s in sources)),
            domains_searched=domains_searched,
            languages=languages_used,
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
            generated_at=datetime.now(timezone.utc),  # noqa: UP017
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

        # ─────────────────────────────────────────────────────────────────
        # Final Summary
        # ─────────────────────────────────────────────────────────────────
        print("=" * 60)
        print("✅ SNAPSHOT COMPLETE")
        print("=" * 60)
        print(f"  Topic: {topic}")
        print(f"  Time: {elapsed:.1f}s")
        print()
        print("  📊 Stats:")
        print(f"     URLs discovered: {urls_discovered}")
        print(f"     URLs crawled: {urls_crawled} ({urls_failed} failed)")
        print(f"     Ideas extracted: {len(ideas)}")
        print(f"     Consensus clusters: {len(consensus_clusters)}")
        print(f"     Contention zones: {len(contention_zones)}")
        print()

        # Show source type breakdown
        source_type_counts: dict[str, int] = {}
        for s in sources:
            st = s.source_type.value if hasattr(s.source_type, 'value') else str(s.source_type)
            source_type_counts[st] = source_type_counts.get(st, 0) + 1
        if source_type_counts:
            print("  📰 Source types:")
            for st, count in sorted(source_type_counts.items(), key=lambda x: -x[1]):
                print(f"     {st}: {count}")
            print()

        # Show signal zone breakdown
        zone_counts: dict[str, int] = {}
        for s in sources:
            z = s.signal_zone.value if hasattr(s.signal_zone, 'value') else str(s.signal_zone)
            zone_counts[z] = zone_counts.get(z, 0) + 1
        if zone_counts:
            print("  🎯 Signal zones:")
            for z, count in sorted(zone_counts.items(), key=lambda x: -x[1]):
                print(f"     {z}: {count}")
            print()

        if summary:
            print("  📝 Summary:")
            # Word wrap summary at 60 chars
            words = summary.split()
            line = "     "
            for word in words[:50]:  # First 50 words
                if len(line) + len(word) > 65:
                    print(line)
                    line = "     " + word
                else:
                    line += " " + word if line.strip() else word
            if line.strip():
                print(line)
            if len(words) > 50:
                print("     ...")
            print()

        log.info(f"SNAPSHOT COMPLETE: {snapshot_id} in {elapsed:.1f}s")

        return snapshot

    async def _discover_urls(self, topic: str) -> list[dict[str, Any]]:
        """
        Discover URLs via Search APIs.

        Uses MultiSourceSearch directly for topic-aware discovery:
        - RSS feeds (news) from 20+ major outlets
        - arXiv (academic)
        - Reddit (social)
        - DuckDuckGo (web)
        - Site-specific: Twitter, LinkedIn, YouTube via DuckDuckGo site: queries
        - Tech sources: YCombinator, ProductHunt, GitHub via site: queries

        Returns URL metadata dicts for the filtering/crawling pipeline.
        """
        log.info(f"DISCOVERY START: topic='{topic}'")
        log.debug(f"  sources={self.config.sources}, max_per_source={self.config.max_results_per_source}")

        # Build list of queries (with translations if enabled)
        queries_to_search = [topic]
        if self.config.translate_queries and self.config.target_languages:
            for lang in self.config.target_languages:
                if lang.lower() != "en":
                    translated = await self._translate_query(topic, lang)
                    if translated != topic:
                        queries_to_search.append(translated)
                        log.info(f"Translated to {lang}: {translated}")

        # Configure search
        api_config = SearchAPIConfig(
            max_results_per_provider=self.config.max_results_per_source,
            language="en",
            days_back=30,
            use_screenshot_fallback=self.config.use_screenshot_fallback,
            screenshot_llm_provider=self.config.screenshot_llm_provider,
        )
        search = MultiSourceSearch(api_config)

        # Collect all results
        all_results: list[APISearchResult] = []
        seen_urls: set[str] = set()

        for i, query in enumerate(queries_to_search):
            # Wait between query variations (providers have rate limits)
            if i > 0:
                log.info("[Wait] 5s between search queries...")
                await asyncio.sleep(5)

            region_info = f" (region: {self.config.region})" if self.config.region else ""
            log.info(f"Searching via {self.config.sources}{region_info}: {query[:50]}...")

            # Core API search
            results = await search.search(
                query,
                sources=self.config.sources,
                max_results_per_source=self.config.max_results_per_source,
            )

            # Deduplicate
            for result in results:
                if result.url not in seen_urls:
                    seen_urls.add(result.url)
                    all_results.append(result)

            # Calculate relevance for logging
            scores = [r.relevance_score for r in results if r.relevance_score]
            avg_score = sum(scores) / len(scores) if scores else 0
            log.info(f"  Found {len(results)} results, avg_relevance={avg_score:.2f}")

        # Generate site-specific queries for broader social/tech coverage
        if self.config.use_site_specific_search:
            log.info("Searching site-specific sources (social/tech)...")
            site_queries = generate_site_queries(
                topic,
                include_social=True,
                include_tech="tech" in topic.lower() or "startup" in topic.lower(),
            )

            # Run site-specific searches (limit to avoid too many queries)
            for site_query in site_queries[:5]:
                try:
                    site_results = await search.search(
                        site_query,
                        sources=["web"],  # Use DuckDuckGo for site: queries
                        max_results_per_source=10,
                    )
                    for result in site_results:
                        if result.url not in seen_urls:
                            seen_urls.add(result.url)
                            all_results.append(result)
                    if site_results:
                        log.debug(f"  {site_query[:40]}... -> {len(site_results)} results")
                except Exception as e:
                    log.debug(f"  Site search failed: {site_query[:30]}... ({e})")

                # Brief delay between site queries
                await asyncio.sleep(0.5)

        # Convert APISearchResult to dict format for pipeline
        all_urls = []
        for result in all_results:
            domain = urlparse(result.url).netloc.replace("www.", "")
            source_type = result.source_type or _classify_source_type(result.url, domain)

            all_urls.append({
                "url": result.url,
                "title": result.title,
                "snippet": result.snippet or "",
                "domain": domain,
                "relevance_score": result.relevance_score or 0,
                "source_type": source_type.value if hasattr(source_type, 'value') else str(source_type),
                "api_source": result.source,
                "source_name": result.source_name or domain,
                "published_at": result.published_at.isoformat() if result.published_at else None,
            })

        log.info(f"DISCOVERY COMPLETE: {len(all_urls)} URLs discovered")
        return all_urls

    async def _expand_domains(
        self, discovered_urls: list[dict[str, Any]], topic: str
    ) -> list[dict[str, Any]]:
        """
        Expand discovered domains using URL Seeder (sitemap + Common Crawl).

        Uses Crawl4AI's AsyncUrlSeeder with BM25 scoring to find more
        relevant URLs on domains already discovered via search APIs.

        Args:
            discovered_urls: URLs already discovered
            topic: Topic for BM25 relevance scoring

        Returns:
            Additional URLs from domain expansion (deduplicated)
        """
        if not discovered_urls:
            return []

        # Extract unique domains and count URLs per domain
        domain_counts: dict[str, int] = {}
        seen_urls = {u["url"] for u in discovered_urls}

        for u in discovered_urls:
            domain = u.get("domain", "")
            if domain:
                domain_counts[domain] = domain_counts.get(domain, 0) + 1

        # Select top domains to expand (most URLs = most relevant domains)
        sorted_domains = sorted(domain_counts.items(), key=lambda x: x[1], reverse=True)
        domains_to_expand = [d for d, _ in sorted_domains[:self.config.expansion_max_domains]]

        if not domains_to_expand:
            return []

        log.info(f"DOMAIN EXPANSION: expanding {len(domains_to_expand)} domains via {self.config.expansion_source}")
        log.info(f"Expanding {len(domains_to_expand)} domains via {self.config.expansion_source}...")

        # Configure URL seeding
        seeding_config = SeedingConfig(
            source=self.config.expansion_source,
            max_urls=self.config.expansion_max_per_domain,
            extract_head=self.config.expansion_extract_head,
            score_threshold=self.config.expansion_score_threshold,
            query=topic,
            scoring_method="bm25",
            filter_nonsense_urls=True,
        )

        expanded_urls = []

        try:
            async with UrlSeeder() as seeder:
                results = await seeder.discover_many(domains_to_expand, topic, seeding_config)

                for domain, seeded_urls in results.items():
                    new_count = 0
                    for seeded in seeded_urls:
                        if seeded.url not in seen_urls:
                            seen_urls.add(seeded.url)
                            expanded_urls.append({
                                "url": seeded.url,
                                "title": seeded.title or "",
                                "snippet": seeded.description or "",
                                "domain": domain,
                                "relevance_score": seeded.relevance_score,
                                "source_type": "news",  # Default, will be reclassified
                                "api_source": "url_seeder",
                                "source_name": domain,
                                "published_at": None,
                            })
                            new_count += 1

                    if new_count > 0:
                        log.info(f"  {domain}: +{new_count} URLs (BM25 score >= {self.config.expansion_score_threshold})")
                        log.info(f"  {domain}: {new_count} new URLs via seeding")

        except Exception as e:
            log.warning(f"Domain expansion failed: {e}")
            log.info(f"Domain expansion failed: {e}")

        log.info(f"DOMAIN EXPANSION COMPLETE: {len(expanded_urls)} additional URLs")
        return expanded_urls

    async def _augment_query(self, topic: str) -> list[str]:
        """
        Generate multiple query variations for better search coverage.

        Returns list of queries including original + variations.
        """

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
            response = await self.llm_client.complete(
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
            log.info(f"(Query augmentation failed: {e})")

        return [topic]  # Fallback to original only

    async def _translate_query(self, query: str, target_lang: str) -> str:
        """
        Translate a search query to target language using LLM.

        Args:
            query: Original query (assumed English)
            target_lang: Target language code (e.g., "de", "fr", "es")

        Returns:
            Translated query
        """
        # Language code to name mapping
        lang_names = {
            "de": "German", "fr": "French", "es": "Spanish", "it": "Italian",
            "pt": "Portuguese", "nl": "Dutch", "pl": "Polish", "ru": "Russian",
            "ja": "Japanese", "ko": "Korean", "zh": "Chinese", "ar": "Arabic",
            "hi": "Hindi", "sv": "Swedish", "no": "Norwegian", "da": "Danish",
            "fi": "Finnish", "tr": "Turkish", "he": "Hebrew", "th": "Thai",
        }
        lang_name = lang_names.get(target_lang.lower(), target_lang)

        prompt = f"""Translate this search query to {lang_name}.
Keep it concise and preserve search intent. Use natural phrasing.

Original query: {query}

Translation (just the query, no explanation):"""

        try:
            response = await self.llm_client.complete(
                prompt,
                system_prompt="You are a translator. Return only the translated query."
            )
            translated = response.strip().strip('"').strip("'")
            return translated if translated else query
        except Exception as e:
            log.info(f"(Translation to {lang_name} failed: {e})")
            return query

    async def _filter_ideas_by_relevance(
        self, ideas: list, topic: str
    ) -> list:
        """
        Filter extracted ideas by topic relevance.

        Scores each idea in batches to stay under LLM token limits,
        then keeps only those above threshold.
        """
        if not ideas:
            return []

        relevant_ideas = []
        threshold = self.config.idea_relevance_threshold
        batch_size = 30  # ~30 ideas per batch to stay under 6K token limit

        # Process in batches
        for batch_start in range(0, len(ideas), batch_size):
            batch_end = min(batch_start + batch_size, len(ideas))
            batch = ideas[batch_start:batch_end]

            # Build scoring prompt for this batch
            idea_data = [
                {"idx": i, "claim": idea.claim[:200]}
                for i, idea in enumerate(batch)
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
                response = await self.llm_client.complete(
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

                # Filter by threshold (idx is relative to batch)
                for score_item in scores:
                    idx = score_item.get("idx", -1)
                    score = score_item.get("score", 0)
                    if 0 <= idx < len(batch) and score >= threshold:
                        relevant_ideas.append(batch[idx])

            except Exception as e:
                log.warning(f"(Batch {batch_start//batch_size + 1} filtering failed: {e}, keeping batch)")
                relevant_ideas.extend(batch)

            # Brief delay between batches to respect rate limits
            if batch_end < len(ideas):
                await asyncio.sleep(0.5)

        return relevant_ideas

    async def _filter_by_relevance(
        self, urls: list[dict[str, Any]], topic: str
    ) -> list[dict[str, Any]]:
        """
        Filter URLs by topic relevance using LLM scoring.

        Scores each URL based on title/snippet relevance to topic.
        Returns only URLs scoring >= relevance_threshold.
        """
        if not urls:
            return []

        relevant_urls = []
        threshold = self.config.relevance_threshold
        batch_size = self.config.relevance_batch_size

        # Process in batches
        total_batches = (len(urls) + batch_size - 1) // batch_size
        for batch_num, i in enumerate(range(0, len(urls), batch_size)):
            batch = urls[i:i + batch_size]

            # Rate limit protection: delay between batches (5s for Groq free tier)
            if batch_num > 0:
                await asyncio.sleep(5)

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
                response = await self.llm_client.complete(
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
                log.info(f"(Relevance scoring failed for batch, including all: {e})")
                for u in batch:
                    u["relevance_score"] = 0.5
                    relevant_urls.append(u)
            except Exception as e:
                log.info(f"(Relevance filter error: {e})")
                # On error, include batch to avoid losing data
                relevant_urls.extend(batch)

        return relevant_urls

    async def _crawl_content(
        self, urls: list[dict]
    ) -> tuple[list[SourceNode], int, int, CrawlDiagnostics | None]:
        """
        Crawl content and convert to SourceNodes.

        Routes URLs appropriately:
        - Social URLs (Twitter, LinkedIn, YouTube) -> PageSnapshotter
        - Other URLs -> ParallelCrawler (or sequential)

        Returns (sources, crawled_count, failed_count, diagnostics).
        """
        log.info(f"CRAWL START: {len(urls)} URLs to crawl")

        # Build URL list and metadata map
        url_list = [item["url"] for item in urls]
        url_metadata = {item["url"]: item for item in urls}

        # Split URLs into social and non-social
        social_urls = []
        regular_urls = []

        if self.config.use_social_snapshots:
            for url in url_list:
                if _is_social_url(url):
                    social_urls.append(url)
                else:
                    regular_urls.append(url)
            if social_urls:
                log.info(f"  Social URLs: {len(social_urls)} (using PageSnapshotter)")
                log.info(f"  Regular URLs: {len(regular_urls)} (using ParallelCrawler)")
        else:
            regular_urls = url_list

        # Crawl regular URLs
        all_sources = []
        total_crawled = 0
        total_failed = 0
        diagnostics = None

        if regular_urls:
            if self.config.use_parallel_crawler:
                sources, crawled, failed, diagnostics = await self._crawl_parallel(regular_urls, url_metadata)
            else:
                sources, crawled, failed, diagnostics = await self._crawl_sequential(regular_urls, url_metadata)
            all_sources.extend(sources)
            total_crawled += crawled
            total_failed += failed

        # Crawl social URLs with PageSnapshotter
        if social_urls:
            social_sources, social_crawled, social_failed, snapshots = await self._crawl_social_with_snapshots(
                social_urls, url_metadata
            )
            all_sources.extend(social_sources)
            total_crawled += social_crawled
            total_failed += social_failed

            # Store snapshots for potential later use (evidence, temporal tracking)
            if snapshots and hasattr(self, '_social_snapshots'):
                self._social_snapshots.extend(snapshots)
            elif snapshots:
                self._social_snapshots = snapshots

        return all_sources, total_crawled, total_failed, diagnostics

    async def _crawl_parallel(
        self, url_list: list[str], url_metadata: dict[str, dict[str, Any]]
    ) -> tuple[list[SourceNode], int, int, CrawlDiagnostics]:
        """
        Parallel crawling with domain batching (Crawl4AI-enhanced).

        Features:
        - Domain-batched crawling for session reuse
        - Zone-aware configuration per domain
        - Comprehensive diagnostics
        """
        sources = []
        diagnostics = CrawlDiagnostics()
        diagnostics.discovered = len(url_list)

        # Create parallel crawler
        crawler = ParallelCrawler(
            max_concurrent=self.config.max_concurrent_crawls,
            headless=True,
            timeout_per_url=self.config.crawl_timeout * 1000,
        )

        # Crawl all URLs in parallel with domain batching
        log.info(f"Parallel crawling with {self.config.max_concurrent_crawls} concurrent connections...")
        batch_result = await crawler.crawl_many(url_list, diagnostics=diagnostics)

        # Convert results to SourceNodes
        for result in batch_result.results:
            if result.success and result.markdown and len(result.markdown) > 200:
                domain = urlparse(result.url).netloc.replace("www.", "")
                zone = get_zone_for_domain(domain) if self.config.use_zone_config else SignalZone.GRASSROOTS

                # Get original metadata
                meta = url_metadata.get(result.url, {})

                # Create SourceNode
                source = SourceNode(
                    id=SourceId(),
                    url=result.url,
                    title=result.title or meta.get("title") or domain,
                    origin=meta.get("source_name") or domain,
                    source_type=_classify_source_type(result.url, domain),
                    signal_zone=zone,
                    content_markdown=result.markdown,
                )

                # Preserve API metadata
                source.metadata = {
                    "relevance_score": meta.get("relevance_score", 0),
                    "snippet": meta.get("snippet", ""),
                    "api_source": meta.get("api_source", ""),
                    "source_name": meta.get("source_name", ""),
                    "published_at": meta.get("published_at"),
                    "zone": zone.value,
                    "crawl_time_ms": getattr(result, "crawl_time_ms", 0),
                }

                sources.append(source)

                # Note: diagnostics already recorded in parallel_crawler._crawl_single()

                api_src = meta.get("api_source", "")
                log.info(f"[{len(sources)}] {domain} [{zone.value}] via {api_src} ({len(result.markdown):,} chars)")
            # Note: drops already recorded in parallel_crawler._crawl_single()

        # Show diagnostics summary
        if self.config.show_diagnostics:
            log.info(f"{diagnostics.report()}")

        crawled = diagnostics.crawled
        failed = diagnostics.total_dropped

        log.info(f"CRAWL COMPLETE: {crawled} success, {failed} failed, yield={diagnostics.yield_rate():.1%}")
        return sources, crawled, failed, diagnostics

    async def _crawl_sequential(
        self, url_list: list[str], url_metadata: dict[str, dict[str, Any]]
    ) -> tuple[list[SourceNode], int, int, None]:
        """Legacy sequential crawling (fallback)."""
        sources = []
        crawled = 0
        failed = 0

        async with ContentCrawler() as crawler:
            for url in url_list:
                meta = url_metadata.get(url, {})
                domain = meta.get("domain", urlparse(url).netloc)

                try:
                    result = await crawler.crawl(url)

                    if result.success and result.markdown and len(result.markdown) > 200:
                        source = crawler.result_to_source_node(result)
                        if source:
                            source.metadata = source.metadata or {}
                            source.metadata["relevance_score"] = meta.get("relevance_score", 0)
                            source.metadata["snippet"] = meta.get("snippet", "")
                            source.metadata["api_source"] = meta.get("api_source", "")
                            source.metadata["source_name"] = meta.get("source_name", "")
                            source.metadata["published_at"] = meta.get("published_at")

                            if not source.title or source.title == domain:
                                source.title = meta.get("title") or source.title

                            if meta.get("source_name") and meta["source_name"] != domain:
                                source.origin = meta["source_name"]

                            sources.append(source)
                            crawled += 1
                            api_src = meta.get("api_source", "")
                            log.info(f"[{crawled}] {domain} via {api_src} ({len(result.markdown):,} chars)")
                    else:
                        failed += 1

                except Exception as e:
                    failed += 1
                    log.warning(f"Crawl failed: {domain} - {e}")
                    log.info(f"{domain}: Failed - {e}")

        log.info(f"CRAWL COMPLETE: {crawled} success, {failed} failed")
        return sources, crawled, failed, None

    async def _crawl_social_with_snapshots(
        self, url_list: list[str], url_metadata: dict[str, dict[str, Any]]
    ) -> tuple[list[SourceNode], int, int, list[PageSnapshot]]:
        """
        Crawl social URLs using PageSnapshotter for better JavaScript rendering.

        Social platforms (Twitter, LinkedIn, YouTube) often have dynamic content
        that requires proper JavaScript execution and longer wait times.

        Returns (sources, crawled_count, failed_count, snapshots).
        """
        from pathlib import Path

        sources = []
        snapshots = []
        crawled = 0
        failed = 0

        if not url_list:
            return sources, crawled, failed, snapshots

        log.info(f"SOCIAL SNAPSHOT: Capturing {len(url_list)} social URLs with PageSnapshotter")

        # Configure snapshot capture
        output_dir = None
        if self.config.social_snapshot_output_dir:
            output_dir = Path(self.config.social_snapshot_output_dir)
            output_dir.mkdir(parents=True, exist_ok=True)

        snapshot_config = PageSnapshotConfig(
            capture_screenshot=self.config.social_snapshot_screenshot,
            capture_html=True,
            capture_pdf=False,
            capture_mhtml=False,
            delay_before_capture=self.config.social_snapshot_delay,
            wait_for_images=True,
            output_dir=output_dir,
        )

        async with PageSnapshotter() as snapshotter:
            for url in url_list:
                domain = urlparse(url).netloc.replace("www.", "")
                meta = url_metadata.get(url, {})

                try:
                    # Capture snapshot with JavaScript rendering
                    snapshot = await snapshotter.capture(url, snapshot_config)
                    snapshots.append(snapshot)

                    # Extract content from snapshot
                    content = snapshot.html_content or ""

                    # Convert HTML to markdown-like text for extraction
                    # Strip HTML tags for basic text extraction
                    import re
                    text_content = re.sub(r"<script[^>]*>.*?</script>", "", content, flags=re.DOTALL | re.IGNORECASE)
                    text_content = re.sub(r"<style[^>]*>.*?</style>", "", text_content, flags=re.DOTALL | re.IGNORECASE)
                    text_content = re.sub(r"<[^>]+>", " ", text_content)
                    text_content = re.sub(r"\s+", " ", text_content).strip()

                    if len(text_content) < 100:
                        log.info(f"  {domain}: Too little content ({len(text_content)} chars), skipping")
                        failed += 1
                        continue

                    # Determine zone for social content
                    zone = SignalZone.GRASSROOTS  # Social content is grassroots by default

                    # Create SourceNode
                    source = SourceNode(
                        id=SourceId(),
                        url=url,
                        title=snapshot.page_title or meta.get("title") or domain,
                        origin=meta.get("source_name") or domain,
                        source_type=SourceType.SOCIAL,
                        signal_zone=zone,
                        content_markdown=text_content[:self.config.max_content_chars],
                    )

                    # Add metadata
                    source.metadata = {
                        "relevance_score": meta.get("relevance_score", 0),
                        "snippet": meta.get("snippet", ""),
                        "api_source": meta.get("api_source", ""),
                        "source_name": meta.get("source_name", ""),
                        "published_at": meta.get("published_at"),
                        "zone": zone.value,
                        "captured_via": "page_snapshot",
                        "has_screenshot": snapshot.screenshot_b64 is not None,
                        "content_hash": snapshot.content_hash,
                    }

                    sources.append(source)
                    crawled += 1

                    screenshot_note = " (with screenshot)" if snapshot.screenshot_b64 else ""
                    log.info(f"  {domain}: Captured{screenshot_note} ({len(text_content):,} chars)")

                except Exception as e:
                    failed += 1
                    log.warning(f"  {domain}: Snapshot failed - {e}")

        log.info(f"SOCIAL SNAPSHOT COMPLETE: {crawled} captured, {failed} failed")
        return sources, crawled, failed, snapshots

    async def _extract_ideas(
        self, sources: list[SourceNode], topic: str
    ) -> list[IdeaNode]:
        """
        Extract ideas from sources using LLM.

        When use_hybrid_extraction=True (default):
        - Pre-filters content using HybridExtractor (CSS → Regex → Cosine)
        - Extracts structured data (quotes, stats, citations) without LLM
        - Only sends relevant chunks to LLM, reducing token usage
        """
        log.info(f"EXTRACTION START: {len(sources)} sources to process")
        all_ideas = []
        total_tokens_saved = 0

        extraction_config = ExtractionConfig(
            provider=self.config.llm_provider,
            api_token=self.config.llm_api_key,
            max_claims_per_source=self.config.max_ideas_per_source,
            chunk_token_threshold=self.config.chunk_token_threshold,
        )
        extractor = IdeaExtractor(extraction_config)

        # Create hybrid extractor if enabled
        hybrid_extractor = None
        if self.config.use_hybrid_extraction:
            hybrid_extractor = HybridExtractor(
                topic=topic,
                min_relevance=self.config.hybrid_min_relevance,
            )
            log.info(f"Using hybrid extraction (pre-LLM filtering enabled)")

        for i, source in enumerate(sources):
            if not source.content_markdown:
                log.debug(f"[{i+1}/{len(sources)}] {source.origin}: No content, skipping")
                continue

            # Small delay between sources (Groq limiter handles rate limiting)
            if i > 0:
                await asyncio.sleep(1)

            content = source.content_markdown
            original_len = len(content)
            pre_extracted: QuickExtraction | None = None

            # Hybrid extraction: pre-filter and extract structured data
            if hybrid_extractor:
                pre_extracted = hybrid_extractor.extract(content, url=source.url)
                total_tokens_saved += pre_extracted.tokens_saved

                # Use filtered content if available
                if pre_extracted.relevant_chunks:
                    content = pre_extracted.content or "\n\n".join(pre_extracted.relevant_chunks)
                    log.debug(f"  Hybrid: {original_len} -> {len(content)} chars, saved ~{pre_extracted.tokens_saved} tokens")

                # Skip LLM if hybrid extraction got enough data
                if not pre_extracted.needs_llm and pre_extracted.quotes:
                    # Convert quotes directly to ideas (fast path)
                    quick_ideas = self._quick_ideas_from_extraction(pre_extracted, source, topic)
                    all_ideas.extend(quick_ideas)
                    log.info(f"{source.origin}: {len(quick_ideas)} ideas (quick extraction)")
                    continue

            # Limit content length to avoid rate limits
            if len(content) > self.config.max_content_chars:
                content = content[:self.config.max_content_chars]
                log.info(f"(Truncated {source.origin} from {original_len:,} to {self.config.max_content_chars:,} chars)")

            log.info(f"[{i+1}/{len(sources)}] EXTRACT: {source.origin}")
            log.debug(f"  URL: {source.url}")
            log.debug(f"  Content: {original_len} chars -> {len(content)} chars")

            try:
                result = await extractor.extract(
                    content=content,
                    source_id=source.id,
                    topic=topic,
                    pre_extracted=pre_extracted,  # Pass pre-extracted data
                )

                for idea in result.ideas:
                    # Ensure proper ID
                    if not idea.id:
                        idea.id = IdeaId()
                    all_ideas.append(idea)

                log.info(f"  Result: {len(result.ideas)} ideas extracted")
                for j, idea in enumerate(result.ideas[:3]):  # Log first 3 ideas
                    log.debug(f"  Idea {j+1}: {idea.claim[:100]}...")

                log.info(f"{source.origin}: {len(result.ideas)} ideas")

            except Exception as e:
                log.error(f"  FAILED: {e}")
                log.info(f"{source.origin}: Extraction failed - {e}")

        if hybrid_extractor and total_tokens_saved > 0:
            log.info(f"Total tokens saved by hybrid extraction: ~{total_tokens_saved:,}")

        log.info(f"EXTRACTION COMPLETE: {len(all_ideas)} total ideas extracted")
        return all_ideas

    def _quick_ideas_from_extraction(
        self, extraction: QuickExtraction, source: SourceNode, topic: str
    ) -> list[IdeaNode]:
        """Convert quick extraction results directly to IdeaNodes (no LLM needed)."""
        ideas = []

        # Convert quotes to ideas
        for quote in extraction.quotes[:5]:  # Limit to 5 quotes
            idea = IdeaNode(
                id=IdeaId(),
                claim=quote.strip('"'),
                source_ids=[source.id],
                stance_distribution={Stance.NEUTRAL: 1.0},
            )
            idea.metadata = {
                "extraction_method": "hybrid_quick",
                "has_percentage": bool(extraction.percentages),
                "citation_count": len(extraction.citations),
            }
            ideas.append(idea)

        return ideas

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
            summary = await self.llm_client.complete(prompt, system_prompt="You are a research analyst. Be concise and factual.")
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
            generated_at=datetime.now(timezone.utc),  # noqa: UP017
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
