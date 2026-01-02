"""
Discovery stage for URL discovery.

Handles:
- Query augmentation and translation
- Multi-source search (RSS, arXiv, Reddit, DuckDuckGo)
- Site-specific searches (Twitter, LinkedIn, YouTube, YC)
- Domain expansion via URL seeding
"""

from __future__ import annotations

import asyncio
from typing import TYPE_CHECKING
from urllib.parse import urlparse

from ...infrastructure.crawlers.search_api import (
    APISearchResult,
    MultiSourceSearch,
    SearchAPIConfig,
)
from ...infrastructure.crawlers.url_seeder import (
    SeedingConfig,
    UrlSeeder,
    generate_site_queries,
)
from ...infrastructure.logging import get_structured_logger

if TYPE_CHECKING:
    from .base import PipelineContext

_log = get_structured_logger("nous.stages.discovery")


def _classify_source_type(url: str, domain: str):
    """Classify URL into source type based on domain and path."""
    from ...domain import SourceType

    url_lower = url.lower()
    domain_lower = domain.lower()

    # Domain-based detection
    if any(
        d in domain_lower
        for d in ["arxiv.org", "scholar.google", "researchgate", "pubmed"]
    ):
        return SourceType.ACADEMIC
    if any(
        d in domain_lower
        for d in ["reddit.com", "twitter.com", "x.com", "linkedin.com"]
    ):
        return SourceType.SOCIAL
    if any(
        d in domain_lower for d in ["github.com", "gitlab.com", "stackoverflow.com"]
    ):
        return SourceType.CODE
    if any(d in domain_lower for d in [".gov", "official", "government"]):
        return SourceType.OFFICIAL
    if any(
        d in domain_lower
        for d in ["medium.com", "substack.com", "wordpress.com", "blogspot"]
    ):
        return SourceType.BLOG
    if any(
        d in domain_lower
        for d in ["ycombinator", "producthunt", "techcrunch", "theverge"]
    ):
        return SourceType.NEWS

    # Path-based detection
    if any(
        p in url_lower
        for p in ["/research/", "/paper/", "/publication/", "/abstract/", ".pdf"]
    ):
        return SourceType.ACADEMIC
    if (
        any(p in url_lower for p in ["/blog/", "/posts/", "/article/"])
        and "news" not in domain_lower
    ):
        return SourceType.BLOG
    if any(
        p in url_lower for p in ["/forum/", "/thread/", "/discussion/", "/comments/"]
    ):
        return SourceType.FORUM
    if any(p in url_lower for p in ["/video/", "/watch/", "/embed/", "youtube.com"]):
        return SourceType.VIDEO

    return SourceType.NEWS


class DiscoveryStage:
    """
    Pipeline stage for URL discovery.

    Discovers URLs via multiple search APIs and optional domain expansion.
    """

    @property
    def name(self) -> str:
        return "discovery"

    async def execute(self, context: PipelineContext) -> PipelineContext:
        """
        Execute URL discovery.

        Populates context.discovered_urls and context.domains_searched.
        """
        _log.info("stage_start", stage=self.name, topic=context.topic)

        # Build queries (with translations if enabled)
        queries = await self._build_queries(context)
        context.queries = queries

        # Run discovery
        discovered = await self._search_all_sources(context, queries)
        context.discovered_urls = discovered

        # Domain expansion if enabled
        if context.config.expand_domains:
            expanded = await self._expand_domains(context, discovered)
            context.discovered_urls = expanded

        _log.info(
            "stage_complete",
            stage=self.name,
            urls_discovered=len(context.discovered_urls),
        )
        return context

    async def _build_queries(self, context: PipelineContext) -> list[str]:
        """Build list of search queries including translations."""
        queries = [context.topic]

        if context.config.translate_queries and context.config.target_languages:
            for lang in context.config.target_languages:
                if lang.lower() != "en":
                    translated = await self._translate_query(
                        context, context.topic, lang
                    )
                    if translated != context.topic:
                        queries.append(translated)
                        _log.info("query_translated", lang=lang, query=translated[:50])

        return queries

    async def _translate_query(
        self, context: PipelineContext, query: str, target_lang: str
    ) -> str:
        """Translate query to target language using LLM."""
        prompt = f"""Translate this search query to {target_lang}.
Return ONLY the translated text, nothing else.

Query: {query}"""

        try:
            response = await context.llm_client.complete(prompt)
            return response.strip()
        except Exception as e:
            _log.warning("translation_failed", lang=target_lang, error=str(e))
            return query

    async def _search_all_sources(
        self, context: PipelineContext, queries: list[str]
    ) -> list[dict]:
        """Search all configured sources for URLs."""
        api_config = SearchAPIConfig(
            max_results_per_provider=context.config.max_results_per_source,
            language="en",
            days_back=30,
            use_screenshot_fallback=context.config.use_screenshot_fallback,
            screenshot_llm_provider=context.config.screenshot_llm_provider,
        )
        search = MultiSourceSearch(api_config)

        all_results: list[APISearchResult] = []
        seen_urls: set[str] = set()

        for i, query in enumerate(queries):
            if i > 0:
                _log.debug("query_delay", seconds=5)
                await asyncio.sleep(5)

            region_info = (
                f" (region: {context.config.region})" if context.config.region else ""
            )
            _log.info(
                "searching",
                query=query[:50],
                sources=context.config.sources,
                region=region_info,
            )

            results = await search.search(
                query,
                sources=context.config.sources,
                max_results_per_source=context.config.max_results_per_source,
            )

            for result in results:
                if result.url not in seen_urls:
                    seen_urls.add(result.url)
                    all_results.append(result)

            scores = [r.relevance_score for r in results if r.relevance_score]
            avg_score = sum(scores) / len(scores) if scores else 0
            _log.info(
                "search_results", count=len(results), avg_relevance=f"{avg_score:.2f}"
            )

        # Site-specific searches
        if context.config.use_site_specific_search:
            site_results = await self._search_site_specific(context, search, seen_urls)
            all_results.extend(site_results)

        # Convert to dict format
        return self._convert_results(all_results)

    async def _search_site_specific(
        self,
        context: PipelineContext,
        search: MultiSourceSearch,
        seen_urls: set[str],
    ) -> list[APISearchResult]:
        """Search site-specific sources (social/tech)."""
        _log.info("searching_site_specific")
        results: list[APISearchResult] = []

        site_queries = generate_site_queries(
            context.topic,
            include_social=True,
            include_tech="tech" in context.topic.lower()
            or "startup" in context.topic.lower(),
        )

        for site_query in site_queries[:5]:
            try:
                site_results = await search.search(
                    site_query,
                    sources=["web"],
                    max_results_per_source=10,
                )
                for result in site_results:
                    if result.url not in seen_urls:
                        seen_urls.add(result.url)
                        results.append(result)
                if site_results:
                    _log.debug(
                        "site_search_results",
                        query=site_query[:40],
                        count=len(site_results),
                    )
            except Exception as e:
                _log.debug("site_search_failed", query=site_query[:30], error=str(e))

            await asyncio.sleep(0.5)

        return results

    def _convert_results(self, results: list[APISearchResult]) -> list[dict]:
        """Convert APISearchResult to dict format for pipeline."""
        all_urls = []
        for result in results:
            domain = urlparse(result.url).netloc.replace("www.", "")
            source_type = result.source_type or _classify_source_type(
                result.url, domain
            )

            all_urls.append(
                {
                    "url": result.url,
                    "title": result.title,
                    "snippet": result.snippet or "",
                    "domain": domain,
                    "relevance_score": result.relevance_score or 0,
                    "source_type": (
                        source_type.value
                        if hasattr(source_type, "value")
                        else str(source_type)
                    ),
                    "api_source": result.source,
                    "source_name": result.source_name or domain,
                    "published_at": (
                        result.published_at.isoformat() if result.published_at else None
                    ),
                }
            )

        return all_urls

    async def _expand_domains(
        self, context: PipelineContext, discovered_urls: list[dict]
    ) -> list[dict]:
        """Expand domains using URL seeding."""
        if not discovered_urls:
            return discovered_urls

        seen_urls = {u["url"] for u in discovered_urls}
        new_urls = list(discovered_urls)

        # Find domains to expand
        domain_counts: dict[str, int] = {}
        for url_data in discovered_urls:
            domain = url_data.get("domain", "")
            domain_counts[domain] = domain_counts.get(domain, 0) + 1

        # Seed from top domains
        top_domains = sorted(domain_counts.items(), key=lambda x: -x[1])[:5]
        context.domains_searched = [d[0] for d in top_domains]

        seeding_config = SeedingConfig(
            max_urls_per_domain=context.config.max_urls_per_domain,
            include_subdomains=False,
        )
        seeder = UrlSeeder(seeding_config)

        for domain, _ in top_domains:
            try:
                seeded = await seeder.seed_from_domain(domain, context.topic)
                for url_data in seeded:
                    if url_data.url not in seen_urls:
                        seen_urls.add(url_data.url)
                        new_urls.append(
                            {
                                "url": url_data.url,
                                "title": url_data.title or "",
                                "snippet": "",
                                "domain": domain,
                                "relevance_score": 0.5,
                                "source_type": "seeded",
                                "api_source": "seeder",
                                "source_name": domain,
                                "published_at": None,
                            }
                        )
                _log.debug("domain_expanded", domain=domain, new_urls=len(seeded))
            except Exception as e:
                _log.warning("domain_expansion_failed", domain=domain, error=str(e))

        _log.info(
            "expansion_complete", original=len(discovered_urls), total=len(new_urls)
        )
        return new_urls
