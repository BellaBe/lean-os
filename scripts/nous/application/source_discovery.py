"""
Source Discovery Use Case

Orchestrates the process of discovering and extracting sources for a topic.
Pipeline: Topic -> SERP -> Crawl Content -> Extract Ideas
"""

from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path

from ..domain import (
    IdeaId,
    IdeaNode,
    SearchResponse,
    SourceNode,
    Stance,
)
from ..infrastructure.crawlers import (
    ContentCrawler,
    Crawl4AISerpCrawler,
    FileSchemaStore,
    SchemaManager,
    SerpConfig,
    SerpCrawler,
)
from ..infrastructure.llm import (
    Crawl4AISchemaGenerator,
    DirectLLMClient,
    IdeaExtractor,
    LLMConfig,
)


@dataclass
class DiscoveryConfig:
    """Configuration for source discovery."""

    max_search_results: int = 10
    max_concurrent_crawls: int = 5
    extract_ideas: bool = True
    max_ideas_per_source: int = 5
    schema_cache_path: Path = field(default_factory=lambda: Path.home() / ".nous" / "schemas")
    llm_config: LLMConfig | None = None


@dataclass
class DiscoveryResult:
    """Result of a source discovery operation."""

    topic: str
    search_response: SearchResponse
    sources: list[SourceNode]
    ideas: list[IdeaNode]
    failed_urls: list[str]
    discovered_at: datetime = field(default_factory=datetime.utcnow)
    duration_seconds: float = 0.0


class SourceDiscoveryUseCase:
    """
    Discover sources for a topic using web search and content extraction.

    Pipeline:
    1. Search for topic using SERP crawler
    2. Crawl discovered URLs for content
    3. Extract ideas from content (optional, uses LLM)
    """

    def __init__(
        self,
        serp_crawler: SerpCrawler | None = None,
        content_crawler: ContentCrawler | None = None,
        idea_extractor: IdeaExtractor | None = None,
        config: DiscoveryConfig | None = None,
    ):
        self.config = config or DiscoveryConfig()
        self.serp_crawler = serp_crawler
        self.content_crawler = content_crawler
        self.idea_extractor = idea_extractor
        self._initialized = False

    async def _ensure_initialized(self) -> None:
        """Lazy initialization of crawlers."""
        if self._initialized:
            return

        # Initialize SERP crawler with schema management
        if self.serp_crawler is None:
            schema_store = FileSchemaStore(self.config.schema_cache_path)

            # Only create generator if LLM config provided
            generator = None
            if self.config.llm_config:
                generator = Crawl4AISchemaGenerator(self.config.llm_config)

            schema_manager = SchemaManager(
                store=schema_store,
                generator=generator,
            )

            self.serp_crawler = Crawl4AISerpCrawler(
                schema_manager=schema_manager,
                use_fallback_schemas=True,  # Use pre-defined schemas
            )

        # Initialize content crawler
        if self.content_crawler is None:
            self.content_crawler = ContentCrawler()

        # Initialize idea extractor
        if self.idea_extractor is None and self.config.extract_ideas:
            if self.config.llm_config:
                llm_client = DirectLLMClient(self.config.llm_config)
                self.idea_extractor = IdeaExtractor(llm_client)

        self._initialized = True

    async def discover(
        self,
        topic: str,
        search_config: SerpConfig | None = None,
    ) -> DiscoveryResult:
        """
        Discover sources and ideas for a topic.

        Args:
            topic: Topic to investigate
            search_config: Optional search configuration

        Returns:
            DiscoveryResult with sources and extracted ideas
        """
        start_time = datetime.utcnow()
        await self._ensure_initialized()

        search_config = search_config or SerpConfig(
            num_results=self.config.max_search_results,
        )

        # Step 1: Search for topic
        assert self.serp_crawler is not None, "SERP crawler not initialized"
        search_response = await self.serp_crawler.search(topic, search_config)

        # Step 2: Crawl discovered URLs
        urls_to_crawl = [r.url for r in search_response.results]

        assert self.content_crawler is not None, "Content crawler not initialized"
        async with self.content_crawler as crawler:
            crawl_results = await crawler.crawl_many(
                urls_to_crawl,
                max_concurrent=self.config.max_concurrent_crawls,
            )

        # Step 3: Convert to source nodes
        sources: list[SourceNode] = []
        failed_urls: list[str] = []

        for result in crawl_results:
            if result.success:
                source = crawler.result_to_source_node(result)
                if source:
                    sources.append(source)
            else:
                failed_urls.append(result.url)

        # Step 4: Extract ideas (if configured)
        ideas: list[IdeaNode] = []

        if self.idea_extractor and self.config.extract_ideas:
            ideas = await self._extract_ideas_from_sources(topic, sources)

        duration = (datetime.utcnow() - start_time).total_seconds()

        return DiscoveryResult(
            topic=topic,
            search_response=search_response,
            sources=sources,
            ideas=ideas,
            failed_urls=failed_urls,
            duration_seconds=duration,
        )

    async def _extract_ideas_from_sources(
        self,
        topic: str,
        sources: list[SourceNode],
    ) -> list[IdeaNode]:
        """Extract ideas from all sources."""
        ideas: list[IdeaNode] = []

        for source in sources:
            if not source.content_markdown:
                continue

            try:
                assert self.idea_extractor is not None
                raw_ideas = await self.idea_extractor.extract(
                    source.content_markdown,
                    topic,
                    max_ideas=self.config.max_ideas_per_source,
                )

                for raw in raw_ideas:
                    idea = IdeaNode(
                        id=IdeaId(),
                        claim=raw.get("claim", ""),
                        stance_distribution={
                            Stance.SUPPORT: 1.0 if raw.get("stance") == "support" else 0.0,
                            Stance.OPPOSE: 1.0 if raw.get("stance") == "oppose" else 0.0,
                            Stance.NEUTRAL: 1.0 if raw.get("stance") == "neutral" else 0.0,
                        },
                        source_ids=[source.id],
                        behavioral_triggers=raw.get("behavioral_triggers", []),
                    )
                    ideas.append(idea)
                    source.ideas_contributed.append(idea.id)

            except Exception as e:
                print(f"Failed to extract ideas from {source.url}: {e}")

        return ideas

    async def close(self) -> None:
        """Clean up resources."""
        if self.serp_crawler is not None and hasattr(self.serp_crawler, "close"):
            await self.serp_crawler.close()
        if self.content_crawler is not None and hasattr(self.content_crawler, "close"):
            await self.content_crawler.close()


async def quick_discover(
    topic: str,
    num_results: int = 5,
    llm_provider: str | None = None,
    extract_ideas: bool = False,
) -> DiscoveryResult:
    """
    Quick discovery function for exploration.

    Args:
        topic: Topic to search
        num_results: Number of search results
        llm_provider: LLM provider string (e.g., "ollama/llama3.3", "openai/gpt-4o")
        extract_ideas: Whether to extract ideas (requires LLM)

    Returns:
        DiscoveryResult
    """
    llm_config = None
    if llm_provider or extract_ideas:
        llm_config = LLMConfig.from_env(llm_provider)

    config = DiscoveryConfig(
        max_search_results=num_results,
        extract_ideas=extract_ideas,
        llm_config=llm_config,
    )

    use_case = SourceDiscoveryUseCase(config=config)

    try:
        return await use_case.discover(topic)
    finally:
        await use_case.close()
