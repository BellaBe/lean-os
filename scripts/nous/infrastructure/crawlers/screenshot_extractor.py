"""
Screenshot-based Content Extraction

For sites that block traditional scraping (Reuters, Bloomberg, WSJ, etc.),
this module captures screenshots and uses LLM vision to extract content.

Features:
- Human-like delays with jitter
- Screenshot capture with PageSnapshotter
- LLM-based content extraction from screenshots
- Fallback for paywalled/blocked sites
"""

import asyncio
import logging
import random
from dataclasses import dataclass, field
from datetime import UTC, datetime
from urllib.parse import urlparse

from ...domain import SourceType
from .page_snapshot import PageSnapshot, PageSnapshotConfig, PageSnapshotter
from .search_api import SCREENSHOT_FALLBACK_SITES, APISearchResult

log = logging.getLogger("nous.screenshot")


@dataclass
class HumanBehaviorConfig:
    """Configuration for human-like crawling behavior."""

    # Delay between requests (seconds)
    min_delay: float = 2.0
    max_delay: float = 5.0

    # Extra delay for same domain (seconds)
    same_domain_delay: float = 3.0

    # Jitter range (percentage of delay)
    jitter_percent: float = 0.3

    # Random pause probability (1-10% chance of longer pause)
    random_pause_chance: float = 0.05
    random_pause_min: float = 5.0
    random_pause_max: float = 15.0

    # Viewport randomization
    viewport_widths: list[int] = field(
        default_factory=lambda: [1280, 1366, 1440, 1536, 1920]
    )
    viewport_heights: list[int] = field(
        default_factory=lambda: [720, 768, 800, 864, 900, 1080]
    )

    def get_delay(self, same_domain: bool = False) -> float:
        """Calculate a human-like delay with jitter."""
        base = random.uniform(self.min_delay, self.max_delay)

        if same_domain:
            base += self.same_domain_delay

        # Add jitter
        jitter = base * random.uniform(-self.jitter_percent, self.jitter_percent)
        delay = base + jitter

        # Random long pause
        if random.random() < self.random_pause_chance:
            delay += random.uniform(self.random_pause_min, self.random_pause_max)
            log.debug(f"Taking a random pause, total delay: {delay:.1f}s")

        return max(0.5, delay)

    def get_random_viewport(self) -> tuple[int, int]:
        """Get a random viewport size."""
        return (
            random.choice(self.viewport_widths),
            random.choice(self.viewport_heights),
        )


@dataclass
class ExtractedArticle:
    """Article extracted from screenshot via LLM."""

    title: str
    url: str | None
    snippet: str
    source_name: str
    extracted_at: datetime = field(default_factory=lambda: datetime.now(UTC))


@dataclass
class ScreenshotExtractionResult:
    """Result of screenshot-based extraction."""

    url: str
    screenshot: PageSnapshot | None
    articles: list[ExtractedArticle]
    success: bool
    error: str | None = None


class ScreenshotExtractor:
    """
    Extracts content from screenshot-only sites using LLM vision.

    Designed for sites that:
    - Block traditional web scraping
    - Discontinued RSS feeds (Reuters, etc.)
    - Require JavaScript rendering
    - Have aggressive anti-bot measures

    Uses human-like behavior to avoid detection:
    - Random delays between requests
    - Viewport randomization
    - Session-like browsing patterns
    """

    def __init__(
        self,
        llm_provider: str = "groq/llama-3.2-90b-vision-preview",
        behavior_config: HumanBehaviorConfig | None = None,
    ) -> None:
        self.llm_provider = llm_provider
        self.behavior = behavior_config or HumanBehaviorConfig()
        self._last_domain: str | None = None
        self._last_request_time: datetime | None = None
        self._snapshotter: PageSnapshotter | None = None

    async def _ensure_snapshotter(self) -> PageSnapshotter:
        """Get or create snapshotter instance."""
        if self._snapshotter is None:
            self._snapshotter = PageSnapshotter()
            await self._snapshotter._get_crawler()
        return self._snapshotter

    async def close(self) -> None:
        """Close the snapshotter."""
        if self._snapshotter:
            await self._snapshotter.close()
            self._snapshotter = None

    async def __aenter__(self) -> "ScreenshotExtractor":
        await self._ensure_snapshotter()
        return self

    async def __aexit__(self, *args) -> None:
        await self.close()

    async def _human_delay(self, url: str) -> None:
        """Apply human-like delay before request."""
        domain = urlparse(url).netloc
        same_domain = domain == self._last_domain

        delay = self.behavior.get_delay(same_domain)

        if delay > 0:
            log.debug(f"Human-like delay: {delay:.1f}s before {domain}")
            await asyncio.sleep(delay)

        self._last_domain = domain
        self._last_request_time = datetime.now(UTC)

    async def extract_from_url(
        self,
        url: str,
        query: str | None = None,
        max_retries: int = 2,
    ) -> ScreenshotExtractionResult:
        """
        Capture screenshot and extract content using LLM vision.

        Args:
            url: URL to capture
            query: Optional query to filter extracted content
            max_retries: Number of retries on navigation/timeout errors

        Returns:
            ScreenshotExtractionResult with extracted articles
        """
        last_error = None

        for attempt in range(max_retries + 1):
            # Human-like delay (longer on retry)
            await self._human_delay(url)
            if attempt > 0:
                retry_delay = 2.0 * attempt  # Exponential backoff
                log.info(
                    f"Retry {attempt}/{max_retries} for {url}, waiting {retry_delay}s..."
                )
                await asyncio.sleep(retry_delay)

            try:
                snapshotter = await self._ensure_snapshotter()

                # Random viewport
                width, height = self.behavior.get_random_viewport()

                config = PageSnapshotConfig(
                    capture_screenshot=True,
                    capture_html=True,
                    full_page_screenshot=True,
                    delay_before_capture=3.0,  # Longer wait for content to load
                    wait_for_images=False,  # Don't wait for images - we only need text
                )

                log.info(f"Capturing screenshot: {url}")
                snapshot = await snapshotter.capture(url, config)

                if not snapshot.screenshot_b64:
                    return ScreenshotExtractionResult(
                        url=url,
                        screenshot=snapshot,
                        articles=[],
                        success=False,
                        error="No screenshot captured",
                    )

                # Extract articles using LLM vision
                articles = await self._extract_with_llm(
                    snapshot.screenshot_b64,
                    url,
                    query,
                )

                return ScreenshotExtractionResult(
                    url=url,
                    screenshot=snapshot,
                    articles=articles,
                    success=True,
                )

            except Exception as e:
                error_msg = str(e).lower()
                last_error = str(e)

                # Retryable errors: navigation, timeout, context destroyed
                is_retryable = any(
                    msg in error_msg
                    for msg in [
                        "navigation",
                        "context was destroyed",
                        "timeout",
                        "target closed",
                        "connection closed",
                        "frame was detached",
                    ]
                )

                if is_retryable and attempt < max_retries:
                    log.warning(f"Retryable error for {url}: {e}")
                    # Reset snapshotter on navigation errors
                    if "context" in error_msg or "navigation" in error_msg:
                        await self.close()
                    continue
                else:
                    log.error(f"Screenshot extraction failed for {url}: {e}")
                    break

        return ScreenshotExtractionResult(
            url=url,
            screenshot=None,
            articles=[],
            success=False,
            error=last_error,
        )

    async def _extract_with_llm(
        self,
        screenshot_b64: str,
        source_url: str,
        query: str | None = None,
    ) -> list[ExtractedArticle]:
        """Extract articles from screenshot using LLM vision."""
        try:
            import litellm
        except ImportError:
            log.error("litellm not installed")
            return []

        domain = urlparse(source_url).netloc.replace("www.", "")

        prompt = f"""Analyze this screenshot of {domain} and extract the visible news headlines/articles.

For each article you can see, extract:
1. Title/Headline (exact text)
2. Brief summary if visible (1-2 sentences)

{"Focus on articles related to: " + query if query else ""}

Return as JSON array:
[
  {{"title": "...", "snippet": "..."}},
  ...
]

Only include articles you can clearly read. If you can't see any articles, return empty array [].
Return ONLY the JSON array, no other text."""

        try:
            response = await litellm.acompletion(
                model=self.llm_provider,
                messages=[
                    {
                        "role": "user",
                        "content": [
                            {"type": "text", "text": prompt},
                            {
                                "type": "image_url",
                                "image_url": {
                                    "url": f"data:image/png;base64,{screenshot_b64}"
                                },
                            },
                        ],
                    }
                ],
                max_tokens=2000,
            )

            content = response.choices[0].message.content.strip()

            # Parse JSON response
            import json

            # Handle markdown code blocks
            if content.startswith("```"):
                content = content.split("```")[1]
                if content.startswith("json"):
                    content = content[4:]
                content = content.strip()

            articles_data = json.loads(content)

            articles = []
            for item in articles_data:
                if isinstance(item, dict) and item.get("title"):
                    articles.append(
                        ExtractedArticle(
                            title=item["title"],
                            url=None,  # Can't get URLs from screenshot
                            snippet=item.get("snippet", ""),
                            source_name=domain,
                        )
                    )

            log.info(f"Extracted {len(articles)} articles from {domain} screenshot")
            return articles

        except Exception as e:
            log.error(f"LLM extraction failed: {e}")
            return []

    async def extract_from_fallback_sites(
        self,
        query: str,
        sites: dict[str, str] | None = None,
    ) -> list[APISearchResult]:
        """
        Extract content from all fallback sites (Reuters, Bloomberg, etc.).

        Args:
            query: Search query to filter content
            sites: Override sites dict (default: SCREENSHOT_FALLBACK_SITES)

        Returns:
            List of APISearchResult from all sites
        """
        sites = sites or SCREENSHOT_FALLBACK_SITES
        all_results: list[APISearchResult] = []

        print(f"  → Screenshot: Checking {len(sites)} blocked sites...")

        for site_name, url in sites.items():
            result = await self.extract_from_url(url, query)

            if result.success:
                for article in result.articles:
                    # Check if article matches query
                    query_lower = query.lower()
                    text = f"{article.title} {article.snippet}".lower()
                    keywords = [k for k in query_lower.split() if len(k) > 2]
                    matches = sum(1 for kw in keywords if kw in text)

                    if matches > 0:
                        all_results.append(
                            APISearchResult(
                                title=article.title,
                                url=url,  # Use section URL since we don't have article URLs
                                snippet=article.snippet,
                                source="screenshot",
                                source_name=article.source_name.title(),
                                published_at=article.extracted_at,
                                relevance_score=(
                                    min(1.0, matches / len(keywords))
                                    if keywords
                                    else 0.5
                                ),
                                source_type=SourceType.NEWS,
                                metadata={"extraction_method": "screenshot_llm"},
                            )
                        )

        print(f"    ✓ Screenshot: Found {len(all_results)} matching articles")
        log.info(
            f"Screenshot extraction: {len(all_results)} results from {len(sites)} sites"
        )

        return all_results


async def extract_fallback_news(
    query: str,
    llm_provider: str = "groq/llama-3.2-90b-vision-preview",
) -> list[APISearchResult]:
    """
    Convenience function to extract news from blocked sites.

    Args:
        query: Search query
        llm_provider: Vision LLM to use

    Returns:
        List of APISearchResult
    """
    async with ScreenshotExtractor(llm_provider=llm_provider) as extractor:
        return await extractor.extract_from_fallback_sites(query)
