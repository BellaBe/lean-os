#!/usr/bin/env python3
"""
Nous Example - Quick demonstration of source discovery

Run: python examples/quick_start.py
"""

import asyncio

# Add parent to path for local development
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).parent.parent))


async def example_search() -> Any:
    """Example: Simple search without idea extraction."""
    from nous.infrastructure.crawlers import Crawl4AISerpCrawler, SerpConfig

    print("\n" + "=" * 60)
    print("🔍 Example 1: Basic SERP Search")
    print("=" * 60)

    config = SerpConfig(num_results=5)

    async with Crawl4AISerpCrawler(use_fallback_schemas=True) as crawler:
        response = await crawler.search("AI regulation EU", config)

    print(f"\nFound {len(response.results)} results from {response.source}")
    for i, result in enumerate(response.results[:3], 1):
        print(f"\n{i}. {result.title}")
        print(f"   {result.url}")
        print(f"   {result.snippet[:100]}...")

    return response


async def example_crawl() -> Any:
    """Example: Crawl a single URL for content."""
    from nous.infrastructure.crawlers import ContentCrawler

    print("\n" + "=" * 60)
    print("🕷️  Example 2: Content Crawling")
    print("=" * 60)

    async with ContentCrawler() as crawler:
        result = await crawler.crawl("https://en.wikipedia.org/wiki/Artificial_intelligence")

    if result.success:
        print(f"\n✅ Successfully crawled: {result.title}")
        print(f"   Markdown: {len(result.markdown)} chars")
        print(f"   Fit markdown: {len(result.fit_markdown)} chars")
        print("\nFirst 500 chars of content:")
        print("-" * 40)
        print((result.fit_markdown or result.markdown)[:500])
    else:
        print(f"\n❌ Failed: {result.error}")

    return result


async def example_discover() -> Any:
    """Example: Full discovery pipeline (without LLM idea extraction)."""
    from nous import quick_discover

    print("\n" + "=" * 60)
    print("🌐 Example 3: Full Discovery Pipeline")
    print("=" * 60)

    result = await quick_discover(
        topic="Bitcoin ETF approval",
        num_results=3,
        extract_ideas=False,  # Set to True if you have LLM configured
    )

    print(f"\n✅ Discovery completed in {result.duration_seconds:.1f}s")
    print(f"   Sources: {len(result.sources)}")
    print(f"   Failed: {len(result.failed_urls)}")

    for source in result.sources:
        print(f"\n📰 {source.title}")
        print(f"   Type: {source.source_type.value}")
        print(f"   Zone: {source.signal_zone.value}")
        print(f"   Content: {len(source.content_markdown or '')} chars")

    return result


async def main() -> None:
    """Run all examples."""
    print("\n🌌 Nous - Noosphere Snapshot Engine")
    print("    Automated Knowledge Synthesis")

    try:
        # Example 1: Basic search
        await example_search()

        # Example 2: Content crawling
        await example_crawl()

        # Example 3: Full discovery
        await example_discover()

        print("\n" + "=" * 60)
        print("✨ All examples completed!")
        print("=" * 60)

    except ImportError as e:
        print(f"\n⚠️  Missing dependency: {e}")
        print("   Install with: pip install 'nous[all]'")
        print("   Or: pip install crawl4ai litellm")
    except Exception as e:
        print(f"\n❌ Error: {e}")
        raise


if __name__ == "__main__":
    asyncio.run(main())
