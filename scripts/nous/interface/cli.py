#!/usr/bin/env python3
"""
Nous CLI - Command Line Interface for exploration

Usage:
    python -m nous.interface.cli search "AI regulation" --results 5
    python -m nous.interface.cli discover "Bitcoin ETF" --ideas
"""

import argparse
import asyncio
import json
import sys
from typing import Any


def format_search_result(result: Any, index: int) -> str:
    """Format a single search result for display."""
    return f"""
{index}. {result.title}
   URL: {result.url}
   {result.snippet[:200]}...
   {f"Date: {result.date}" if result.date else ""}
"""


def format_source(source: Any) -> str:
    """Format a source node for display."""
    return f"""
📰 {source.title}
   Type: {source.source_type.value} | Zone: {source.signal_zone.value}
   Origin: {source.origin}
   URL: {source.url}
   Content: {len(source.content_markdown or '')} chars
"""


def format_idea(idea: Any) -> str:
    """Format an idea node for display."""
    stance = max(idea.stance_distribution.items(), key=lambda x: x[1])[0].value
    return f"""
💡 {idea.claim}
   Stance: {stance}
   Triggers: {', '.join(idea.behavioral_triggers) or 'None'}
"""


async def cmd_search(args: Any) -> None:
    """Execute search command."""
    from ..infrastructure.crawlers import Crawl4AISerpCrawler, SerpConfig

    print(f"\n🔍 Searching for: {args.query}")
    print("=" * 60)

    config = SerpConfig(
        num_results=args.results,
        time_range=args.time,
    )

    async with Crawl4AISerpCrawler(use_fallback_schemas=True) as crawler:
        response = await crawler.search(args.query, config)

    print(f"\nFound {len(response.results)} results from {response.source}")
    print("-" * 60)

    for i, result in enumerate(response.results, 1):
        print(format_search_result(result, i))

    if response.top_stories:
        print("\n📰 Top Stories:")
        for story in response.top_stories[:3]:
            print(f"   - {story.get('title', 'N/A')}")

    if args.json:
        output = {
            "query": response.query,
            "source": response.source,
            "results": [
                {
                    "title": r.title,
                    "url": r.url,
                    "snippet": r.snippet,
                    "position": r.position,
                }
                for r in response.results
            ],
        }
        print("\n" + json.dumps(output, indent=2))


async def cmd_discover(args: Any) -> None:
    """Execute discover command (full pipeline)."""
    from ..application import quick_discover

    print(f"\n🌐 Discovering sources for: {args.topic}")
    print("=" * 60)

    result = await quick_discover(
        topic=args.topic,
        num_results=args.results,
        llm_provider=args.llm if args.ideas else None,
        extract_ideas=args.ideas,
    )

    print(f"\n✅ Discovery completed in {result.duration_seconds:.1f}s")
    print(f"   Sources found: {len(result.sources)}")
    print(f"   Ideas extracted: {len(result.ideas)}")
    print(f"   Failed URLs: {len(result.failed_urls)}")

    print("\n📚 Sources:")
    print("-" * 60)
    for source in result.sources:
        print(format_source(source))

    if result.ideas:
        print("\n💭 Ideas:")
        print("-" * 60)
        for idea in result.ideas:
            print(format_idea(idea))

    if result.failed_urls:
        print(f"\n⚠️  Failed to crawl: {len(result.failed_urls)} URLs")

    if args.json:
        output = {
            "topic": result.topic,
            "duration_seconds": result.duration_seconds,
            "sources": [
                {
                    "title": s.title,
                    "url": s.url,
                    "type": s.source_type.value,
                    "zone": s.signal_zone.value,
                    "origin": s.origin,
                }
                for s in result.sources
            ],
            "ideas": [
                {
                    "claim": i.claim,
                    "stance": max(i.stance_distribution.items(), key=lambda x: x[1])[0].value,
                }
                for i in result.ideas
            ],
        }
        print("\n" + json.dumps(output, indent=2))


async def cmd_crawl(args: Any) -> None:
    """Crawl a single URL."""
    from ..infrastructure.crawlers import ContentCrawler

    print(f"\n🕷️  Crawling: {args.url}")
    print("=" * 60)

    async with ContentCrawler() as crawler:
        result = await crawler.crawl(args.url)

    if result.success:
        print("\n✅ Success")
        print(f"   Title: {result.title}")
        print(f"   Markdown length: {len(result.markdown)} chars")
        print(f"   Fit markdown length: {len(result.fit_markdown)} chars")
        print(f"   Links found: {len(result.links)}")
        print(f"   Images found: {len(result.images)}")

        if args.content:
            print("\n📝 Content (first 2000 chars):")
            print("-" * 60)
            content = result.fit_markdown or result.markdown
            print(content[:2000])
            if len(content) > 2000:
                print(f"\n... ({len(content) - 2000} more chars)")

        if args.json:
            output = {
                "url": result.url,
                "title": result.title,
                "markdown_length": len(result.markdown),
                "fit_markdown_length": len(result.fit_markdown),
                "links_count": len(result.links),
                "images_count": len(result.images),
            }
            print("\n" + json.dumps(output, indent=2))
    else:
        print(f"\n❌ Failed: {result.error}")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Nous - Noosphere Snapshot Engine CLI",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  nous search "AI regulation" --results 10
  nous discover "Bitcoin ETF" --ideas --llm ollama/llama3.3
  nous crawl https://example.com --content
        """,
    )

    subparsers = parser.add_subparsers(dest="command", help="Available commands")

    # Search command
    search_parser = subparsers.add_parser("search", help="Search for a topic")
    search_parser.add_argument("query", help="Search query")
    search_parser.add_argument("-n", "--results", type=int, default=10, help="Number of results")
    search_parser.add_argument("-t", "--time", choices=["d", "w", "m", "y"], help="Time range")
    search_parser.add_argument("--json", action="store_true", help="Output as JSON")

    # Discover command
    discover_parser = subparsers.add_parser("discover", help="Discover sources for a topic")
    discover_parser.add_argument("topic", help="Topic to investigate")
    discover_parser.add_argument("-n", "--results", type=int, default=5, help="Number of sources")
    discover_parser.add_argument(
        "--ideas", action="store_true", help="Extract ideas (requires LLM)"
    )
    discover_parser.add_argument("--llm", help="LLM provider (e.g., ollama/llama3.3)")
    discover_parser.add_argument("--json", action="store_true", help="Output as JSON")

    # Crawl command
    crawl_parser = subparsers.add_parser("crawl", help="Crawl a single URL")
    crawl_parser.add_argument("url", help="URL to crawl")
    crawl_parser.add_argument("--content", action="store_true", help="Show content preview")
    crawl_parser.add_argument("--json", action="store_true", help="Output as JSON")

    args = parser.parse_args()

    if args.command is None:
        parser.print_help()
        return

    # Run the appropriate command
    try:
        if args.command == "search":
            asyncio.run(cmd_search(args))
        elif args.command == "discover":
            asyncio.run(cmd_discover(args))
        elif args.command == "crawl":
            asyncio.run(cmd_crawl(args))
    except KeyboardInterrupt:
        print("\n\nInterrupted by user")
        sys.exit(1)
    except Exception as e:
        print(f"\n❌ Error: {e}")
        if "--debug" in sys.argv:
            raise
        sys.exit(1)


if __name__ == "__main__":
    main()
