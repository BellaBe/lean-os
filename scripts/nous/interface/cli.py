#!/usr/bin/env python3
"""
Nous CLI - Command Line Interface for topic-aware web intelligence.

Primary command: snapshot - builds complete topic analysis

Usage:
    nous snapshot "AI regulation EU" --region de --translate --target-langs de,fr
    nous snapshot "climate tech" --sources news,academic --max-urls 30
"""

import argparse
import asyncio
import json
import logging
import os
import re
import sys
from datetime import datetime
from pathlib import Path
from typing import Any

from ..domain.entities import Snapshot
from ..infrastructure.llm.client import DirectLLMClient, LLMConfig

logger = logging.getLogger("nous.cli")



def generate_output_filename(topic: str, format: str = "md") -> str:
    """
    Generate output filename from topic and timestamp.

    Format: {topic_slug}_{YYYYMMDD_HHMMSS}.{format}
    Example: uae_ai_progress_2026_20260101_120530.md
    """
    # Slugify topic: lowercase, replace non-alphanumeric with underscore
    slug = re.sub(r'[^a-z0-9]+', '_', topic.lower())
    slug = re.sub(r'_+', '_', slug).strip('_')  # Remove duplicate/trailing underscores

    # Limit slug length
    if len(slug) > 50:
        slug = slug[:50].rstrip('_')

    # Add timestamp
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

    # Determine extension
    ext = "json" if format == "json" else "md"

    return f"{slug}_{timestamp}.{ext}"



def snapshot_to_dict(snapshot: Snapshot) -> dict:
    """Convert Snapshot to JSON-serializable dict."""
    return {
        "id": str(snapshot.id),
        "topic": snapshot.topic,
        "generated_at": snapshot.generated_at.isoformat(),
        "scope": {
            "time_range": snapshot.scope.time_range,
            "source_types": snapshot.scope.source_types,
            "domains_searched": snapshot.scope.domains_searched,
            "languages": snapshot.scope.languages,
        },
        "stats": {
            "urls_discovered": snapshot.stats.urls_discovered,
            "urls_crawled": snapshot.stats.urls_crawled,
            "urls_failed": snapshot.stats.urls_failed,
            "ideas_extracted": snapshot.stats.ideas_extracted,
            "avg_relevance_score": snapshot.stats.avg_relevance_score,
            "crawl_time_seconds": snapshot.stats.crawl_time_seconds,
        },
        "summary": snapshot.summary,
        "consensus_clusters": [
            {
                "representative_claim": c.representative_claim,
                "idea_count": c.idea_count,
                "source_count": c.source_count,
            }
            for c in snapshot.consensus_clusters
        ],
        "contention_zones": [
            {
                "representative_claim": c.representative_claim,
                "opposing_views": c.opposing_views,
            }
            for c in snapshot.contention_zones
        ],
        "sources": [
            {
                "id": str(s.id),
                "url": s.url,
                "title": s.title,
                "origin": s.origin,
                "source_type": s.source_type.value,
                "signal_zone": s.signal_zone.value,
            }
            for s in snapshot.sources
        ],
        "ideas": [
            {
                "id": str(i.id),
                "claim": i.claim,
                "stance": max(i.stance_distribution.items(), key=lambda x: x[1])[0].value
                if i.stance_distribution else "neutral",
            }
            for i in snapshot.ideas
        ],
    }


def format_snapshot_markdown(snapshot: Any) -> str:
    """Format snapshot as markdown report."""
    lines = [
        f"# Snapshot: {snapshot.topic}",
        "",
        f"**Generated:** {snapshot.generated_at.isoformat()}",
        f"**ID:** {snapshot.id}",
        "",
        "## Summary",
        "",
        snapshot.summary or "(No summary generated)",
        "",
        "## Stats",
        "",
        f"- URLs discovered: {snapshot.stats.urls_discovered}",
        f"- URLs crawled: {snapshot.stats.urls_crawled}",
        f"- Ideas extracted: {snapshot.stats.ideas_extracted}",
        f"- Time: {snapshot.stats.crawl_time_seconds}s",
        "",
    ]

    if snapshot.consensus_clusters:
        lines.append("## Consensus Points")
        lines.append("")
        for c in snapshot.consensus_clusters[:5]:
            lines.append(f"- {c.representative_claim} ({c.source_count} sources)")
        lines.append("")

    if snapshot.contention_zones:
        lines.append("## Contention Zones")
        lines.append("")
        for c in snapshot.contention_zones[:5]:
            lines.append(f"- {c.representative_claim}")
        lines.append("")

    if snapshot.sources:
        lines.append("## Top Sources")
        lines.append("")
        for s in snapshot.sources[:10]:
            lines.append(f"- [{s.title or s.origin}]({s.url})")
        lines.append("")

    return "\n".join(lines)


async def cmd_snapshot(args: Any) -> None:
    """Execute snapshot command - full topic analysis."""
    from ..application import SnapshotBuilder, SnapshotBuilderConfig

    # Build config from args
    config = SnapshotBuilderConfig(
        # Discovery
        use_screenshot_fallback=True,
        sources=args.sources.split(",") if args.sources else ["news", "academic", "social", "web"],
        max_urls=args.max_urls,
        max_results_per_source=args.max_per_source,

        # Region/Language
        region=args.region,
        regions=args.regions.split(",") if args.regions else None,
        target_languages=args.target_langs.split(",") if args.target_langs else None,
        translate_queries=args.translate,

        # Query augmentation
        augment_queries=not args.no_augment,
        max_query_variations=args.query_variations,

        # Filtering
        filter_relevance=not args.no_filter_urls,
        filter_ideas=not args.no_filter_ideas,
        relevance_threshold=args.relevance_threshold,
        idea_relevance_threshold=args.idea_threshold,

        # LLM
        llm_provider=args.llm,
        llm_api_key=args.llm_key or os.getenv("GROQ_API_KEY") or os.getenv("LLM_API_KEY"),

        # Analysis
        generate_summary=not args.no_summary,
        build_graph=not args.no_graph,
        consensus_threshold=args.consensus_threshold,

        # Parallel crawling (from Crawl4AI upgrade)
        max_concurrent_crawls=args.parallel,

        # Domain expansion via URL seeding
        use_domain_expansion=not args.no_expand,
    )

    llm_config = LLMConfig(
        provider=config.llm_provider,
        api_key=config.llm_api_key,
    )

    llm_client = DirectLLMClient(llm_config)

    builder = SnapshotBuilder(config, llm_client=llm_client)
    snapshot = await builder.build(args.topic)

    # Calculate zone distribution from sources
    zone_counts: dict[str, int] = {}
    for source in snapshot.sources:
        zone_name = source.signal_zone.name
        zone_counts[zone_name] = zone_counts.get(zone_name, 0) + 1

    # Generate filename from topic
    filename = generate_output_filename(args.topic, "md").replace(".md", "")

    # Create output directories
    reports_dir = Path(__file__).parent.parent / "reports"
    json_dir = reports_dir / "json"
    md_dir = reports_dir / "md"
    json_dir.mkdir(parents=True, exist_ok=True)
    md_dir.mkdir(parents=True, exist_ok=True)

    # Save JSON
    json_path = json_dir / f"{filename}.json"
    json_output = json.dumps(snapshot_to_dict(snapshot), indent=2)
    json_path.write_text(json_output)

    # Save Markdown
    md_path = md_dir / f"{filename}.md"
    md_output = format_snapshot_markdown(snapshot)
    md_path.write_text(md_output)

    # Print summary (not full output)
    print(f"\n{'=' * 60}")
    print(f"SNAPSHOT COMPLETE: {snapshot.topic}")
    print(f"{'=' * 60}")
    print(f"Time: {snapshot.stats.crawl_time_seconds:.1f}s")
    print(f"URLs: {snapshot.stats.urls_crawled}/{snapshot.stats.urls_discovered} crawled")
    print(f"Ideas: {snapshot.stats.ideas_extracted}")
    print(f"Consensus: {len(snapshot.consensus_clusters)} clusters")
    print(f"Contention: {len(snapshot.contention_zones)} zones")
    print(f"Zones: {', '.join(f'{k}: {v}' for k, v in zone_counts.items())}")
    print("Saved to:")
    print(f"  {json_path}")
    print(f"  {md_path}")


def setup_snapshot_parser(subparsers: Any) -> None:
    """Setup snapshot command parser."""
    p = subparsers.add_parser("snapshot", help="Build complete topic snapshot")

    # Required
    p.add_argument("topic", help="Topic to research")

    # Discovery options
    p.add_argument("--sources", "-s", default="news,academic,social,web",
                   help="Comma-separated: news,academic,social,web,all (default: news,academic,social,web)")
    p.add_argument("--max-urls", "-u", type=int, default=20,
                   help="Max URLs to crawl (default: 20)")
    p.add_argument("--max-per-source", type=int, default=50,
                   help="Max results per search provider (default: 50)")

    # Region/Language
    p.add_argument("--region", "-r",
                   help="Region code: us, de, fr, gb, jp, etc.")
    p.add_argument("--regions",
                   help="Multi-region search: us,de,gb")
    p.add_argument("--translate", action="store_true",
                   help="Translate query to target languages")
    p.add_argument("--target-langs",
                   help="Languages for translation: de,fr,es")

    # Query augmentation
    p.add_argument("--no-augment", action="store_true",
                   help="Disable query augmentation")
    p.add_argument("--query-variations", type=int, default=3,
                   help="Number of query variations (default: 3)")

    # Filtering
    p.add_argument("--no-filter-urls", action="store_true",
                   help="Disable URL relevance filtering")
    p.add_argument("--no-filter-ideas", action="store_true",
                   help="Disable idea relevance filtering")
    p.add_argument("--relevance-threshold", type=int, default=6,
                   help="URL relevance threshold 1-10 (default: 6)")
    p.add_argument("--idea-threshold", type=int, default=6,
                   help="Idea relevance threshold 1-10 (default: 6)")

    # LLM
    p.add_argument("--llm", default="groq/llama-3.1-8b-instant",
                   help="LLM provider (default: groq/llama-3.1-8b-instant)")
    p.add_argument("--llm-key",
                   help="LLM API key (default: $GROQ_API_KEY or $LLM_API_KEY)")

    # Analysis
    p.add_argument("--no-summary", action="store_true",
                   help="Skip summary generation")
    p.add_argument("--no-graph", action="store_true",
                   help="Skip graph building")
    p.add_argument("--consensus-threshold", type=float, default=0.7,
                   help="Consensus similarity threshold (default: 0.7)")

    # Parallel crawling (from Crawl4AI upgrade)
    p.add_argument("--parallel", "-p", type=int, default=10,
                   help="Max concurrent crawls (default: 10)")

    # Domain expansion via URL seeding (enabled by default)
    p.add_argument("--no-expand", action="store_true",
                   help="Disable domain expansion via sitemap")

    # Output (always saves to reports/json/ and reports/md/)
    p.add_argument("--verbose", "-v", action="store_true",
                   help="Verbose output")


def main() -> None:
    # Initialize session logging
    from ..infrastructure.logging import init_session_logging
    log_file = init_session_logging()
    print(f"Logs: {log_file}")

    parser = argparse.ArgumentParser(
        description="Nous - Topic-aware web intelligence",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Basic snapshot (saves to reports/json/ and reports/md/)
  nous snapshot "AI regulation EU"

  # Multi-region with translation
  nous snapshot "renewable energy policy" --region de --translate --target-langs de,fr

  # Academic focus
  nous snapshot "quantum computing" --sources academic,news --max-urls 30

Output files are saved to:
  reports/json/{topic}_{timestamp}.json
  reports/md/{topic}_{timestamp}.md

Environment variables:
  GROQ_API_KEY    LLM API key (Groq)
  LLM_API_KEY     Alternative LLM API key
  NEWSAPI_KEY     NewsAPI.org key (optional)
        """,
    )

    subparsers = parser.add_subparsers(dest="command", help="Available commands")

    # Setup parsers
    setup_snapshot_parser(subparsers)

    args = parser.parse_args()

    if args.command is None:
        parser.print_help()
        return


    logger.info(f"Command: {args.command}")
    logger.info(f"Args: {args}")

    # Run the appropriate command
    try:
        if args.command == "snapshot":
            asyncio.run(cmd_snapshot(args))

        logger.info("Command completed successfully")
    except KeyboardInterrupt:
        logger.warning("Interrupted by user")
        print("\n\nInterrupted by user")
        sys.exit(1)
    except Exception as e:
        logger.error(f"Command failed: {e}", exc_info=True)
        print(f"\nError: {e}")
        if "--verbose" in sys.argv or "-v" in sys.argv:
            raise
        sys.exit(1)


if __name__ == "__main__":
    main()
