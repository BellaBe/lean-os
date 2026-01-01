#!/usr/bin/env python3
"""
Integration test for SnapshotBuilder.

Tests the full pipeline from topic to complete Snapshot.

Usage:
    GROQ_API_KEY=your_key python -m examples.test_snapshot_builder "AI regulation EU"

Or from scripts/nous directory:
    GROQ_API_KEY=your_key .venv/bin/python examples/test_snapshot_builder.py "AI regulation EU"
"""

import asyncio
import json
import os
import sys
from dataclasses import asdict
from datetime import datetime
from pathlib import Path

# Setup path for both module and script execution
_this_dir = Path(__file__).parent
_nous_dir = _this_dir.parent
if str(_nous_dir) not in sys.path:
    sys.path.insert(0, str(_nous_dir))
if str(_nous_dir.parent) not in sys.path:
    sys.path.insert(0, str(_nous_dir.parent))

# Now import using package names
from nous.application import SnapshotBuilder, SnapshotBuilderConfig, build_snapshot
from nous.domain import Snapshot


def snapshot_to_json(snapshot: Snapshot) -> dict:
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
                "cluster_type": c.cluster_type,
                "avg_similarity": c.avg_similarity,
                "idea_count": c.idea_count,
                "source_count": c.source_count,
                "signal_zone_distribution": c.signal_zone_distribution,
                "top_sources": c.top_sources,
            }
            for c in snapshot.consensus_clusters
        ],
        "contention_zones": [
            {
                "representative_claim": c.representative_claim,
                "cluster_type": c.cluster_type,
                "opposing_views": c.opposing_views,
                "idea_count": c.idea_count,
            }
            for c in snapshot.contention_zones
        ],
        "amplification_warnings": [
            {
                "original_url": w.original_url,
                "amplifier_count": w.amplifier_count,
                "note": w.note,
            }
            for w in snapshot.amplification_warnings
        ],
        "sources": [
            {
                "id": str(s.id),
                "url": s.url,
                "title": s.title,
                "origin": s.origin,
                "source_type": s.source_type.value,
                "signal_zone": s.signal_zone.value,
                "ideas_contributed": [str(i) for i in s.ideas_contributed],
            }
            for s in snapshot.sources
        ],
        "ideas": [
            {
                "id": str(i.id),
                "claim": i.claim,
                "stance_distribution": {
                    k.value if hasattr(k, "value") else k: v
                    for k, v in i.stance_distribution.items()
                },
                "cluster": i.cluster,
                "source_ids": [str(s) for s in i.source_ids],
            }
            for i in snapshot.ideas
        ],
        "graph": {
            "nodes": snapshot.graph_nodes[:10],  # Limit for readability
            "edges": [
                {
                    "source_id": e.source_id,
                    "target_id": e.target_id,
                    "relationship": e.relationship,
                }
                for e in snapshot.graph_edges[:20]
            ],
        },
    }


def print_snapshot_summary(snapshot: Snapshot):
    """Print human-readable snapshot summary."""
    print("\n" + "=" * 70)
    print("  SNAPSHOT SUMMARY")
    print("=" * 70)
    print(f"  Topic:            {snapshot.topic}")
    print(f"  Generated:        {snapshot.generated_at.isoformat()}")
    print(f"  ID:               {str(snapshot.id)[:8]}...")

    print("\n  STATS:")
    print(f"    URLs discovered:  {snapshot.stats.urls_discovered}")
    print(f"    URLs crawled:     {snapshot.stats.urls_crawled}")
    print(f"    URLs failed:      {snapshot.stats.urls_failed}")
    print(f"    Ideas extracted:  {snapshot.stats.ideas_extracted}")
    print(f"    Avg relevance:    {snapshot.stats.avg_relevance_score}")
    print(f"    Time:             {snapshot.stats.crawl_time_seconds}s")

    print("\n  SCOPE:")
    print(f"    Source types:     {', '.join(snapshot.scope.source_types)}")
    print(f"    Domains:          {len(snapshot.scope.domains_searched)}")

    print("\n  SUMMARY:")
    if snapshot.summary:
        # Wrap summary text
        words = snapshot.summary.split()
        lines = []
        current_line = "    "
        for word in words:
            if len(current_line) + len(word) + 1 > 70:
                lines.append(current_line)
                current_line = "    " + word
            else:
                current_line += " " + word if current_line.strip() else "    " + word
        if current_line.strip():
            lines.append(current_line)
        print("\n".join(lines))
    else:
        print("    (No summary generated)")

    print("\n  CONSENSUS CLUSTERS:")
    if snapshot.consensus_clusters:
        for i, c in enumerate(snapshot.consensus_clusters[:3], 1):
            claim = c.representative_claim[:60] + "..." if len(c.representative_claim) > 60 else c.representative_claim
            print(f"    [{i}] {claim}")
            print(f"        {c.idea_count} ideas, {c.source_count} sources, sim={c.avg_similarity:.2f}")
    else:
        print("    (None)")

    print("\n  CONTENTION ZONES:")
    if snapshot.contention_zones:
        for i, c in enumerate(snapshot.contention_zones[:3], 1):
            claim = c.representative_claim[:60] + "..." if len(c.representative_claim) > 60 else c.representative_claim
            print(f"    [{i}] {claim}")
            if c.opposing_views.get("pro"):
                print(f"        PRO: {c.opposing_views['pro'][:50]}...")
            if c.opposing_views.get("con"):
                print(f"        CON: {c.opposing_views['con'][:50]}...")
    else:
        print("    (None)")

    print("\n  AMPLIFICATION WARNINGS:")
    if snapshot.amplification_warnings:
        for w in snapshot.amplification_warnings[:3]:
            print(f"    - {w.note}")
    else:
        print("    (None)")

    print("\n  TOP IDEAS:")
    for i, idea in enumerate(snapshot.ideas[:5], 1):
        stance = max(idea.stance_distribution.items(), key=lambda x: x[1], default=("neutral", 0))
        stance_name = stance[0].value if hasattr(stance[0], "value") else stance[0]
        emoji = {"support": "+", "oppose": "-", "neutral": "~"}.get(stance_name, "?")
        claim = idea.claim[:55] + "..." if len(idea.claim) > 55 else idea.claim
        print(f"    [{i}] [{emoji}] {claim}")

    print("\n  TOP SOURCES:")
    for source in snapshot.sources[:5]:
        zone = source.signal_zone.value
        ideas = len(source.ideas_contributed)
        print(f"    - {source.origin} ({zone}) - {ideas} ideas")

    print("\n  GRAPH:")
    print(f"    Nodes: {len(snapshot.graph_nodes)}")
    print(f"    Edges: {len(snapshot.graph_edges)}")

    print("=" * 70 + "\n")


async def main():
    if len(sys.argv) < 2:
        print("Usage: python test_snapshot_builder.py <topic>")
        print('Example: python test_snapshot_builder.py "AI regulation EU"')
        sys.exit(1)

    topic = sys.argv[1]
    max_urls = 10

    if "--max-urls" in sys.argv:
        idx = sys.argv.index("--max-urls")
        if idx + 1 < len(sys.argv):
            max_urls = int(sys.argv[idx + 1])

    api_key = os.getenv("GROQ_API_KEY")
    if not api_key:
        print("Error: GROQ_API_KEY environment variable required")
        sys.exit(1)

    # Configure builder
    config = SnapshotBuilderConfig(
        max_urls=max_urls,
        sources=["news", "academic", "social", "web"],  # Search APIs + DuckDuckGo
        llm_provider="groq/llama-3.1-8b-instant",
        llm_api_key=api_key,
        generate_summary=True,
        build_graph=True,
        # Quality filters
        augment_queries=True,
        filter_relevance=True,
        filter_ideas=True,
    )

    # Build snapshot
    builder = SnapshotBuilder(config)
    snapshot = await builder.build(topic)

    # Print summary
    print_snapshot_summary(snapshot)

    # Save to file
    output_dir = Path("artifacts/snapshots")
    output_dir.mkdir(parents=True, exist_ok=True)

    safe_topic = topic.replace(" ", "_")[:30]
    filename = f"snapshot_{safe_topic}_{str(snapshot.id)[:8]}.json"
    output_path = output_dir / filename

    with open(output_path, "w") as f:
        json.dump(snapshot_to_json(snapshot), f, indent=2)

    print(f"Snapshot saved to: {output_path}")

    return snapshot


if __name__ == "__main__":
    asyncio.run(main())
