#!/usr/bin/env python3
"""
DuckDuckGo-based URL discovery test.

Usage:
    python examples/duckduckgo_test.py "AI regulation EU"

This discovers URLs via web search instead of sitemaps.
Produces snapshots matching architecture.md specification.
"""

import asyncio
import json
import os
import re
import sys
import time
from dataclasses import asdict
from datetime import datetime, timezone
from html.parser import HTMLParser
from pathlib import Path
from typing import Any
from urllib.parse import urlparse, parse_qs, unquote
from urllib.request import urlopen, Request
from uuid import uuid4

# Add parent to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from domain import (
    AmplificationWarning,
    ConsensusCluster,
    ContentionZone,
    GraphEdge,
    IdeaId,
    IdeaNode,
    Snapshot,
    SnapshotScope,
    SnapshotStats,
    SignalZone,
    SourceId,
    SourceNode,
    SourceType,
    Stance,
)


# ============================================================================
# HTML utilities
# ============================================================================

class HTMLTextExtractor(HTMLParser):
    def __init__(self):
        super().__init__()
        self.text_parts = []
        self.skip_tags = {'script', 'style', 'nav', 'footer', 'header', 'aside'}
        self.current_skip = 0

    def handle_starttag(self, tag, attrs):
        if tag in self.skip_tags:
            self.current_skip += 1

    def handle_endtag(self, tag):
        if tag in self.skip_tags and self.current_skip > 0:
            self.current_skip -= 1

    def handle_data(self, data):
        if self.current_skip == 0:
            text = data.strip()
            if text:
                self.text_parts.append(text)

    def get_text(self) -> str:
        return ' '.join(self.text_parts)


def html_to_text(html: str) -> str:
    parser = HTMLTextExtractor()
    try:
        parser.feed(html)
    except Exception:
        pass
    return parser.get_text()


def fetch_url(url: str, timeout: int = 10) -> str | None:
    """Fetch URL content, return None on failure."""
    headers = {
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36'
    }
    try:
        req = Request(url, headers=headers)
        with urlopen(req, timeout=timeout) as resp:
            return resp.read().decode('utf-8', errors='ignore')
    except Exception:
        return None


# ============================================================================
# DuckDuckGo Search
# ============================================================================

def search_duckduckgo(query: str, max_results: int = 20) -> list[dict]:
    """
    Search DuckDuckGo HTML and extract URLs.
    Returns list of {url, title, snippet}.
    """
    results = []
    search_url = f"https://html.duckduckgo.com/html/?q={query.replace(' ', '+')}"

    headers = {
        'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36'
    }

    try:
        req = Request(search_url, headers=headers)
        with urlopen(req, timeout=15) as resp:
            html = resp.read().decode('utf-8', errors='ignore')

        # Parse result links - DuckDuckGo HTML format
        link_pattern = r'<a[^>]+class="result__a"[^>]+href="([^"]+)"[^>]*>([^<]+)</a>'
        snippet_pattern = r'<a[^>]+class="result__snippet"[^>]*>([^<]+)</a>'

        links = re.findall(link_pattern, html)
        snippets = re.findall(snippet_pattern, html)

        for i, (url, title) in enumerate(links[:max_results]):
            # DuckDuckGo returns redirect URLs - extract actual URL
            if 'uddg=' in url:
                parsed = parse_qs(urlparse(url).query)
                if 'uddg' in parsed:
                    url = unquote(parsed['uddg'][0])

            snippet = snippets[i] if i < len(snippets) else ""

            # Skip non-http URLs and known bad domains
            if not url.startswith('http'):
                continue
            if any(x in url for x in ['duckduckgo.com', '/ad/', 'ads.']):
                continue

            results.append({
                'url': url,
                'title': title.strip(),
                'snippet': snippet.strip(),
            })

    except Exception as e:
        print(f"      Search error: {e}")

    return results


def discover_urls_for_topic(topic: str, max_results: int = 20) -> list[dict]:
    """
    Discover relevant URLs for a topic using web search.
    Returns list of {url, title, snippet, domain}.
    """
    # Build diverse search queries
    queries = [
        f"{topic}",
        f"{topic} news 2024",
        f"{topic} analysis",
    ]

    seen_urls = set()
    results = []

    for query in queries:
        if len(results) >= max_results:
            break

        print(f"      Query: {query[:50]}...", end=" ", flush=True)
        search_results = search_duckduckgo(query, max_results=10)
        print(f"{len(search_results)} results")

        for r in search_results:
            url = r['url']
            if url in seen_urls:
                continue
            seen_urls.add(url)

            domain = urlparse(url).netloc.replace('www.', '')

            results.append({
                'url': url,
                'title': r['title'],
                'snippet': r.get('snippet', ''),
                'domain': domain,
            })

            if len(results) >= max_results:
                break

    return results


# ============================================================================
# LLM Client
# ============================================================================

class LLMClient:
    def __init__(self, api_key: str):
        self.api_key = api_key

    async def extract_ideas(self, content: str, topic: str) -> list[dict]:
        """Extract ideas from content."""
        import litellm

        if len(content) > 5000:
            content = content[:5000] + "..."

        prompt = f"""Topic: {topic}

Content:
{content}

Extract 3-5 key ideas/claims. Return ONLY a JSON array:
[{{"claim": "...", "stance": "support|oppose|neutral", "confidence": 0.0-1.0}}]"""

        system = "Extract ideas as JSON array. Output ONLY valid JSON."

        for attempt in range(3):
            try:
                response = await litellm.acompletion(
                    model="groq/llama-3.1-8b-instant",
                    messages=[
                        {"role": "system", "content": system},
                        {"role": "user", "content": prompt},
                    ],
                    api_key=self.api_key,
                    temperature=0,
                    max_tokens=2000,
                )

                text = response.choices[0].message.content or ""

                # Extract JSON
                if "```json" in text:
                    text = text.split("```json")[1].split("```")[0]
                elif "```" in text:
                    text = text.split("```")[1].split("```")[0]

                return json.loads(text.strip())

            except Exception as e:
                if "429" in str(e) or "rate" in str(e).lower():
                    await asyncio.sleep(2 ** attempt)
                    continue
                if attempt == 2:
                    return []
        return []


# ============================================================================
# Classification helpers
# ============================================================================

def classify_source_type(domain: str) -> SourceType:
    d = domain.lower()
    if any(x in d for x in ["arxiv", "nature.com", "science.org", "academic"]):
        return SourceType.ACADEMIC
    if any(x in d for x in [".gov", "europa.eu", "commission.europa", "europarl"]):
        return SourceType.GOVERNMENT
    if any(x in d for x in ["medium", "substack", "blog"]):
        return SourceType.BLOG
    if any(x in d for x in ["reddit", "twitter", "x.com"]):
        return SourceType.SOCIAL
    return SourceType.NEWS


def classify_signal_zone(domain: str) -> SignalZone:
    d = domain.lower()
    if any(x in d for x in ["reuters", "bbc", "nytimes", "ft.com", "economist", "gov", "europa"]):
        return SignalZone.INSTITUTIONAL
    if any(x in d for x in ["twitter", "reddit", "4chan", "substack"]):
        return SignalZone.SPECULATIVE
    return SignalZone.GRASSROOTS


def extract_origin_name(domain: str) -> str:
    """Extract human-readable origin name from domain."""
    name_map = {
        "reuters.com": "Reuters",
        "bbc.com": "BBC",
        "nytimes.com": "New York Times",
        "ft.com": "Financial Times",
        "economist.com": "The Economist",
        "theguardian.com": "The Guardian",
        "washingtonpost.com": "Washington Post",
        "europarl.europa.eu": "European Parliament",
        "commission.europa.eu": "European Commission",
        "eur-lex.europa.eu": "EUR-Lex",
        "wikipedia.org": "Wikipedia",
        "investopedia.com": "Investopedia",
    }
    for key, name in name_map.items():
        if key in domain:
            return name
    # Fallback: capitalize domain parts
    parts = domain.replace("www.", "").split(".")
    return parts[0].title() if parts else domain


# ============================================================================
# Main pipeline
# ============================================================================

async def create_snapshot(topic: str, max_urls: int = 10) -> Snapshot:
    """Create a snapshot for a topic using web search discovery."""
    api_key = os.getenv("GROQ_API_KEY")
    if not api_key:
        raise ValueError("GROQ_API_KEY environment variable required")

    start_time = time.time()

    print(f"\n{'=' * 70}")
    print(f"  NOUS SNAPSHOT (DuckDuckGo): {topic}")
    print(f"{'=' * 70}\n")

    # Stage 1: URL Discovery via search
    print(f"[1/3] Discovering URLs via web search...")
    discovered = discover_urls_for_topic(topic, max_results=max_urls * 2)
    urls_discovered = len(discovered)
    print(f"      Total: {urls_discovered} unique URLs discovered")

    # Stage 2: Content Crawling
    print(f"\n[2/3] Crawling content from top {min(len(discovered), max_urls)} URLs...")

    sources = []
    crawled = 0
    failed = 0

    for i, item in enumerate(discovered[:max_urls]):
        url = item['url']
        domain = item['domain']
        title = item['title']

        print(f"      [{i+1}/{min(len(discovered), max_urls)}] {domain[:30]}...", end=" ", flush=True)

        html = fetch_url(url)
        if html:
            text = html_to_text(html)
            if len(text) > 200:
                sources.append({
                    "id": str(uuid.uuid4())[:8],
                    "url": url,
                    "domain": domain,
                    "title": title[:100],
                    "content": text,
                })
                crawled += 1
                print(f"({len(text):,} chars)")
            else:
                failed += 1
                print("(too short)")
        else:
            failed += 1
            print("(failed)")

    print(f"      Crawled: {crawled}, Failed: {failed}")

    # Stage 3: Idea Extraction
    print(f"\n[3/3] Extracting ideas with LLM...")

    llm = LLMClient(api_key)
    all_ideas = []
    source_nodes = []

    for source in sources:
        print(f"      {source['domain'][:30]}...", end=" ", flush=True)

        ideas = await llm.extract_ideas(source["content"], topic)

        source_node = SourceNode(
            id=source["id"],
            url=source["url"],
            title=source["title"],
            domain=source["domain"],
            source_type=classify_source_type(source["domain"]),
            signal_zone=classify_signal_zone(source["domain"]),
            content_length=len(source["content"]),
            ideas_extracted=len(ideas),
        )
        source_nodes.append(source_node)

        for idea in ideas:
            all_ideas.append(IdeaNode(
                id=str(uuid.uuid4())[:8],
                claim=idea.get("claim", ""),
                stance=idea.get("stance", "neutral"),
                confidence=idea.get("confidence", 0.5),
                source_ids=[source["id"]],
            ))

        print(f"{len(ideas)} ideas")

    # Build Snapshot
    elapsed = time.time() - start_time

    stance_dist = {"support": 0, "oppose": 0, "neutral": 0}
    for idea in all_ideas:
        stance_dist[idea.stance] = stance_dist.get(idea.stance, 0) + 1

    total_ideas = len(all_ideas)
    support_count = stance_dist.get("support", 0)
    consensus_ratio = support_count / total_ideas if total_ideas > 0 else 0

    confidences = [i.confidence for i in all_ideas if i.confidence]
    avg_confidence = sum(confidences) / len(confidences) if confidences else 0

    snapshot = Snapshot(
        id=str(uuid.uuid4()),
        topic=topic,
        generated_at=datetime.now(timezone.utc).isoformat(),
        urls_discovered=urls_discovered,
        urls_crawled=crawled,
        urls_failed=failed,
        ideas_extracted=total_ideas,
        crawl_time_seconds=round(elapsed, 1),
        sources=source_nodes,
        ideas=all_ideas,
        consensus_ratio=round(consensus_ratio, 2),
        stance_distribution=stance_dist,
        avg_confidence=round(avg_confidence, 2),
    )

    return snapshot


def snapshot_to_dict(snapshot: Snapshot) -> dict:
    return {
        "id": snapshot.id,
        "topic": snapshot.topic,
        "generated_at": snapshot.generated_at,
        "stats": {
            "urls_discovered": snapshot.urls_discovered,
            "urls_crawled": snapshot.urls_crawled,
            "urls_failed": snapshot.urls_failed,
            "ideas_extracted": snapshot.ideas_extracted,
            "crawl_time_seconds": snapshot.crawl_time_seconds,
        },
        "analysis": {
            "consensus_ratio": snapshot.consensus_ratio,
            "stance_distribution": snapshot.stance_distribution,
            "avg_confidence": snapshot.avg_confidence,
        },
        "sources": [asdict(s) for s in snapshot.sources],
        "ideas": [asdict(i) for i in snapshot.ideas],
    }


def print_snapshot_summary(snapshot: Snapshot):
    print(f"\n{'=' * 70}")
    print(f"  SNAPSHOT SUMMARY")
    print(f"{'=' * 70}")
    print(f"  Topic:            {snapshot.topic}")
    print(f"  Generated:        {snapshot.generated_at}")
    print(f"  ID:               {snapshot.id[:8]}...")
    print(f"\n  STATS:")
    print(f"    URLs discovered:  {snapshot.urls_discovered}")
    print(f"    URLs crawled:     {snapshot.urls_crawled}")
    print(f"    URLs failed:      {snapshot.urls_failed}")
    print(f"    Ideas extracted:  {snapshot.ideas_extracted}")
    print(f"    Time:             {snapshot.crawl_time_seconds}s")
    print(f"\n  ANALYSIS:")
    print(f"    Avg confidence:   {snapshot.avg_confidence}")
    print(f"    Consensus ratio:  {snapshot.consensus_ratio:.0%}")
    print(f"\n  STANCE DISTRIBUTION:")
    for stance, count in snapshot.stance_distribution.items():
        emoji = {"support": "+", "oppose": "-", "neutral": "~"}.get(stance, "?")
        print(f"    [{emoji}] {stance}: {count}")

    print(f"\n  TOP IDEAS:")
    for i, idea in enumerate(snapshot.ideas[:5], 1):
        emoji = {"support": "+", "oppose": "-", "neutral": "~"}.get(idea.stance, "?")
        print(f"    [{i}] [{emoji}] {idea.claim[:60]}{'...' if len(idea.claim) > 60 else ''}")

    print(f"\n  SOURCES:")
    for source in snapshot.sources[:5]:
        print(f"    - {source.domain} ({source.signal_zone}) - {source.ideas_extracted} ideas")

    print(f"{'=' * 70}\n")


async def main():
    if len(sys.argv) < 2:
        print("Usage: python duckduckgo_test.py <topic>")
        print('Example: python duckduckgo_test.py "AI regulation EU"')
        sys.exit(1)

    topic = sys.argv[1]
    max_urls = 10

    if "--max-urls" in sys.argv:
        idx = sys.argv.index("--max-urls")
        if idx + 1 < len(sys.argv):
            max_urls = int(sys.argv[idx + 1])

    snapshot = await create_snapshot(topic, max_urls=max_urls)
    print_snapshot_summary(snapshot)

    # Save
    output_dir = Path("artifacts/snapshots")
    output_dir.mkdir(parents=True, exist_ok=True)

    filename = f"snapshot_ddg_{topic.replace(' ', '_')[:30]}_{snapshot.id[:8]}.json"
    output_path = output_dir / filename

    with open(output_path, "w") as f:
        json.dump(snapshot_to_dict(snapshot), f, indent=2)

    print(f"Snapshot saved to: {output_path}")

    return snapshot


if __name__ == "__main__":
    asyncio.run(main())
