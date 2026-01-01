#!/usr/bin/env python3
"""
End-to-end Nous test: Topic → Snapshot

Usage:
    python examples/snapshot_test.py "AI regulation EU"
    python examples/snapshot_test.py "climate change policy" --max-urls 10

Produces a structured snapshot as per architecture.md
"""

import asyncio
import json
import os
import sys
import time
import uuid
from dataclasses import dataclass, field, asdict
from datetime import datetime, timezone
from html.parser import HTMLParser
from pathlib import Path
from typing import Any
from urllib.parse import urlparse
from urllib.request import urlopen, Request
import xml.etree.ElementTree as ET


# ============================================================================
# Domain lists for URL seeding
# ============================================================================

NEWS_DOMAINS = [
    "reuters.com",
    "bbc.com",
    "theguardian.com",
    "nytimes.com",
    "washingtonpost.com",
    "ft.com",
    "economist.com",
    "politico.eu",
    "euronews.com",
    "dw.com",
]

TECH_DOMAINS = [
    "techcrunch.com",
    "wired.com",
    "theverge.com",
    "arstechnica.com",
    "thenextweb.com",
]


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
    except:
        pass
    return parser.get_text()


def fetch_url(url: str, timeout: int = 10) -> str | None:
    """Fetch URL content, return None on failure."""
    headers = {'User-Agent': 'Mozilla/5.0 (compatible; NousBot/1.0)'}
    try:
        req = Request(url, headers=headers)
        with urlopen(req, timeout=timeout) as resp:
            return resp.read().decode('utf-8', errors='ignore')
    except Exception:
        return None


# ============================================================================
# URL Seeder - discovers URLs from sitemaps
# ============================================================================

def fetch_sitemap_urls(domain: str, max_urls: int = 100) -> list[str]:
    """Fetch URLs from a domain's sitemap."""
    urls = []
    sitemap_urls_to_try = [
        f"https://{domain}/sitemap.xml",
        f"https://{domain}/sitemap_index.xml",
        f"https://{domain}/news-sitemap.xml",
        f"https://www.{domain}/sitemap.xml",
    ]

    for sitemap_url in sitemap_urls_to_try:
        try:
            content = fetch_url(sitemap_url, timeout=5)
            if not content:
                continue

            # Parse XML
            root = ET.fromstring(content)
            ns = {'sm': 'http://www.sitemaps.org/schemas/sitemap/0.9'}

            # Check if it's a sitemap index
            sitemaps = root.findall('.//sm:sitemap/sm:loc', ns)
            if sitemaps:
                # It's an index, fetch first sub-sitemap
                for sm in sitemaps[:2]:
                    sub_content = fetch_url(sm.text, timeout=5)
                    if sub_content:
                        try:
                            sub_root = ET.fromstring(sub_content)
                            for loc in sub_root.findall('.//sm:url/sm:loc', ns):
                                if loc.text:
                                    urls.append(loc.text)
                                if len(urls) >= max_urls:
                                    break
                        except:
                            pass
                    if len(urls) >= max_urls:
                        break
            else:
                # Direct sitemap
                for loc in root.findall('.//sm:url/sm:loc', ns):
                    if loc.text:
                        urls.append(loc.text)
                    if len(urls) >= max_urls:
                        break

            if urls:
                break

        except Exception:
            continue

    return urls[:max_urls]


def score_url_relevance(url: str, title: str, topic: str) -> float:
    """Simple BM25-like relevance scoring."""
    topic_terms = set(topic.lower().split())
    text = f"{url} {title}".lower()

    matches = sum(1 for term in topic_terms if term in text)
    return matches / len(topic_terms) if topic_terms else 0


# ============================================================================
# LLM Client with rate limiting
# ============================================================================

@dataclass
class RateLimitState:
    remaining_requests: int = 30
    remaining_tokens: int = 6000
    last_updated: float = field(default_factory=time.time)


class RateLimiter:
    def __init__(self):
        self.state = RateLimitState()
        self.max_retries = 3

    def update(self, headers: dict):
        if "x-ratelimit-remaining-requests" in headers:
            self.state.remaining_requests = int(headers["x-ratelimit-remaining-requests"])

    async def backoff(self, attempt: int) -> bool:
        if attempt >= self.max_retries:
            return False
        await asyncio.sleep(2 ** attempt)
        return True


class LLMClient:
    def __init__(self, api_key: str):
        self.api_key = api_key
        self.rate_limiter = RateLimiter()

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
                    if await self.rate_limiter.backoff(attempt):
                        continue
                if attempt == 2:
                    return []
        return []


# ============================================================================
# Snapshot data structures
# ============================================================================

@dataclass
class SourceNode:
    id: str
    url: str
    title: str
    domain: str
    source_type: str  # news, academic, blog, etc.
    signal_zone: str  # institutional, grassroots, speculative
    relevance_score: float
    content_length: int
    ideas_extracted: int


@dataclass
class IdeaNode:
    id: str
    claim: str
    stance: str
    confidence: float
    source_ids: list[str]


@dataclass
class Snapshot:
    id: str
    topic: str
    generated_at: str

    # Stats
    domains_searched: list[str]
    urls_discovered: int
    urls_crawled: int
    urls_failed: int
    ideas_extracted: int
    crawl_time_seconds: float

    # Results
    sources: list[SourceNode]
    ideas: list[IdeaNode]

    # Analysis
    consensus_ratio: float
    stance_distribution: dict[str, int]
    avg_relevance: float
    avg_confidence: float


# ============================================================================
# Main discovery pipeline
# ============================================================================

def classify_source_type(url: str, domain: str) -> str:
    d = domain.lower()
    if any(x in d for x in ["arxiv", "nature.com", "science.org"]):
        return "academic"
    if any(x in d for x in [".gov", "europa.eu"]):
        return "government"
    if any(x in d for x in ["medium", "substack", "blog"]):
        return "blog"
    return "news"


def classify_signal_zone(domain: str) -> str:
    d = domain.lower()
    if any(x in d for x in ["reuters", "bbc", "nytimes", "ft.com", "economist", "gov"]):
        return "institutional"
    if any(x in d for x in ["twitter", "reddit", "substack"]):
        return "speculative"
    return "grassroots"


async def create_snapshot(topic: str, max_urls: int = 20, domains: list[str] | None = None) -> Snapshot:
    """
    Create a snapshot for a topic.

    This is the main entry point - just provide a topic.
    """
    api_key = os.getenv("GROQ_API_KEY")
    if not api_key:
        raise ValueError("GROQ_API_KEY environment variable required")

    domains = domains or NEWS_DOMAINS[:5]
    start_time = time.time()

    print(f"\n{'═' * 70}")
    print(f"  NOUS SNAPSHOT: {topic}")
    print(f"{'═' * 70}\n")

    # ─────────────────────────────────────────────────────────────────────
    # Stage 1: URL Discovery (from sitemaps)
    # ─────────────────────────────────────────────────────────────────────
    print(f"[1/4] 🔍 Discovering URLs from {len(domains)} domains...")

    all_urls = []
    for domain in domains:
        print(f"      {domain}...", end=" ", flush=True)
        urls = fetch_sitemap_urls(domain, max_urls=50)
        print(f"{len(urls)} URLs")
        all_urls.extend([(url, domain) for url in urls])

    urls_discovered = len(all_urls)
    print(f"      Total: {urls_discovered} URLs discovered")

    # ─────────────────────────────────────────────────────────────────────
    # Stage 2: Relevance Scoring & Filtering
    # ─────────────────────────────────────────────────────────────────────
    print(f"\n[2/4] 📊 Scoring relevance to '{topic}'...")

    scored_urls = []
    for url, domain in all_urls:
        # Get title from URL path
        path = urlparse(url).path
        title = path.replace("-", " ").replace("/", " ").strip()
        score = score_url_relevance(url, title, topic)
        if score > 0:
            scored_urls.append((url, domain, title, score))

    # Sort by relevance and take top N
    scored_urls.sort(key=lambda x: x[3], reverse=True)
    scored_urls = scored_urls[:max_urls]

    print(f"      {len(scored_urls)} URLs match topic (score > 0)")

    # ─────────────────────────────────────────────────────────────────────
    # Stage 3: Content Crawling
    # ─────────────────────────────────────────────────────────────────────
    print(f"\n[3/4] 📥 Crawling content from top {len(scored_urls)} URLs...")

    sources = []
    crawled = 0
    failed = 0

    for i, (url, domain, title, score) in enumerate(scored_urls):
        print(f"      [{i+1}/{len(scored_urls)}] {domain}...", end=" ", flush=True)

        html = fetch_url(url)
        if html:
            text = html_to_text(html)
            if len(text) > 200:  # Minimum content threshold
                sources.append({
                    "id": str(uuid.uuid4())[:8],
                    "url": url,
                    "domain": domain,
                    "title": title[:100],
                    "content": text,
                    "relevance": score,
                })
                crawled += 1
                print(f"✓ ({len(text):,} chars)")
            else:
                failed += 1
                print("✗ (too short)")
        else:
            failed += 1
            print("✗ (failed)")

    print(f"      Crawled: {crawled}, Failed: {failed}")

    # ─────────────────────────────────────────────────────────────────────
    # Stage 4: Idea Extraction (LLM)
    # ─────────────────────────────────────────────────────────────────────
    print(f"\n[4/4] 🧠 Extracting ideas with LLM...")

    llm = LLMClient(api_key)
    all_ideas = []
    source_nodes = []

    for source in sources:
        print(f"      {source['domain']}...", end=" ", flush=True)

        ideas = await llm.extract_ideas(source["content"], topic)

        source_node = SourceNode(
            id=source["id"],
            url=source["url"],
            title=source["title"],
            domain=source["domain"],
            source_type=classify_source_type(source["url"], source["domain"]),
            signal_zone=classify_signal_zone(source["domain"]),
            relevance_score=source["relevance"],
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

    # ─────────────────────────────────────────────────────────────────────
    # Build Snapshot
    # ─────────────────────────────────────────────────────────────────────
    elapsed = time.time() - start_time

    # Calculate stats
    stance_dist = {"support": 0, "oppose": 0, "neutral": 0}
    for idea in all_ideas:
        stance_dist[idea.stance] = stance_dist.get(idea.stance, 0) + 1

    total_ideas = len(all_ideas)
    support_count = stance_dist.get("support", 0)
    consensus_ratio = support_count / total_ideas if total_ideas > 0 else 0

    confidences = [i.confidence for i in all_ideas if i.confidence]
    avg_confidence = sum(confidences) / len(confidences) if confidences else 0

    relevances = [s.relevance_score for s in source_nodes]
    avg_relevance = sum(relevances) / len(relevances) if relevances else 0

    snapshot = Snapshot(
        id=str(uuid.uuid4()),
        topic=topic,
        generated_at=datetime.now(timezone.utc).isoformat(),
        domains_searched=domains,
        urls_discovered=urls_discovered,
        urls_crawled=crawled,
        urls_failed=failed,
        ideas_extracted=total_ideas,
        crawl_time_seconds=round(elapsed, 1),
        sources=source_nodes,
        ideas=all_ideas,
        consensus_ratio=round(consensus_ratio, 2),
        stance_distribution=stance_dist,
        avg_relevance=round(avg_relevance, 2),
        avg_confidence=round(avg_confidence, 2),
    )

    return snapshot


def snapshot_to_dict(snapshot: Snapshot) -> dict:
    """Convert snapshot to serializable dict."""
    return {
        "id": snapshot.id,
        "topic": snapshot.topic,
        "generated_at": snapshot.generated_at,
        "stats": {
            "domains_searched": snapshot.domains_searched,
            "urls_discovered": snapshot.urls_discovered,
            "urls_crawled": snapshot.urls_crawled,
            "urls_failed": snapshot.urls_failed,
            "ideas_extracted": snapshot.ideas_extracted,
            "crawl_time_seconds": snapshot.crawl_time_seconds,
        },
        "analysis": {
            "consensus_ratio": snapshot.consensus_ratio,
            "stance_distribution": snapshot.stance_distribution,
            "avg_relevance": snapshot.avg_relevance,
            "avg_confidence": snapshot.avg_confidence,
        },
        "sources": [asdict(s) for s in snapshot.sources],
        "ideas": [asdict(i) for i in snapshot.ideas],
    }


def print_snapshot_summary(snapshot: Snapshot):
    """Print human-readable snapshot summary."""
    print(f"\n{'═' * 70}")
    print(f"  SNAPSHOT SUMMARY")
    print(f"{'═' * 70}")
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
    print(f"    Avg relevance:    {snapshot.avg_relevance}")
    print(f"    Avg confidence:   {snapshot.avg_confidence}")
    print(f"    Consensus ratio:  {snapshot.consensus_ratio:.0%}")
    print(f"\n  STANCE DISTRIBUTION:")
    for stance, count in snapshot.stance_distribution.items():
        emoji = {"support": "👍", "oppose": "👎", "neutral": "➖"}.get(stance, "?")
        print(f"    {emoji} {stance}: {count}")

    print(f"\n  TOP IDEAS:")
    for i, idea in enumerate(snapshot.ideas[:5], 1):
        emoji = {"support": "👍", "oppose": "👎", "neutral": "➖"}.get(idea.stance, "?")
        print(f"    [{i}] {emoji} {idea.claim[:65]}{'...' if len(idea.claim) > 65 else ''}")

    print(f"\n  SOURCES:")
    for source in snapshot.sources[:5]:
        print(f"    • {source.domain} ({source.signal_zone}) - {source.ideas_extracted} ideas")

    print(f"{'═' * 70}\n")


async def main():
    # Parse args
    if len(sys.argv) < 2:
        print("Usage: python snapshot_test.py <topic> [--max-urls N]")
        print('Example: python snapshot_test.py "AI regulation EU"')
        sys.exit(1)

    topic = sys.argv[1]
    max_urls = 10

    if "--max-urls" in sys.argv:
        idx = sys.argv.index("--max-urls")
        if idx + 1 < len(sys.argv):
            max_urls = int(sys.argv[idx + 1])

    # Create snapshot
    snapshot = await create_snapshot(topic, max_urls=max_urls)

    # Print summary
    print_snapshot_summary(snapshot)

    # Save to file
    output_dir = Path("artifacts/snapshots")
    output_dir.mkdir(parents=True, exist_ok=True)

    filename = f"snapshot_{topic.replace(' ', '_')[:30]}_{snapshot.id[:8]}.json"
    output_path = output_dir / filename

    with open(output_path, "w") as f:
        json.dump(snapshot_to_dict(snapshot), f, indent=2)

    print(f"📁 Snapshot saved to: {output_path}")

    return snapshot


if __name__ == "__main__":
    asyncio.run(main())
