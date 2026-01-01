"""
Nous - Noosphere Snapshot Engine

Automated knowledge synthesis tool that crawls, extracts, and maps
the ideological landscape around any topic.
"""

from .application import (
    DiscoveryConfig,
    DiscoveryResult,
    # Seeded discovery (bypasses SERP/Google anti-bot)
    SeededDiscovery,
    SeededDiscoveryConfig,
    SeededDiscoveryResult,
    # Original SERP-based discovery
    SourceDiscoveryUseCase,
    discover_academic,
    discover_all,
    discover_news,
    discover_seeded,
    discover_tech,
    quick_discover,
)
from .domain import (
    IdeaNode,
    SearchResponse,
    SearchResult,
    SignalZone,
    SourceNode,
    SourceType,
    Stance,
)

__version__ = "0.1.0"

__all__ = [
    # Domain
    "SourceType",
    "SignalZone",
    "Stance",
    "SourceNode",
    "IdeaNode",
    "SearchResult",
    "SearchResponse",
    # Application - SERP-based (may hit anti-bot)
    "SourceDiscoveryUseCase",
    "DiscoveryConfig",
    "DiscoveryResult",
    "quick_discover",
    # Application - Seeded (reliable, no anti-bot issues)
    "SeededDiscovery",
    "SeededDiscoveryConfig",
    "SeededDiscoveryResult",
    "discover_seeded",
    "discover_news",
    "discover_tech",
    "discover_academic",
    "discover_all",
]
