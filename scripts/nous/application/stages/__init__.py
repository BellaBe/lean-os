"""
Pipeline stages for Nous snapshot building.

Each stage is a self-contained unit that:
- Receives a PipelineContext
- Performs its work
- Returns updated PipelineContext

This allows for:
- Testable, modular stages
- Easy reordering/skipping of stages
- Clear data flow between stages
"""

from .base import PipelineContext, PipelineStage
from .discovery import DiscoveryStage

__all__ = [
    "PipelineContext",
    "PipelineStage",
    "DiscoveryStage",
]
