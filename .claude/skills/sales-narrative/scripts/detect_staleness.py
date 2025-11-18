#!/usr/bin/env python3
"""
Compares file modification times to determine if narrative needs regeneration.
Pure logic, no generation.
"""

import json
import sys
from pathlib import Path
from datetime import datetime, timezone

def detect_staleness(thread_id: str, persona: str) -> dict:
    thread_path = Path(f"threads/sales/{thread_id}")
    narrative_path = thread_path / f"narratives/{persona}.md"
    meta_path = thread_path / f"narratives/{persona}-meta.json"
    
    if not narrative_path.exists():
        return {
            'thread_id': thread_id,
            'persona': persona,
            'is_stale': True,
            'reasons': ['Narrative does not exist']
        }
    
    # Load generation timestamp
    if not meta_path.exists():
        return {
            'thread_id': thread_id,
            'persona': persona,
            'is_stale': True,
            'reasons': ['No meta file (cannot determine age)']
        }
    
    meta = json.loads(meta_path.read_text())
    generated_at = datetime.fromisoformat(meta['generated_at'])
    
    reasons = []
    
    # Check discovery files
    discovery_files = [
        thread_path / 'discovery/problem-interview.md',
        thread_path / 'discovery/solution-interview.md',
        thread_path / 'discovery/stakeholders.md'
    ]
    
    for file in discovery_files:
        if file.exists() and _modified_after(file, generated_at):
            reasons.append(f"Discovery updated: {file.name}")
    
    # Check Canvas files
    canvas_path = Path('strategy/canvas')
    canvas_files = ['problem.md', 'solution.md', 'unique-value.md', 'metrics.md']
    
    for file in canvas_files:
        full_path = canvas_path / file
        if full_path.exists() and _modified_after(full_path, generated_at):
            reasons.append(f"Canvas updated: {file}")
    
    # Check age (14 days)
    age_days = (datetime.now(timezone.utc) - generated_at).days
    if age_days > 14:
        reasons.append(f"Narrative is {age_days} days old")
    
    return {
        'thread_id': thread_id,
        'persona': persona,
        'is_stale': len(reasons) > 0,
        'reasons': reasons,
        'generated_at': meta['generated_at'],
        'age_days': age_days
    }

def _modified_after(file: Path, timestamp: datetime) -> bool:
    file_mtime = datetime.fromtimestamp(file.stat().st_mtime, tz=timezone.utc)
    return file_mtime > timestamp

if __name__ == '__main__':
    result = detect_staleness(sys.argv[1], sys.argv[2])
    print(json.dumps(result, indent=2))