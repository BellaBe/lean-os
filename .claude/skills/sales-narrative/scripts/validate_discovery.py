#!/usr/bin/env python3
"""
Checks if discovery files exist and contain minimum required data.
Returns: JSON with validation status
"""

import json
import sys
from pathlib import Path

def validate_discovery(thread_id: str) -> dict:
    thread_path = Path(f"threads/sales/{thread_id}")
    
    required_files = {
        'problem_interview': thread_path / 'discovery/problem-interview.md',
        'solution_interview': thread_path / 'discovery/solution-interview.md',
        'stakeholders': thread_path / 'discovery/stakeholders.md'
    }
    
    results = {}
    for name, path in required_files.items():
        results[name] = {
            'exists': path.exists(),
            'has_content': path.exists() and len(path.read_text().strip()) > 100
        }
    
    return {
        'thread_id': thread_id,
        'valid': all(r['exists'] and r['has_content'] for r in results.values()),
        'files': results
    }

if __name__ == '__main__':
    result = validate_discovery(sys.argv[1])
    print(json.dumps(result, indent=2))