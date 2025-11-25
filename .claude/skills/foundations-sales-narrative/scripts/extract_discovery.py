#!/usr/bin/env python3
"""
Parses discovery markdown files into structured JSON.
Claude uses this to access discovery data without re-parsing markdown.
"""

import json
import re
import sys
from pathlib import Path

def extract_discovery(thread_id: str) -> dict:
    thread_path = Path(f"threads/sales/{thread_id}/discovery")
    
    problem = thread_path / 'problem-interview.md'
    solution = thread_path / 'solution-interview.md'
    stakeholders = thread_path / 'stakeholders.md'
    
    return {
        'thread_id': thread_id,
        'problem_interview': {
            'pain_points': extract_section(problem, 'Pain Points'),
            'current_solution': extract_section(problem, 'Current Solution'),
            'cost_impact': extract_section(problem, 'Cost/Impact')
        },
        'solution_interview': {
            'desired_outcome': extract_section(solution, 'Desired Outcome'),
            'success_criteria': extract_section(solution, 'Success Criteria'),
            'objections': extract_section(solution, 'Concerns/Objections')
        },
        'stakeholders': extract_personas(stakeholders)
    }

def extract_section(file_path: Path, heading: str) -> str:
    """Extract content under a markdown heading"""
    if not file_path.exists():
        return ""
    
    content = file_path.read_text()
    pattern = rf"##\s+{re.escape(heading)}.*?\n(.*?)(?=\n##|\Z)"
    match = re.search(pattern, content, re.DOTALL | re.IGNORECASE)
    return match.group(1).strip() if match else ""

def extract_personas(file_path: Path) -> list[dict]:
    """Extract persona mapping from stakeholders.md"""
    if not file_path.exists():
        return []
    
    content = file_path.read_text()
    # Simple regex to find persona sections
    # Expects format like: "### John Doe - CFO (Economic Buyer)"
    pattern = r"###\s+([^\n]+?)\s+-\s+([^\n]+?)\s+\(([^)]+)\)"
    
    personas = []
    for match in re.finditer(pattern, str(content)):
        personas.append({
            'name': match.group(1).strip(),
            'role': match.group(2).strip(),
            'persona_type': match.group(3).strip().lower().replace(' ', '-')
        })
    
    return personas

if __name__ == '__main__':
    result = extract_discovery(sys.argv[1])
    print(json.dumps(result, indent=2))