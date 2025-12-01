#!/usr/bin/env python3
"""Validate content draft against quality standards."""

import argparse
import re
import sys
from pathlib import Path

def validate_draft(draft_path: str, content_type: str) -> dict:
    """Validate draft and return issues."""
    issues = []
    warnings = []
    
    draft = Path(draft_path).read_text()
    
    # Check frontmatter exists
    if not draft.startswith('---'):
        issues.append("Missing frontmatter")
    
    # Check for sales language
    sales_patterns = [
        r'\bbook a demo\b',
        r'\bsign up\b',
        r'\bget started today\b',
        r'\blimited time\b',
        r'\bact now\b',
    ]
    for pattern in sales_patterns:
        if re.search(pattern, draft, re.IGNORECASE):
            warnings.append(f"Possible sales language: {pattern}")
    
    # Check for unsourced metrics
    metric_pattern = r'\b\d+%|\$\d+|\d+x\b'
    metrics = re.findall(metric_pattern, draft)
    if metrics and 'source_paths' not in draft:
        warnings.append(f"Metrics found ({len(metrics)}) - verify sourced")
    
    # Check minimum length by type
    word_count = len(draft.split())
    minimums = {
        'blog': 800,
        'case-study': 1000,
        'linkedin': 100,
        'twitter': 20,
        'email': 200,
    }
    min_words = minimums.get(content_type, 500)
    if word_count < min_words:
        warnings.append(f"Short for {content_type}: {word_count} words (min: {min_words})")
    
    # Check review notes section
    if '## Review Notes' not in draft and '## Editor Notes' not in draft:
        warnings.append("Missing review notes section")
    
    return {
        'valid': len(issues) == 0,
        'issues': issues,
        'warnings': warnings,
        'word_count': word_count,
    }

def main():
    parser = argparse.ArgumentParser(description='Validate content draft')
    parser.add_argument('--draft', required=True, help='Path to draft file')
    parser.add_argument('--type', default='blog', help='Content type')
    args = parser.parse_args()
    
    result = validate_draft(args.draft, args.type)
    
    print(f"Word count: {result['word_count']}")
    
    if result['issues']:
        print("\nIssues (must fix):")
        for issue in result['issues']:
            print(f"  ✗ {issue}")
    
    if result['warnings']:
        print("\nWarnings (review):")
        for warning in result['warnings']:
            print(f"  ⚠ {warning}")
    
    if result['valid'] and not result['warnings']:
        print("\n✓ Draft valid")
    
    sys.exit(0 if result['valid'] else 1)

if __name__ == '__main__':
    main()