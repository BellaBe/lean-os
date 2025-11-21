#!/usr/bin/env python3
"""
Content Draft Validation Script

Checks draft quality against brand voice, factual accuracy, and pattern compliance.
"""

import re
import sys
from pathlib import Path
from typing import Dict, List, Tuple


class DraftValidator:
    """Validate content draft quality."""
    
    # Brand voice violations (sales language patterns)
    SALES_LANGUAGE = [
        r'\b(revolutionary|cutting-edge|game-changing|unprecedented)\b',
        r'\b(book\s+a\s+demo|sign\s+up\s+now|get\s+started\s+today)\b',
        r'\b(leverage|synergy|paradigm\s+shift|disrupt)\b',
        r'!{2,}',  # Multiple exclamation marks
        r'\b(amazing|incredible|fantastic|awesome)\b(?!\s+in\s+the\s+sense)',
    ]
    
    # Vague claims (should have specific numbers)
    VAGUE_CLAIMS = [
        r'\b(many|several|numerous|significant|substantial)\b',
        r'\b(dramatically|significantly|greatly)\s+(improve|increase|reduce)',
        r'\b(much\s+(better|faster|cheaper|higher|lower))\b',
    ]
    
    # Required elements for SEO (blog only)
    SEO_CHECKS = {
        'keyword_in_title': lambda content, keyword: keyword.lower() in content.split('\n')[0].lower(),
        'keyword_in_first_100': lambda content, keyword: keyword.lower() in content[:500].lower(),
        'h2_subheadings': lambda content, _: len(re.findall(r'^## ', content, re.MULTILINE)) >= 3,
    }
    
    def __init__(self, draft_path: str):
        self.draft_path = Path(draft_path)
        self.content = self._load_draft()
        self.metadata = self._parse_metadata()
        self.errors: List[str] = []
        self.warnings: List[str] = []
        
    def _load_draft(self) -> str:
        """Load draft file."""
        if not self.draft_path.exists():
            raise FileNotFoundError(f"Draft not found: {self.draft_path}")
        return self.draft_path.read_text()
    
    def _parse_metadata(self) -> Dict[str, str]:
        """Extract YAML frontmatter."""
        match = re.search(r'^---\n(.*?)\n---', self.content, re.DOTALL)
        if not match:
            self.errors.append("Missing YAML frontmatter")
            return {}
        
        metadata = {}
        for line in match.group(1).split('\n'):
            if ':' in line:
                key, value = line.split(':', 1)
                metadata[key.strip()] = value.strip().strip('"')
        return metadata
    
    def validate_brand_voice(self) -> None:
        """Check for sales language violations."""
        # Remove frontmatter and editor notes for analysis
        body = re.sub(r'^---.*?---', '', self.content, flags=re.DOTALL)
        body = re.sub(r'## Editor Notes.*$', '', body, flags=re.DOTALL)
        
        for pattern in self.SALES_LANGUAGE:
            matches = re.finditer(pattern, body, re.IGNORECASE)
            for match in matches:
                context = self._get_context(body, match.start())
                self.errors.append(
                    f"Sales language detected: '{match.group()}' in '{context}'"
                )
        
        # Check for vague claims
        for pattern in self.VAGUE_CLAIMS:
            matches = re.finditer(pattern, body, re.IGNORECASE)
            for match in matches:
                context = self._get_context(body, match.start())
                self.warnings.append(
                    f"Vague claim: '{match.group()}' in '{context}' - Use specific numbers"
                )
    
    def validate_structure(self) -> None:
        """Check pattern compliance."""
        content_type = self.metadata.get('content_type', '')
        
        if not content_type:
            self.errors.append("Missing content_type in metadata")
            return
        
        # Check word count
        word_count = len(re.findall(r'\b\w+\b', self.content))
        expected_ranges = {
            'blog': (800, 2500),
            'case-study': (1000, 1800),
            'announcement': (400, 700),
            'linkedin': (300, 600),
            'email': (400, 600),
        }
        
        if content_type in expected_ranges:
            min_words, max_words = expected_ranges[content_type]
            if word_count < min_words:
                self.warnings.append(
                    f"Word count {word_count} below minimum {min_words} for {content_type}"
                )
            elif word_count > max_words:
                self.warnings.append(
                    f"Word count {word_count} above maximum {max_words} for {content_type}"
                )
        
        # Check for required sections (H2 headers)
        h2_headers = re.findall(r'^## (.+)$', self.content, re.MULTILINE)
        if len(h2_headers) < 3 and content_type in ['blog', 'case-study']:
            self.warnings.append(
                f"Only {len(h2_headers)} H2 sections found - expected at least 3"
            )
    
    def validate_seo(self) -> None:
        """Check SEO readiness (blog only)."""
        content_type = self.metadata.get('content_type', '')
        if content_type != 'blog':
            return
        
        keyword = self.metadata.get('target_keyword', '')
        if not keyword:
            self.warnings.append("Missing target_keyword in metadata (SEO)")
            return
        
        for check_name, check_fn in self.SEO_CHECKS.items():
            if not check_fn(self.content, keyword):
                self.warnings.append(
                    f"SEO issue: {check_name.replace('_', ' ')} for keyword '{keyword}'"
                )
    
    def validate_completeness(self) -> None:
        """Check for TODO markers and incomplete sections."""
        todos = re.findall(r'TODO|TK|XXX|\[.*?\]', self.content, re.IGNORECASE)
        if todos:
            self.errors.append(
                f"Draft incomplete: {len(todos)} TODO markers found"
            )
        
        # Check for empty sections
        empty_sections = re.findall(
            r'^## (.+)\n\n##', self.content, re.MULTILINE
        )
        if empty_sections:
            self.errors.append(
                f"Empty sections: {', '.join(empty_sections)}"
            )
    
    def _get_context(self, text: str, position: int, length: int = 60) -> str:
        """Get surrounding context for error reporting."""
        start = max(0, position - 30)
        end = min(len(text), position + length)
        return f"...{text[start:end]}..."
    
    def run(self) -> Tuple[bool, str]:
        """Run all validation checks."""
        self.validate_brand_voice()
        self.validate_structure()
        self.validate_seo()
        self.validate_completeness()
        
        # Build report
        report = []
        
        if self.errors:
            report.append("❌ ERRORS (Must Fix):")
            for error in self.errors:
                report.append(f"  - {error}")
        
        if self.warnings:
            report.append("\n⚠️  WARNINGS (Review Recommended):")
            for warning in self.warnings:
                report.append(f"  - {warning}")
        
        if not self.errors and not self.warnings:
            report.append("✅ Draft passes all validation checks")
        
        passed = len(self.errors) == 0
        return passed, '\n'.join(report)


def main():
    """CLI entry point."""
    if len(sys.argv) < 2:
        print("Usage: python validate_draft.py <draft_path>")
        sys.exit(1)
    
    draft_path = sys.argv[1]
    
    try:
        validator = DraftValidator(draft_path)
        passed, report = validator.run()
        
        print(report)
        sys.exit(0 if passed else 1)
        
    except Exception as e:
        print(f"❌ Validation failed: {e}")
        sys.exit(1)


if __name__ == '__main__':
    main()