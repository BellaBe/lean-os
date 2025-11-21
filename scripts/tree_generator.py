#!/usr/bin/env python3
"""
Directory Tree Generator

Creates an ASCII tree visualization of directory structure.
Supports filtering by file extensions and custom ignore patterns.

Examples:
  python tree.py --dir ./docs
  python tree.py --dir . --max-depth 3
  python tree.py --dir ./src --extensions .py .js
  python tree.py --dir . --ignore node_modules build
"""

import sys
import argparse
from pathlib import Path
from typing import Set, List, Optional
import fnmatch

DEFAULT_IGNORE_PATTERNS: Set[str] = {
    '.git', '.svn', '.hg',
    '__pycache__', '*.pyc', '*.pyo', '*.pyd', '.Python', '*.egg-info',
    'venv', 'env', '.venv', '.env', 'virtualenv',
    'node_modules', 'npm-debug.log', 'yarn-error.log', 'pnpm-lock.yaml',
    '.idea', '.vscode', '*.swp', '*.swo', '.DS_Store', 'Thumbs.db',
    'build', 'dist', 'target', '.parcel-cache', '.next', '.turbo', '.vercel',
    '.coverage', '.pytest_cache', '.mypy_cache', '.tox', 'coverage', 'htmlcov', "CLAUDE.md", "scripts",
}

def should_ignore(path: Path, patterns: Set[str]) -> bool:
    """Check if path matches any ignore pattern."""
    name = path.name
    for pattern in patterns:
        if fnmatch.fnmatch(name, pattern):
            return True
    return False

def should_include_file(path: Path, extensions: Optional[Set[str]]) -> bool:
    """Check if file should be included based on extension filter."""
    if extensions is None:
        return True
    return path.suffix.lower() in extensions

def build_tree(
    root: Path,
    ignore_patterns: Set[str],
    extensions: Optional[Set[str]] = None,
    max_depth: Optional[int] = None,
    show_hidden: bool = False
) -> List[str]:
    """
    Build ASCII tree of directory structure.
    
    Args:
        root: Root directory to start from
        ignore_patterns: Set of patterns to ignore
        extensions: Set of file extensions to include (None = all)
        max_depth: Maximum depth to traverse (None = unlimited)
        show_hidden: Whether to show hidden files/dirs
    """
    lines: List[str] = []
    
    def list_dir(d: Path, prefix: str = "", depth: int = 0):
        if max_depth is not None and depth >= max_depth:
            return
        
        try:
            entries = list(d.iterdir())
        except PermissionError:
            lines.append(prefix + "[Permission Denied]")
            return
        
        # Filter entries
        dirs = []
        files = []
        
        for p in entries:
            # Skip hidden unless explicitly allowed
            if not show_hidden and p.name.startswith('.'):
                continue
            
            # Skip ignored patterns
            if should_ignore(p, ignore_patterns):
                continue
            
            if p.is_dir():
                dirs.append(p)
            elif p.is_file():
                # Apply extension filter to files
                if should_include_file(p, extensions):
                    files.append(p)
        
        # Sort alphabetically
        dirs.sort(key=lambda p: p.name.lower())
        files.sort(key=lambda p: p.name.lower())
        
        items = dirs + files
        
        for i, p in enumerate(items):
            is_last = (i == len(items) - 1)
            branch = "└── " if is_last else "├── "
            child_prefix = prefix + ("    " if is_last else "│   ")
            
            if p.is_dir():
                lines.append(prefix + branch + p.name + "/")
                list_dir(p, child_prefix, depth + 1)
            else:
                # Show file size
                try:
                    size = p.stat().st_size
                    size_str = format_size(size)
                    lines.append(prefix + branch + p.name + f" ({size_str})")
                except OSError:
                    lines.append(prefix + branch + p.name)
    
    # Root line
    lines.append(f"{root.name}/")
    list_dir(root, "", 0)
    return lines

def format_size(size: float) -> str:
    """Format file size in human-readable format."""
    for unit in ['B', 'KB', 'MB', 'GB']:
        if size < 1024.0:
            return f"{size:.1f}{unit}"
        size /= 1024.0
    return f"{size:.1f}TB"

def main() -> int:
    parser = argparse.ArgumentParser(
        description="Generate ASCII tree of directory structure."
    )
    parser.add_argument(
        '--dir',
        type=str,
        default='.',
        help='Directory to start from (default: current directory)'
    )
    parser.add_argument(
        '--max-depth',
        type=int,
        default=None,
        help='Maximum depth to traverse (default: unlimited)'
    )
    parser.add_argument(
        '--extensions',
        nargs='+',
        default=None,
        help='File extensions to include (e.g., .py .js .md)'
    )
    parser.add_argument(
        '--ignore',
        nargs='+',
        default=[],
        help='Additional patterns to ignore'
    )
    parser.add_argument(
        '--show-hidden',
        action='store_true',
        help='Show hidden files and directories'
    )
    parser.add_argument(
        '--no-default-ignores',
        action='store_true',
        help='Disable default ignore patterns'
    )
    parser.add_argument(
        '--output',
        type=str,
        default=None,
        help='Output file (default: stdout)'
    )
    
    args = parser.parse_args()
    
    root = Path(args.dir).resolve()
    if not root.exists() or not root.is_dir():
        print(f"Error: {root} does not exist or is not a directory", file=sys.stderr)
        return 1
    
    # Build ignore patterns
    if args.no_default_ignores:
        ignore_patterns = set(args.ignore)
    else:
        ignore_patterns = set(DEFAULT_IGNORE_PATTERNS)
        ignore_patterns.update(args.ignore)
    
    # Build extensions set
    extensions = None
    if args.extensions:
        extensions = {ext.lower() if ext.startswith('.') else f'.{ext.lower()}' 
                     for ext in args.extensions}
    
    # Generate tree
    tree_lines = build_tree(
        root,
        ignore_patterns,
        extensions,
        args.max_depth,
        args.show_hidden
    )
    
    # Output
    output = '\n'.join(tree_lines) + '\n'
    
    if args.output:
        out_path = Path(args.output)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(output, encoding='utf-8')
        print(f"Tree written to {out_path}")
    else:
        sys.stdout.write(output)
    
    return 0

if __name__ == "__main__":
    sys.exit(main())