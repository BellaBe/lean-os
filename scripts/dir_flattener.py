#!/usr/bin/env python3
"""
Markdown Flattener

- Builds a directory tree of only Markdown files and folders.
- Then concatenates Markdown files with clear file references.
- Numbered files like `1.intro.md` sort before non-numbered within a directory.

Examples:
  python md_flattener.py --dir ./docs --stdout
  python md_flattener.py --dir . --output scripts/output/docs_flat.md
  python md_flattener.py --dir ./packages/foo --base .
"""

import os
import sys
import re
import argparse
from pathlib import Path
from typing import Set, Iterable, Tuple, List
import fnmatch

DEFAULT_IGNORE_PATTERNS: Set[str] = {
    '.git', '.svn', '.hg',
    '__pycache__', '*.pyc', '*.pyo', '*.pyd', '.Python', '*.egg-info',
    'venv', 'env', '.venv', '.env', 'virtualenv',
    'node_modules', 'npm-debug.log', 'yarn-error.log', 'pnpm-lock.yaml',
    '.idea', '.vscode', '*.swp', '*.swo', '.DS_Store', 'Thumbs.db',
    'build', 'dist', 'target', '.parcel-cache', '.next', '.turbo', '.vercel',
    '.coverage', '.pytest_cache', '.mypy_cache', '.tox', 'coverage', 'htmlcov',
    '.dockerignore',
    'scripts',  # Exclude scripts directory
    '.one-pagers',  # Exclude one-pagers directories (auto-generated)
    'CLAUDE.md',  # Exclude CLAUDE.md at any level
}

MD_EXTS = {'.md', '.markdown'}

def should_ignore(path: Path, patterns: Set[str]) -> bool:
    name = path.name
    for pattern in patterns:
        if fnmatch.fnmatch(name, pattern):
            return True
    return False

_num_prefix_re = re.compile(r'^\s*(\d+)[\.\-_ ]')

def filename_key(fname: str) -> Tuple[int, int, str]:
    """
    Sort key for files within a directory:
      1) numbered prefix first by numeric value
      2) then non-numbered alphabetically
    """
    m = _num_prefix_re.match(fname)
    if m:
        return (0, int(m.group(1)), fname.lower())
    return (1, 0, fname.lower())

def iter_md_files(root: Path, ignore_patterns: Set[str]) -> Iterable[Path]:
    # Deterministic traversal with per-dir numeric precedence
    for dirpath, dirnames, filenames in os.walk(root):
        dpath = Path(dirpath)
        dirnames[:] = sorted(
            [d for d in dirnames if not should_ignore(dpath / d, ignore_patterns)],
            key=str.lower
        )
        for fname in sorted(filenames, key=filename_key):
            fpath = dpath / fname
            if should_ignore(fpath, ignore_patterns):
                continue
            if fpath.suffix.lower() in MD_EXTS and fpath.is_file():
                yield fpath

def build_tree(root: Path, ignore_patterns: Set[str]) -> List[str]:
    """
    Build a tree of only directories and Markdown files.
    Uses ASCII tree characters. Applies numbered-file precedence per directory.
    """
    lines: List[str] = []

    def list_dir(d: Path, prefix: str = "", is_root: bool = False):
        try:
            entries = list(d.iterdir())
        except PermissionError:
            lines.append(prefix + "[Permission Denied]")
            return

        # keep only folders and markdown files
        dirs = [p for p in entries if p.is_dir() and not should_ignore(p, ignore_patterns)]
        files = [
            p for p in entries
            if p.is_file()
            and not should_ignore(p, ignore_patterns)
            and p.suffix.lower() in MD_EXTS
        ]

        dirs.sort(key=lambda p: p.name.lower())
        files.sort(key=lambda p: filename_key(p.name))

        items = dirs + files
        for i, p in enumerate(items):
            is_last = (i == len(items) - 1)
            branch = "└── " if is_last else "├── "
            child_prefix = prefix + ("    " if is_last else "│   ")
            if p.is_dir():
                lines.append(prefix + branch + p.name + "/")
                list_dir(p, child_prefix)
            else:
                lines.append(prefix + branch + p.name)

    # root line
    lines.append(f"{root.name}/")
    list_dir(root, "", True)
    return lines

def read_text(path: Path, max_bytes: int) -> str:
    try:
        if path.stat().st_size > max_bytes:
            return f"[SKIPPED: {path} is {path.stat().st_size:,} bytes > max-size]\n"
        return path.read_text(encoding='utf-8')
    except UnicodeDecodeError:
        return f"[SKIPPED: {path} not valid UTF-8]\n"
    except Exception as e:
        return f"[SKIPPED: error reading {path}: {e}]\n"

def main() -> int:
    parser = argparse.ArgumentParser(
      description="Flatten Markdown files from a directory tree into a single file, with a tree header."
    )
    parser.add_argument('--dir', required=True, type=str,
                        help='Directory to start from. Use repo root to flatten entire repo.')
    parser.add_argument('--base', type=str, default=None,
                        help='Base dir for relative paths in headers. Default: value of --dir.')
    parser.add_argument('--ignore', action='append', default=[],
                        help='Additional ignore patterns. Can be used multiple times.')
    parser.add_argument('--max-size', type=int, default=10 * 1024 * 1024,
                        help='Max file size to include, bytes. Default 10MB.')
    parser.add_argument('--stdout', action='store_true',
                        help='Write result to stdout.')
    parser.add_argument('--output', type=str, default=None,
                        help='Output file path. Required if not using --stdout.')
    args = parser.parse_args()

    root = Path(args.dir).resolve()
    if not root.exists() or not root.is_dir():
        print(f"Error: directory does not exist or is not a directory: {root}", file=sys.stderr)
        return 1

    base = Path(args.base).resolve() if args.base else root

    ignore_patterns = set(DEFAULT_IGNORE_PATTERNS)
    ignore_patterns.update(args.ignore)

    # Build tree first
    tree_lines = build_tree(root, ignore_patterns)

    # Collect files in the same traversal policy
    md_files = list(iter_md_files(root, ignore_patterns))

    sections = []
    header_line = "=" * 80
    sections.append(header_line)
    sections.append(f"Markdown Tree for: {root}")
    sections.append(header_line)
    sections.extend(tree_lines)
    sections.append("")  # spacer
    sections.append(header_line)
    sections.append(f"Concatenated Markdown From: {root}")
    sections.append(f"Total files: {len(md_files)}")
    sections.append(header_line)
    sections.append("")

    for path in md_files:
        try:
            rel = path.resolve().relative_to(base)
        except ValueError:
            rel = path.resolve()
        content = read_text(path, args.max_size)

        sections.append(f"\n<!-- FILE: {rel} -->")
        sections.append(f"\n# {rel}\n")
        sections.append("```markdown")
        sections.append(content.rstrip("\n"))
        sections.append("```")
        sections.append("")

    output_text = "\n".join(sections) + "\n"

    if args.stdout:
        sys.stdout.write(output_text)
        return 0

    out_path = Path(args.output).resolve() if args.output else None
    if out_path is None:
        # Auto-detect business/ or engineering/ in path and route accordingly
        dir_parts = root.parts
        if 'business' in dir_parts:
            out_dir = Path.cwd() / "business" / ".one-pagers"
        elif 'engineering' in dir_parts:
            out_dir = Path.cwd() / "engineering" / ".one-pagers"
        else:
            # Fallback to scripts/output for other directories
            out_dir = Path.cwd() / "scripts" / "output"

        out_dir.mkdir(parents=True, exist_ok=True)
        dir_name = (root.name or "root").replace('/', '_').replace('\\', '_').replace('.', '_')
        out_path = out_dir / f"{dir_name}_one_pager.md"
    else:
        out_path.parent.mkdir(parents=True, exist_ok=True)

    out_path.write_text(output_text, encoding='utf-8')
    print(f"Wrote {len(output_text.encode('utf-8')):,} bytes to {out_path}")
    return 0

if __name__ == "__main__":
    sys.exit(main())