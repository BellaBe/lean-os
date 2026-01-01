#!/usr/bin/env python3
"""
Selective Markdown Flattener (one output file)

Goal:
- Produce ONE one-pager that includes Markdown content ONLY from directories whose
  directory name matches a prefix rule (or other match mode).
- Include a directory tree restricted to the included dirs/files.
- Indicate the output filepath.

Example:
  python flatten_dir.py --dir .claude/skills --prefix engineering

What it does:
- Traverses --dir recursively
- Selects "included roots" = directories where dir.name startswith(--prefix) by default
- Collects Markdown files under ONLY those included roots
- Builds a tree that shows ONLY included roots, their subdirs, and markdown files
- Concatenates markdown files into a single output file

Notes:
- If you want "prefix is a path segment anywhere", not "directory basename startswith",
  use --match contains (or regex).
- Ordering: per-directory numeric precedence (e.g. 1.intro.md before foo.md), same as your script.
"""

import os
import sys
import re
import argparse
from pathlib import Path
from typing import Set, Iterable, Tuple, List, Optional
import fnmatch
from datetime import datetime

DEFAULT_IGNORE_PATTERNS: Set[str] = {
    '.git', '.svn', '.hg',
    '__pycache__', '*.pyc', '*.pyo', '*.pyd', '.Python', '*.egg-info',
    'venv', 'env', '.venv', '.env', 'virtualenv',
    'node_modules', 'npm-debug.log', 'yarn-error.log', 'pnpm-lock.yaml',
    '.idea', '.vscode', '*.swp', '*.swo', '.DS_Store', 'Thumbs.db',
    'build', 'dist', 'target', '.parcel-cache', '.next', '.turbo', '.vercel',
    '.coverage', '.pytest_cache', '.mypy_cache', '.tox', 'coverage', 'htmlcov',
    '.dockerignore',
    'scripts',
    '.one-pagers',
    'CLAUDE.md',
}

MD_EXTS = {'.md', '.markdown'}

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

def should_ignore(path: Path, patterns: Set[str]) -> bool:
    name = path.name
    for pattern in patterns:
        if fnmatch.fnmatch(name, pattern):
            return True
    return False

def iter_matching_dirs(root: Path, prefix: str, ignore_patterns: Set[str], match_mode: str, regex: Optional[re.Pattern]) -> List[Path]:
    """
    Return included root directories under `root` based on match rule.
    These are the roots whose *subtrees* will be flattened.
    """
    matches: List[Path] = []

    for dirpath, dirnames, _filenames in os.walk(root):
        dpath = Path(dirpath)
        # prune ignored dirs
        dirnames[:] = sorted([d for d in dirnames if not should_ignore(dpath / d, ignore_patterns)], key=str.lower)

        name = dpath.name
        ok = False
        if match_mode == "startswith":
            ok = name.startswith(prefix)
        elif match_mode == "equals":
            ok = name == prefix
        elif match_mode == "contains":
            ok = prefix in name
        elif match_mode == "regex":
            ok = bool(regex and regex.search(name))
        else:
            raise ValueError(f"Unknown match mode: {match_mode}")

        if ok:
            matches.append(dpath)
            # Important: do NOT descend further; treat this as an included root subtree
            dirnames[:] = []

    # de-dupe & stable sort
    uniq = sorted(set(matches), key=lambda p: str(p).lower())
    return uniq

def iter_md_files_under(roots: List[Path], ignore_patterns: Set[str]) -> Iterable[Path]:
    """
    Deterministic traversal with per-dir numeric precedence, across multiple roots.
    """
    for root in roots:
        for dirpath, dirnames, filenames in os.walk(root):
            dpath = Path(dirpath)
            dirnames[:] = sorted([d for d in dirnames if not should_ignore(dpath / d, ignore_patterns)], key=str.lower)
            for fname in sorted(filenames, key=filename_key):
                fpath = dpath / fname
                if should_ignore(fpath, ignore_patterns):
                    continue
                if fpath.suffix.lower() in MD_EXTS and fpath.is_file():
                    yield fpath

def build_tree_for_included_roots(base_root: Path, included_roots: List[Path], ignore_patterns: Set[str]) -> List[str]:
    """
    Build a tree that shows ONLY included roots (relative to base_root) and their
    subfolders + markdown files.
    """
    lines: List[str] = []

    def list_dir(d: Path, prefix: str):
        try:
            entries = list(d.iterdir())
        except PermissionError:
            lines.append(prefix + "[Permission Denied]")
            return

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

    # header
    lines.append(f"{base_root.name}/")
    if not included_roots:
        lines.append("└── [no matching directories]")
        return lines

    # Render each included root under the base
    for idx, r in enumerate(included_roots):
        is_last_root = (idx == len(included_roots) - 1)
        branch = "└── " if is_last_root else "├── "
        child_prefix = "    " if is_last_root else "│   "

        try:
            rel_root = r.resolve().relative_to(base_root.resolve())
            rel_label = str(rel_root).replace("\\", "/") + "/"
        except Exception:
            rel_label = str(r) + "/"

        lines.append(branch + rel_label)
        list_dir(r, child_prefix)

    return lines

def read_text(path: Path, max_bytes: int) -> str:
    try:
        st = path.stat()
        if st.st_size > max_bytes:
            return f"[SKIPPED: {path} is {st.st_size:,} bytes > max-size]\n"
        return path.read_text(encoding='utf-8')
    except UnicodeDecodeError:
        return f"[SKIPPED: {path} not valid UTF-8]\n"
    except Exception as e:
        return f"[SKIPPED: error reading {path}: {e}]\n"

def default_output_path(root: Path, prefix: str) -> Path:
    # Keep it simple + deterministic: put output under <root>/.one-pagers
    out_dir = root / "scripts" / "outputs" / "by_prefix"
    out_dir.mkdir(parents=True, exist_ok=True)
    safe_prefix = re.sub(r"[^A-Za-z0-9._-]+", "_", prefix).strip("_") or "prefix"
    return out_dir / f"{safe_prefix}_one_pager.md"

def main() -> int:
    parser = argparse.ArgumentParser(
        description="Flatten Markdown from selected directories (by dir-name prefix) into ONE file, with a tree header."
    )
    parser.add_argument('--dir', required=True, type=str, help='Base directory to traverse.')
    parser.add_argument('--prefix', required=True, type=str, help='Prefix (or pattern) used to select directories.')
    parser.add_argument('--match', choices=['startswith', 'equals', 'contains', 'regex'], default='startswith',
                        help='How to match directory names against --prefix. Default: startswith.')
    parser.add_argument('--base', type=str, default=None,
                        help='Base dir for relative paths in headers. Default: value of --dir.')
    parser.add_argument('--ignore', action='append', default=[],
                        help='Additional ignore patterns. Can be used multiple times.')
    parser.add_argument('--max-size', type=int, default=10 * 1024 * 1024,
                        help='Max file size to include, bytes. Default 10MB.')
    parser.add_argument('--stdout', action='store_true', help='Write result to stdout.')
    parser.add_argument('--output', type=str, default=None,
                        help='Output file path. If omitted and not using --stdout, writes to <dir>/.one-pagers/<prefix>_one_pager.md')
    args = parser.parse_args()

    base_root = Path(args.dir).resolve()
    if not base_root.exists() or not base_root.is_dir():
        print(f"Error: directory does not exist or is not a directory: {base_root}", file=sys.stderr)
        return 1

    base = Path(args.base).resolve() if args.base else base_root

    ignore_patterns = set(DEFAULT_IGNORE_PATTERNS)
    ignore_patterns.update(args.ignore)

    rx = re.compile(args.prefix) if args.match == "regex" else None
    included_roots = iter_matching_dirs(base_root, args.prefix, ignore_patterns, args.match, rx)

    # Collect md files under included roots
    md_files = list(iter_md_files_under(included_roots, ignore_patterns))

    # Build restricted tree
    tree_lines = build_tree_for_included_roots(base_root, included_roots, ignore_patterns)

    now = datetime.now().isoformat(timespec="seconds")
    sections: List[str] = []
    header_line = "=" * 80

    sections.append(header_line)
    sections.append(f"Selective Markdown Tree for: {base_root}")
    sections.append(f"Selection: match={args.match} pattern={args.prefix}")
    sections.append(f"Generated: {now}")
    sections.append(f"Included roots: {len(included_roots)}")
    sections.append(header_line)
    sections.extend(tree_lines)
    sections.append("")

    sections.append(header_line)
    sections.append(f"Concatenated Markdown (selected dirs only) From: {base_root}")
    sections.append(f"Total files: {len(md_files)}")
    sections.append(header_line)
    sections.append("")

    # File content
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

    out_path = Path(args.output).resolve() if args.output else default_output_path(base_root, args.prefix)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(output_text, encoding='utf-8')

    print(f"Wrote {len(output_text.encode('utf-8')):,} bytes to {out_path}")
    if included_roots:
        print("Included directories:")
        for r in included_roots:
            try:
                rr = r.resolve().relative_to(base_root.resolve())
            except Exception:
                rr = r
            print(f"  - {rr}")
    else:
        print("Included directories: (none matched)")
    return 0

if __name__ == "__main__":
    sys.exit(main())
