#!/usr/bin/env python3
"""
Markdown Flattener - Unified tool for flattening markdown files

================================================================================
EXAMPLES
================================================================================

# Flatten ALL markdown files in a directory:
python scripts/md_flattener.py --dir docs
python scripts/md_flattener.py --dir .claude/skills --stdout

# Flatten by PREFIX - match directories (for skills with subdirs):
python scripts/md_flattener.py --dir .claude/skills --prefix engineering

# Flatten by PREFIX - match files directly (for agents as .md files):
python scripts/md_flattener.py --dir .claude/agents --prefix engineering --target files

# Different match modes:
python scripts/md_flattener.py --dir .claude/skills --prefix sales --match startswith
python scripts/md_flattener.py --dir .claude/agents --prefix gateway --match contains --target files
python scripts/md_flattener.py --dir docs --prefix "^(api|sdk)" --match regex

# Custom output:
python scripts/md_flattener.py --dir docs --output my_docs.md
python scripts/md_flattener.py --dir .claude/agents --prefix engineering --target files --stdout

================================================================================
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
    """Sort key: numbered files first, then alphabetical."""
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


def _matches_pattern(name: str, prefix: str, match_mode: str, regex: Optional[re.Pattern]) -> bool:
    """Check if name matches the pattern based on match mode."""
    if match_mode == "startswith":
        return name.startswith(prefix)
    elif match_mode == "equals":
        return name == prefix
    elif match_mode == "contains":
        return prefix in name
    elif match_mode == "regex":
        return bool(regex and regex.search(name))
    raise ValueError(f"Unknown match mode: {match_mode}")


# -----------------------------------------------------------------------------
# Iterators
# -----------------------------------------------------------------------------

def iter_all_md_files(root: Path, ignore_patterns: Set[str]) -> Iterable[Path]:
    """Iterate all markdown files in directory tree."""
    for dirpath, dirnames, filenames in os.walk(root):
        dpath = Path(dirpath)
        dirnames[:] = sorted([d for d in dirnames if not should_ignore(dpath / d, ignore_patterns)], key=str.lower)
        for fname in sorted(filenames, key=filename_key):
            fpath = dpath / fname
            if should_ignore(fpath, ignore_patterns):
                continue
            if fpath.suffix.lower() in MD_EXTS and fpath.is_file():
                yield fpath


def iter_matching_dirs(root: Path, prefix: str, ignore_patterns: Set[str], match_mode: str, regex: Optional[re.Pattern]) -> List[Path]:
    """Return directories matching the pattern."""
    matches: List[Path] = []
    for dirpath, dirnames, _ in os.walk(root):
        dpath = Path(dirpath)
        dirnames[:] = sorted([d for d in dirnames if not should_ignore(dpath / d, ignore_patterns)], key=str.lower)
        if _matches_pattern(dpath.name, prefix, match_mode, regex):
            matches.append(dpath)
            dirnames[:] = []  # Don't descend further
    return sorted(set(matches), key=lambda p: str(p).lower())


def iter_md_files_under(roots: List[Path], ignore_patterns: Set[str]) -> Iterable[Path]:
    """Iterate markdown files under given root directories."""
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


def iter_matching_files(root: Path, prefix: str, ignore_patterns: Set[str], match_mode: str, regex: Optional[re.Pattern]) -> List[Path]:
    """Return markdown files whose name (sans extension) matches the pattern."""
    matches: List[Path] = []
    for dirpath, dirnames, filenames in os.walk(root):
        dpath = Path(dirpath)
        dirnames[:] = sorted([d for d in dirnames if not should_ignore(dpath / d, ignore_patterns)], key=str.lower)
        for fname in sorted(filenames, key=filename_key):
            fpath = dpath / fname
            if should_ignore(fpath, ignore_patterns):
                continue
            if fpath.suffix.lower() not in MD_EXTS:
                continue
            if _matches_pattern(fpath.stem, prefix, match_mode, regex):
                matches.append(fpath)
    return sorted(set(matches), key=lambda p: str(p).lower())


# -----------------------------------------------------------------------------
# Tree builders
# -----------------------------------------------------------------------------

def build_full_tree(root: Path, ignore_patterns: Set[str]) -> List[str]:
    """Build tree of all directories and markdown files."""
    lines: List[str] = []

    def list_dir(d: Path, prefix: str):
        try:
            entries = list(d.iterdir())
        except PermissionError:
            lines.append(prefix + "[Permission Denied]")
            return

        dirs = [p for p in entries if p.is_dir() and not should_ignore(p, ignore_patterns)]
        files = [p for p in entries if p.is_file() and not should_ignore(p, ignore_patterns) and p.suffix.lower() in MD_EXTS]
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

    lines.append(f"{root.name}/")
    list_dir(root, "")
    return lines


def build_tree_for_roots(base_root: Path, included_roots: List[Path], ignore_patterns: Set[str]) -> List[str]:
    """Build tree showing only included root directories and their contents."""
    lines: List[str] = []

    def list_dir(d: Path, prefix: str):
        try:
            entries = list(d.iterdir())
        except PermissionError:
            lines.append(prefix + "[Permission Denied]")
            return

        dirs = [p for p in entries if p.is_dir() and not should_ignore(p, ignore_patterns)]
        files = [p for p in entries if p.is_file() and not should_ignore(p, ignore_patterns) and p.suffix.lower() in MD_EXTS]
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

    lines.append(f"{base_root.name}/")
    if not included_roots:
        lines.append("└── [no matching directories]")
        return lines

    for idx, r in enumerate(included_roots):
        is_last = (idx == len(included_roots) - 1)
        branch = "└── " if is_last else "├── "
        child_prefix = "    " if is_last else "│   "
        try:
            rel = r.resolve().relative_to(base_root.resolve())
            label = str(rel).replace("\\", "/") + "/"
        except Exception:
            label = str(r) + "/"
        lines.append(branch + label)
        list_dir(r, child_prefix)

    return lines


def build_tree_for_files(base_root: Path, matched_files: List[Path]) -> List[str]:
    """Build tree showing matched files."""
    lines: List[str] = [f"{base_root.name}/"]
    if not matched_files:
        lines.append("└── [no matching files]")
        return lines

    for idx, f in enumerate(matched_files):
        is_last = (idx == len(matched_files) - 1)
        branch = "└── " if is_last else "├── "
        try:
            rel = f.resolve().relative_to(base_root.resolve())
        except ValueError:
            rel = f.name
        lines.append(branch + str(rel))

    return lines


# -----------------------------------------------------------------------------
# Helpers
# -----------------------------------------------------------------------------

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


def default_output_path(root: Path, prefix: Optional[str]) -> Path:
    """Generate output path in scripts/output/."""
    script_dir = Path(__file__).resolve().parent
    out_dir = script_dir / "output"
    out_dir.mkdir(parents=True, exist_ok=True)
    source_name = root.name or "root"
    if prefix:
        safe_prefix = re.sub(r"[^A-Za-z0-9._-]+", "_", prefix).strip("_") or "prefix"
        return out_dir / f"{source_name}_{safe_prefix}_one_pager.md"
    return out_dir / f"{source_name}_one_pager.md"


# -----------------------------------------------------------------------------
# Main
# -----------------------------------------------------------------------------

def main() -> int:
    parser = argparse.ArgumentParser(
        description="Flatten Markdown files into a single file with tree header.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # All files:     python md_flattener.py --dir docs
  # By prefix:     python md_flattener.py --dir .claude/skills --prefix engineering
  # Files mode:    python md_flattener.py --dir .claude/agents --prefix engineering --target files
"""
    )
    parser.add_argument('--dir', required=True, type=str, help='Directory to traverse.')
    parser.add_argument('--prefix', type=str, default=None, help='Prefix pattern to filter by. If omitted, includes all files.')
    parser.add_argument('--target', choices=['dirs', 'files'], default='dirs',
                        help='What to match when using --prefix: dirs (default) or files.')
    parser.add_argument('--match', choices=['startswith', 'equals', 'contains', 'regex'], default='startswith',
                        help='How to match against --prefix. Default: startswith.')
    parser.add_argument('--base', type=str, default=None, help='Base dir for relative paths. Default: --dir value.')
    parser.add_argument('--ignore', action='append', default=[], help='Additional ignore patterns.')
    parser.add_argument('--max-size', type=int, default=10 * 1024 * 1024, help='Max file size in bytes. Default: 10MB.')
    parser.add_argument('--stdout', action='store_true', help='Write to stdout instead of file.')
    parser.add_argument('--output', type=str, default=None, help='Output file path. Default: scripts/output/<name>_one_pager.md')
    args = parser.parse_args()

    base_root = Path(args.dir).resolve()
    if not base_root.exists() or not base_root.is_dir():
        print(f"Error: not a directory: {base_root}", file=sys.stderr)
        return 1

    base = Path(args.base).resolve() if args.base else base_root
    ignore_patterns = set(DEFAULT_IGNORE_PATTERNS)
    ignore_patterns.update(args.ignore)

    # Determine mode and collect files
    if args.prefix:
        rx = re.compile(args.prefix) if args.match == "regex" else None
        if args.target == "files":
            md_files = iter_matching_files(base_root, args.prefix, ignore_patterns, args.match, rx)
            tree_lines = build_tree_for_files(base_root, md_files)
            match_info = f"Matched files: {len(md_files)}"
        else:
            included_roots = iter_matching_dirs(base_root, args.prefix, ignore_patterns, args.match, rx)
            md_files = list(iter_md_files_under(included_roots, ignore_patterns))
            tree_lines = build_tree_for_roots(base_root, included_roots, ignore_patterns)
            match_info = f"Matched dirs: {len(included_roots)}"
        selection_line = f"Selection: prefix={args.prefix} match={args.match} target={args.target}"
    else:
        md_files = list(iter_all_md_files(base_root, ignore_patterns))
        tree_lines = build_full_tree(base_root, ignore_patterns)
        match_info = f"Total files: {len(md_files)}"
        selection_line = "Selection: all"

    # Build output
    now = datetime.now().isoformat(timespec="seconds")
    sections: List[str] = []
    sep = "=" * 80

    sections.append(sep)
    sections.append(f"Markdown Tree for: {base_root}")
    sections.append(selection_line)
    sections.append(f"Generated: {now}")
    sections.append(match_info)
    sections.append(sep)
    sections.extend(tree_lines)
    sections.append("")

    sections.append(sep)
    sections.append(f"Concatenated Markdown From: {base_root}")
    sections.append(f"Total files: {len(md_files)}")
    sections.append(sep)
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

    out_path = Path(args.output).resolve() if args.output else default_output_path(base_root, args.prefix)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(output_text, encoding='utf-8')

    print(f"Wrote {len(output_text.encode('utf-8')):,} bytes to {out_path}")
    print(match_info)
    return 0


if __name__ == "__main__":
    sys.exit(main())
