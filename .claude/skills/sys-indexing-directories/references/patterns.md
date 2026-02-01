# Detection Patterns

Directory type detection and navigation links.

---

## Type Detection

Match directory name:

```python
TYPES = {
    "artifacts": ["artifacts"],
    "threads": ["threads"],
    "strategy": ["strategy"],
    "features": ["features", "stories"],
    "design": ["design", "wireframes"],
    "docs": ["docs", "documentation"],
    "workflows": ["workflows", "processes"],
    "meetings": ["meetings", "meeting-notes"],
}

def detect_type(name: str) -> str:
    name = name.lower()
    for type_name, matches in TYPES.items():
        if name in matches:
            return type_name
    return "generic"
```

---

## Cross-References

Navigation links between directories:

```python
RELATED = {
    "artifacts": ["strategy", "threads"],
    "threads": ["artifacts", "strategy"],
    "strategy": ["artifacts"],
    "strategy/canvas": ["strategy/goals"],
    "strategy/goals": ["strategy/financial"],
    "features": ["design"],
    "design": ["features"],
}
```

---

## Exclusions

Directories:
```
node_modules, .git, .venv, __pycache__, src, lib, dist, build, vendor, bin, obj, target, out
```

Files (code — use code-mapper instead):
```
*.py, *.js, *.ts, *.jsx, *.tsx, *.go, *.rs, *.java, *.rb, *.php, *.c, *.cpp, *.h, *.hpp, *.cs, *.swift, *.kt, *.scala, *.css, *.scss, *.less, *.json, *.yaml, *.yml, *.toml, *.xml, *.lock, *.sum, *.mod
```

Process only:
```
*.md (including 1-input.md for thread metadata, not indexed as doc)
```

---

## Description Extraction

```python
def get_snapshot(path: str) -> str:
    """Extract description from 1-input.md, heading, or first line."""

    # For thread directories — read 1-input.md first heading
    input_path = os.path.join(path, '1-input.md')
    if os.path.isdir(path) and os.path.exists(input_path):
        content = read(input_path)
        match = re.search(r'^#\s+(.+)$', content, re.MULTILINE)
        if match:
            return truncate(match.group(1))
        return truncate(content.strip().split('\n')[0])

    # For .md files — first heading or first line
    if path.endswith('.md'):
        content = read(path)
        match = re.search(r'^#\s+(.+)$', content, re.MULTILINE)
        if match:
            return truncate(match.group(1))
        return truncate(content.strip().split('\n')[0])

    # For directories — use README.md or index.md if present
    for name in ['README.md', 'index.md']:
        readme = os.path.join(path, name)
        if os.path.exists(readme):
            return get_snapshot(readme)

    return ''

def truncate(s: str, max_len: int = 40) -> str:
    if len(s) > max_len:
        return s[:max_len-1] + '…'
    return s
```

---

## Terminal Directory Detection

```python
def is_terminal(dir_path: str) -> bool:
    """Terminal = has no subdirectories (only files)."""
    for entry in os.scandir(dir_path):
        if entry.is_dir() and entry.name not in EXCLUDED_DIRS:
            return False
    return True
```

## Thread Leaf Detection

```python
def is_thread_leaf(dir_path: str) -> bool:
    """Check if directory is a thread (contains 1-input.md)."""
    return os.path.exists(os.path.join(dir_path, '1-input.md'))

def should_create_index(dir_path: str) -> bool:
    """No index inside thread dirs or terminal dirs."""
    return not is_thread_leaf(dir_path) and not is_terminal(dir_path)
```

## Bubble-Up Logic

```python
def list_for_parent(parent_path: str) -> list[str]:
    """Generate index lines, bubbling up terminal child contents."""
    lines = []
    for entry in sorted(os.scandir(parent_path), key=lambda e: e.name):
        if entry.is_file() and entry.name.endswith('.md') and entry.name != 'index.md':
            lines.append(f"- [{stem(entry.name)}](./{entry.name}) — {get_snapshot(entry.path)}")
        elif entry.is_dir() and entry.name not in EXCLUDED_DIRS:
            if is_thread_leaf(entry.path):
                continue  # thread leaf — handled by parent index
            elif is_terminal(entry.path):
                # Bubble up: list files under ## heading
                lines.append(f"\n## {entry.name.replace('-', ' ').title()}")
                for f in sorted(os.scandir(entry.path), key=lambda e: e.name):
                    if f.is_file() and f.name.endswith('.md') and f.name != 'index.md':
                        lines.append(f"- [{stem(f.name)}](./{entry.name}/{f.name}) — {get_snapshot(f.path)}")
            else:
                lines.append(f"- [{entry.name}](./{entry.name}/) — {get_snapshot(entry.path)}")
    return lines
```

---

## Thread Index Generation

```python
def index_thread_domain(domain_dir: str) -> str:
    """Generate index for a thread domain directory (e.g., marketing/)."""
    lines = [f"# {basename(domain_dir).title()}", ""]

    for thread in sorted(listdir(domain_dir)):
        thread_path = join(domain_dir, thread)
        if is_thread_leaf(thread_path):
            desc = get_snapshot(thread_path)
            lines.append(f"- [{thread}](./{thread}/) — {truncate(desc)}")

    lines.extend(["", f"↑ [{basename(dirname(domain_dir)).title()}](../)"])
    return '\n'.join(lines)
```