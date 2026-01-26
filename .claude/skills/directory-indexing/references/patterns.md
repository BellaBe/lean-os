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
*.md
meta.json (read for thread metadata, not indexed as doc)
```

---

## Description Extraction

```python
def get_snapshot(path: str) -> str:
    """Extract description from meta.json, heading, or first line."""
    
    # For thread directories — read meta.json
    meta_path = os.path.join(path, 'meta.json')
    if os.path.isdir(path) and os.path.exists(meta_path):
        meta = json.load(open(meta_path))
        return truncate(meta.get('description', meta.get('name', '')))
    
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

## Thread Leaf Detection

```python
def is_thread_leaf(dir_path: str) -> bool:
    """Check if directory is a thread (contains meta.json)."""
    return os.path.exists(os.path.join(dir_path, 'meta.json'))

def should_create_index(dir_path: str) -> bool:
    """Do not create index inside thread directories."""
    return not is_thread_leaf(dir_path)
```

---

## Thread Index Generation

```python
def index_thread_type(type_dir: str) -> str:
    """Generate index for a thread type directory (e.g., campaigns/)."""
    lines = [f"# {basename(type_dir).title()}", ""]
    
    for thread in sorted(listdir(type_dir)):
        thread_path = join(type_dir, thread)
        if is_thread_leaf(thread_path):
            meta = json.load(open(join(thread_path, 'meta.json')))
            desc = meta.get('description', '')
            lines.append(f"- [{thread}](./{thread}/) — {truncate(desc)}")
    
    lines.extend(["", f"↑ [{basename(dirname(type_dir)).title()}](../)"])
    return '\n'.join(lines)
```