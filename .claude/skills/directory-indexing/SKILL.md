---
name: directory-indexing
description: Generates index.md files listing .md documentation. Pure navigation — what exists and where. No code files. Triggers on "index", "catalog", "build index".
allowed-tools: Read, Grep, Glob, Bash
license: Complete terms in LICENSE.txt
---

# Directory Indexer

Generate or update index.md files — yellow pages for directories.

## Principles

1. **List what exists** — Names and links only
2. **No judgment** — No status, flags, or inference
3. **Hierarchical nav** — ↑ parent · → related
4. **Docs only** — No code files (separate code-mapper skill)

## Excludes

Directories: `node_modules`, `.git`, `.venv`, `__pycache__`, `src`, `lib`, `dist`, `build`, `vendor`

Files: `*.py`, `*.js`, `*.ts`, `*.jsx`, `*.tsx`, `*.go`, `*.rs`, `*.java`, `*.rb`, `*.php`, `*.c`, `*.cpp`, `*.h`, `*.css`, `*.scss`, `*.json`, `*.yaml`, `*.yml`, `*.toml`, `*.lock`, `*.sum`

## Directory Types

| Pattern | Subdirs |
|---------|---------|
| `artifacts/` | sales, marketing, engineering, operations, etc |
| `docs/` | references, workflows, etc |
| `meeting-notes/` | as found |
| `research/` | customer, market, etc |
| `strategy/` | canvas, goals, financial, etc |
| `threads/` | {domain}/{type}/{thread}/ — see Threads Structure |
| any other | as found |

## Threads Structure

```
threads/
├── index.md
├── marketing/
│   ├── index.md
│   └── campaigns/
│       ├── index.md          ← lists threads from meta.json
│       └── {thread_name}/
│           ├── meta.json     ← source for index entry
│           └── ...           ← NO index.md here
├── sales/
├── engineering/
└── operations/
```

**Rules:**
1. **Stop at meta.json** — If directory contains `meta.json`, it's a thread leaf. Do NOT create index inside.
2. **Read meta.json** — Extract `name`, `description` for parent index entry.
3. **Index at type level** — `campaigns/index.md` lists all threads under it.

**meta.json schema:**
```json
{
  "name": "Thread display name",
  "description": "Short snapshot for index"
}
```

**Generated index (e.g., `campaigns/index.md`):**
```markdown
# Campaigns

- [spring-launch](./spring-launch/) — Q1 product launch campaign
- [rebrand](./rebrand/) — Brand refresh initiative

↑ [Marketing](../)
```

## Process

### 1. Scan
```bash
find {root} -type f -name "*.md" \
  ! -path "*/node_modules/*" \
  ! -path "*/.git/*" \
  ! -path "*/src/*" \
  ! -path "*/lib/*" \
  ! -path "*/dist/*" \
  ! -path "*/build/*" \
  ! -path "*/vendor/*"
```

### 2. Check for Thread Leaf
```bash
# If meta.json exists, this is a thread — do NOT index inside
if [ -f "{dir}/meta.json" ]; then
  # Skip — parent will index this via meta.json
  exit
fi
```

### 3. List
For .md files: `- [{name}](./{name}.md) — {snapshot}`
For dirs: `- [{name}](./{name}/) — {snapshot}`
For threads (has meta.json): read `name` and `description` from meta.json

Description: first heading or first line — max 40 chars, truncate with `…`

### 4. Link Navigation
- `↑ [Parent](../)`
- `→ [Related](../related/)`

### 5. Recurse
For subdirs with content → generate index → link ↑↓
**Exception:** Do not recurse into directories containing `meta.json`

## Output Format

```markdown
# {Directory Name}

- [{item}](./{item}/) — {snapshot}
- [{item}](./{item}.md) — {snapshot}

↑ [Parent](../)
```

## Examples

**Artifacts:**
```markdown
# Artifacts

## sales
- [q4-deck](./sales/q4-deck/) — Q4 investor pitch materials
- [prospects](./sales/prospects/) — Enterprise lead tracking

## engineering
- [auth-service](./engineering/auth-service/) — OAuth2 implementation

→ [Strategy](../strategy/) · [Threads](../threads/)
```

**Threads (domain level):**
```markdown
# Marketing

- [campaigns](./campaigns/) — Product launch campaigns
- [content](./content/) — Blog and social content

↑ [Threads](../)
```

**Threads (type level — reads from meta.json):**
```markdown
# Campaigns

- [spring-launch](./spring-launch/) — Q1 product launch campaign
- [rebrand](./rebrand/) — Brand refresh initiative

↑ [Marketing](../)
```

**Strategy:**
```markdown
# Strategy

- [Canvas](./canvas/) — Lean canvas sections
- [Goals](./goals/) — OKRs and milestones
- [Financial](./financial/) — Projections and models

→ [Artifacts](../artifacts/)
```

**Canvas:**
```markdown
# Canvas

- [00.mode](./00-mode.md) — {snapshot}
- [00.context](./00.context.md) — {snapshot}

↑ [Strategy](../)
```

## Boundaries

**Does:** List .md files, read meta.json for threads, generate links, build navigation

**Does NOT:** Index code files, create index inside thread dirs (with meta.json), infer status

## References

- `references/patterns.md` — Detection patterns for directory types and navigation
- `references/templates.md` — Index.md templates per directory type