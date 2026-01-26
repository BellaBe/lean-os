# Index Templates

Format per directory type. Each item: `- [name](./path) — snapshot`

Description: first heading or first line, max 40 chars.

---

## Generic

```markdown
# {name}

- [{item}](./{item}) — {snapshot}

↑ [Parent](../)
```

---

## Artifacts

```markdown
# Artifacts

## sales
- [{name}](./sales/{name}/) — {snapshot}

## marketing
- [{name}](./marketing/{name}/) — {snapshot}

## engineering
- [{name}](./engineering/{name}/) — {snapshot}

## operations
- [{name}](./operations/{name}/) — {snapshot}

→ [Strategy](../strategy/) · [Threads](../threads/)
```

---

## Threads

Structure: `threads/{domain}/{type}/{thread}/meta.json`

### threads/index.md
```markdown
# Threads

- [Marketing](./marketing/)
- [Sales](./sales/)
- [Engineering](./engineering/)
- [Operations](./operations/)

→ [Artifacts](../artifacts/) · [Strategy](../strategy/)
```

### threads/{domain}/index.md
```markdown
# {Domain}

- [{type}](./{type}/) — {snapshot from first thread or count}

↑ [Threads](../)
```

### threads/{domain}/{type}/index.md
```markdown
# {Type}

- [{thread}](./{thread}/) — {description from meta.json}

↑ [{Domain}](../)
```

**Read from meta.json:**
```json
{
  "name": "Spring Launch",
  "description": "Q1 product launch campaign"
}
```

**Do NOT create index inside thread directories (those with meta.json).**

→ [Artifacts](../artifacts/) · [Strategy](../strategy/)

---

## Strategy

```markdown
# Strategy

- [Canvas](./canvas/) — Lean canvas sections
- [Goals](./goals/) — OKRs and milestones
- [Financial](./financial/) — Projections and models

→ [Artifacts](../artifacts/)
```

### canvas/
```markdown
# Canvas

- [00.mode](./00-mode.md) — {snapshot}
- [00.context](./00.context.md) — {snapshot}
...

↑ [Strategy](../)
```

### goals/
```markdown
# Goals

- [{goal}](./{file}) — {snapshot}

↑ [Strategy](../)
```

### financial/
```markdown
# Financial

- [{name}](./{file}) — {snapshot}

↑ [Strategy](../)
```

---

## Features

```markdown
# Features

- [{name}](./{slug}/) — {snapshot}

→ [Design](../design/)
```

---

## Design

```markdown
# Design

## flows
- [{name}](./flows/{file}) — {snapshot}

## wireframes
- [{name}](./wireframes/{file}) — {snapshot}

## components
- [{name}](./components/{file}) — {snapshot}

↑ [Features](../features/)
```

---

## Docs

```markdown
# Docs

- [{name}](./{file}) — {snapshot}

↑ [Parent](../)
```

---

## Workflows

```markdown
# Workflows

- [{name}](./{file}) — {snapshot}

↑ [Parent](../)
```

---

## Meetings

```markdown
# Meetings

- [{name}](./{file}) — {snapshot}

↑ [Parent](../)
```