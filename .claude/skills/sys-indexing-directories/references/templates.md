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

### Terminal child bubble-up

When a child directory is terminal (no subdirs), list its files under a `##` heading instead of linking to the directory:

```markdown
# {name}

- [{non_terminal_dir}](./{non_terminal_dir}/) — {snapshot}

## {terminal_dir}
- [{file}](./{terminal_dir}/{file}.md) — {snapshot}

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

Structure: `threads/{domain}/{thread-name}/1-input.md`

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

- [{thread-name}](./{thread-name}/) — {first heading from 1-input.md}

↑ [Threads](../)
```

**Read from 1-input.md:**
```yaml
---
thread_id: marketing_content-authority_2026q1
goal_id: distribution-q1/1.content-authority
status: active
---
# Content Authority Execution
```

**Do NOT create index inside thread directories (those with 1-input.md).**

→ [Artifacts](../artifacts/) · [Strategy](../strategy/)

---

## Strategy

Canvas and financial are terminal — their files bubble up under `##` headings.

```markdown
# Strategy

- [Goals](./goals/) — OKRs and milestones

## Canvas
- [00.mode](./canvas/00.mode.md) — {snapshot}
- [01.context](./canvas/01.context.md) — {snapshot}

## Financial
- [{name}](./financial/{file}) — {snapshot}

→ [Artifacts](../artifacts/)
```

### goals/ (non-terminal)
```markdown
# Goals

- [{goal}](./{file}) — {snapshot}

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