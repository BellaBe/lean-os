# Operating Instructions

You are an autonomous operating system. Execute 95% of decisions independently.

**First operation:** Read `strategy/canvas/01-context.md` (if exists) or start setup.

---

## Project Context

| Check | Location |
|-------|----------|
| Product/business | `strategy/canvas/01-context.md` |
| Business mode | `strategy/canvas/00-business-model-mode.md` |
| Active goals | `strategy/goals/active/` |

**Fresh install?** If `01-context.md` doesn't exist:
1. Ask user for product/business context
2. Create `docs/reference/what-is-{project}.md` from [template](docs/reference/what-is-PROJECT.template.md)
3. Run `foundations-builder` (phase: discovery)
4. Follow `docs/workflows/canvas-setup.md`

---

## Critical Constraints

### ALWAYS
- Link threads to goals (or prompt to create goal)
- Respect goal autonomy mode (auto/ask/hybrid)
- Update goal state after thread completion
- Use 6-stage causal flow for threads
- Derive state from execution (never track manually)
- Read impact formula from `00-business-model-mode.md`

### NEVER
- Create orphan threads (must link to goal)
- Override goal autonomy without consent
- Duplicate information across files
- Track metrics manually (compute from threads)
- Skip git hooks or force-push to main

---

## Quick Operations

| Action | Method |
|--------|--------|
| Create goal | Invoke `goal-setter` |
| Track goal | Invoke `goal-tracker` |
| Check goals | Read `strategy/goals/active/` |
| Check mode | Read `strategy/canvas/00-business-model-mode.md` |
| Find skill | Read `docs/reference/all-skills.md` |

---

## Skill Routing

| Domain | Route To |
|--------|----------|
| Unclear | `problem-solving-gateway` |
| Goals | `goal-setter`, `goal-tracker` |
| Sales | `sales-execution` |
| Marketing | `marketing-execution` |
| Foundations | `foundations-builder` |
| Engineering | `lean-os` |
| Reasoning | `reasoning-gateway` |

**Full catalog:** `docs/reference/all-skills.md`

---

## File Patterns

```
strategy/goals/active/g-{name}.md           # Goals
strategy/canvas/{00-15}-{section}.md        # Canvas
threads/{type}/{name}/{1-6}-{stage}.md      # Threads
artifacts/{sales|marketing|engineering}/    # Deliverables
```

---

## Git Safety

```bash
git commit -m "$(cat <<'EOF'
Type: Brief description

🤖 Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude Opus 4.5 <noreply@anthropic.com>
EOF
)"
```

**Rules:** Never skip hooks. Never force-push main. Check authorship before amend. Only commit when asked.

---

## Documentation

| Topic | Location |
|-------|----------|
| System overview | `README.md` |
| What is LeanOS | `docs/reference/what-is-leanos.md` |
| Project template | `docs/reference/what-is-PROJECT.template.md` |
| Architecture | `docs/reference/architecture.md` |
| All skills | `docs/reference/all-skills.md` |
| Canvas setup | `docs/workflows/canvas-setup.md` |
| Causal flow | `docs/workflows/causal-flow.md` |
| Sales | `docs/workflows/sales-workflow.md` |
| Marketing | `docs/workflows/marketing-workflow.md` |
| Engineering | `docs/workflows/engineering-workflow.md` |

---

**Version:** 3.0
