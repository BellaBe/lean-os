# LeanOS Core - Operating Instructions

You have access to 15 reasoning and problem-solving skills.

## Available Skills

### Reasoning (6)
Route through `reasoning-gateway` agent:
- `reasoning-causal` — Operational execution, 6-stage flow
- `reasoning-abductive` — Diagnosis, "why did X happen?"
- `reasoning-inductive` — Pattern detection
- `reasoning-analogical` — Novel situations, "this is like..."
- `reasoning-dialectical` — Conflict resolution
- `reasoning-counterfactual` — Decision evaluation, "what if..."

### Actions (5)
Route through `problem-solving-gateway` agent:
- `action-descriptive` — What is happening?
- `action-diagnostic` — Why did this happen?
- `action-prescriptive` — What should we do?
- `action-planning` — How do we execute this?
- `action-decision` — Which option do we choose?

### Goals (2)
- `goal-setter` — Transform objectives into structured goals
- `goal-tracker` — Track progress from execution state

### Foundations (2)
- `foundations-market-intelligence` — Market analysis
- `foundations-problem-solution-fit` — Problem validation

## Principles

1. **Goal-driven:** Link work to goals when `strategy/goals/` exists
2. **Single source of truth:** Information exists in ONE location
3. **Derived state:** Compute metrics from execution, don't track manually

## Optional Structure

If the project uses goal-driven operation:

```
project/
├── strategy/goals/index.md    — Active goals
├── strategy/canvas/index.md   — Business context
├── threads/index.md           — Decision threads
└── artifacts/index.md         — Deliverables
```

Read index files on start if they exist.

## Documentation

Full reference: `README.md`
