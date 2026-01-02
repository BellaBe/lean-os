# 6-Stage Causal Flow

Universal decision framework for structured reasoning and execution.

**Skill:** `.claude/skills/reasoning-causal/SKILL.md`

## Relationship to Goals

Threads are the **execution layer** for goals:

```
Goal (goal-setter)
  └── Subgoal
        └── Thread (reasoning-causal) ← 6-stage execution
              └── Learning → updates Goal state + Canvas
```

**Thread types:**
- **Goal-linked:** Created from subgoals, has `goal_id` in metadata
- **Reactive:** Created from signals (no goal), may link to goal later

## Overview

Every decision flows through 6 stages:
**Input → Hypothesis → Implication → Decision → Actions → Learning**

---

## Stage 1: INPUT

**Purpose:** Capture factual observation (not opinion)

**File:** `1-input.md`

**Process:**
- Record what happened
- Include numbers, dates, names
- Link to source

**Example:**
```
{Customer} deal closed: ${ARR} ARR, {X}% {metric} improvement
Source: Signed contract + pilot results
Date: {date}
```

---

## Stage 2: HYPOTHESIS

**Purpose:** Challenge/validate Canvas assumptions

**File:** `2-hypothesis.md`

**Process:**
- Identify which assumption this tests
- Link to `strategy/canvas/10.assumptions.md`
- State confidence level

**Example:**
```
Tests: A4 - {Segment} prefer {option}
Result: Validated (5/5 chose {option})
Confidence: 60% → 95%
```

---

## Stage 3: IMPLICATION

**Purpose:** Analyze business impact with numbers

**File:** `3-implication.md`

**Process:**
- Quantify impact (revenue, cost, time)
- Calculate ROI or priority
- Identify risks

**Example:**
```
Impact: 500 sessions/month → 25 demos
Revenue: $5M pipeline influenced
Investment: 40 hours
Priority: 0.85
```

---

## Stage 4: DECISION

**Purpose:** Official commitment with mode-aware impact scoring

**File:** `4-decision.md`

**Process:**
1. Check business model mode (`strategy/canvas/00.mode.md`)
2. Calculate impact score using mode-specific formula
3. State decision (PROCEED, DEFER, DECLINE)
4. Document alternatives
5. Explain reasoning

**Impact Scoring (Mode-Aware):**

**VENTURE Mode:**
```
Impact = (Strategic Value × Market Size × Defensibility) / 3
```

**BOOTSTRAP Mode:**
```
Impact = (Revenue Impact × Time to Cash × Margin) / 3
```

**Threshold:**
- <0.8: AI proceeds autonomously
- ≥0.8: Human approval required

---

## Stage 5: ACTIONS

**Purpose:** Execute tasks

**File:** `5-actions.md` or `5-actions/` directory

**Core actions:**
- Analysis tasks
- Research tasks
- Planning tasks
- Decision tasks

---

## Stage 6: LEARNING

**Purpose:** Validate hypothesis, update Canvas AND Goal

**File:** `6-learning.md`

**Process:**
- Compile metrics
- Validate/invalidate hypothesis
- Update Canvas assumptions
- If goal-linked: Update goal state
- Detect new opportunities

**Goal Integration:**
```
If thread.goal_id exists:
  1. Read goal from strategy/goals/active/{goal_id}.md
  2. Update subgoal status (pending → completed)
  3. Extract metrics for goal state
  4. Check if goal success criteria met
```

---

## Thread Types

**Operations threads:** `threads/operations/{name}/`
- Strategic decisions
- Canvas updates
- Process improvements

**Business threads:** `threads/sales/{name}/`, `threads/marketing/{name}/`
- Deal progression (with Pro)
- Campaign execution (with Pro)
- Pipeline management (with Pro)

---

## Thread Metadata

**File:** `meta.json`

```json
{
  "id": "thread-{type}-{name}",
  "type": "operations | sales | marketing",
  "status": "active | completed | blocked",
  "created": "YYYY-MM-DD",
  "updated": "YYYY-MM-DD",
  "goal_id": "g-{goal-id}",
  "subgoal": "SG1",
  "stage": 1-6,
  "impact_score": 0.0-1.0
}
```

---

## Workflow

### Goal-Linked Thread (Primary)

```
1. Receive subgoal from goal-setter
2. Create thread: threads/{type}/{name}/
3. Set meta.json with goal_id and subgoal
4. Execute stages 1-6 sequentially
5. At Stage 4: Calculate impact, flag if ≥0.8
6. At Stage 6: Update Canvas AND goal state
7. Notify goal-tracker of completion
```

### Reactive Thread (Fallback)

```
1. Receive signal (feedback, anomaly, opportunity)
2. Create thread: threads/{type}/{name}/
3. Set meta.json without goal_id
4. Execute stages 1-6 sequentially
5. At Stage 4: Calculate impact, flag if ≥0.8
6. At Stage 6: Update Canvas
7. Optionally: Link to existing goal or spawn new goal
```

---

## References

**Skill location:** `.claude/skills/reasoning-causal/`

```
reasoning-causal/
├── SKILL.md              # Main skill file
└── references/
    ├── stages/           # Stage execution details
    │   ├── input.md
    │   ├── hypothesis.md
    │   ├── implication.md
    │   ├── decision.md
    │   ├── actions.md
    │   └── learning.md
    └── threads/          # Thread type specifics
        ├── operations.md
        ├── sales.md
        ├── marketing.md
        └── engineering.md
```

---

## Next Steps

- Learn goal management: [Daily Routine](daily-routine.md)
- See all skills: [All Skills](../reference/skills-index.md)

---

## LeanOS Pro

Need domain-specific thread execution? **LeanOS Pro** includes:
- Sales threads with typed actions (lead-intake, qualify, demo, pilot, close)
- Marketing threads with typed actions (create, publish, promote, measure)
- Engineering threads with typed actions (architecture, backend, frontend, validate)
- Domain agents for orchestrated execution

[Learn more about LeanOS Pro](https://bellabe.gumroad.com/l/leanos-pro)
