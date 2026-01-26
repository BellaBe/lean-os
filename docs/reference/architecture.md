# System Architecture

LeanOS Core operates in layers: Goals → Strategy → Reasoning → Skills → Threads → State.

## Operating Model

**Goal-driven (primary):** All work flows from declared objectives
```
Goal → Plan → Threads → Learning → Canvas
```

**Reactive (fallback):** Handles unexpected signals, links back to goals
```
Signal → Thread → Link to Goal (or create new goal)
```

## Architecture Diagram

```text
┌──────────────────────────────────────────────────────────────────────────────────────────────┐
│ GOALS LAYER (Primary Operating Mode)                                                         │
│ Declared objectives that drive all work                                                      │
│ Location: strategy/goals/                                                                    │
│                                                                                              │
│ ├─ active/: Current objectives with plans                                                    │
│ ├─ completed/: Achieved goals (archive)                                                      │
│ └─ abandoned/: Dropped goals (archive)                                                       │
│                                                                                              │
│ Skills: goal-setter (creates goals), goal-tracker (derives state)                            │
│ Autonomy: auto | ask | hybrid (configurable per goal)                                        │
└──────────────────────────────────────────────────────────────────────────────────────────────┘
                                          ↓
┌──────────────────────────────────────────────────────────────────────────────────────────────┐
│ STRATEGY LAYER                                                                               │
│ Source of Truth: Lean Canvas (15 living documents)                                           │
│ Location: strategy/canvas/                                                                   │
│                                                                                              │
│ Goals READ Canvas for context (assumptions, constraints, segments)                           │
│ Learning WRITES to Canvas (feedback loop from completed threads)                             │
└──────────────────────────────────────────────────────────────────────────────────────────────┘
                                          ↓
┌──────────────────────────────────────────────────────────────────────────────────────────────┐
│ COGNITIVE LAYER                                                                              │
│ Agent: .claude/agents/problem-solver.md                                                      │
│ Skills: thinking-modes, shaping-schemas                                                      │
│                                                                                              │
│ THINKING MODES (6 reasoning approaches):                                                     │
│ ┌─────────────────────────────────────────────────────────────────────────────────────────┐  │
│ │ CAUSAL            │ Operational execution, known processes → 6-stage thread flow       │  │
│ │ ABDUCTIVE         │ Anomaly diagnosis → "Why did X happen?"                            │  │
│ │ INDUCTIVE         │ Pattern detection → "This keeps happening"                         │  │
│ │ ANALOGICAL        │ Novel situations → "This is like..."                               │  │
│ │ DIALECTICAL       │ Stakeholder conflicts → Trade-off resolution                       │  │
│ │ COUNTERFACTUAL    │ Decision evaluation → "What if we had..."                          │  │
│ └─────────────────────────────────────────────────────────────────────────────────────────┘  │
│                                                                                              │
│ SHAPING SCHEMAS (11 output structures):                                                      │
│ ┌─────────────────────────────────────────────────────────────────────────────────────────┐  │
│ │ procedural │ validation │ planning │ decision │ evaluative │ diagnostic                │  │
│ │ risk │ constraint │ alignment │ prescriptive │ descriptive                             │  │
│ └─────────────────────────────────────────────────────────────────────────────────────────┘  │
└──────────────────────────────────────────────────────────────────────────────────────────────┘
                                          ↓
┌──────────────────────────────────────────────────────────────────────────────────────────────┐
│ SKILLS LAYER (Domain Execution)                                                              │
│ Location: .claude/skills/                                                                    │
│                                                                                              │
│ AGENTS (Orchestrators - 2):                                                                  │
│ ┌─────────────────────────────────────────────────────────────────────────────────────────┐  │
│ │ foundations-research │ Startup discovery (market, segments, problems, competition)     │  │
│ │ problem-solver       │ Orchestrates thinking-modes + shaping-schemas                   │  │
│ └─────────────────────────────────────────────────────────────────────────────────────────┘  │
│                                                                                              │
│ SKILLS (14 total):                                                                           │
│ ┌─────────────────────────────────────────────────────────────────────────────────────────┐  │
│ │ foundations-* │ Startup discovery skills (6)                                           │  │
│ │ cognitive-*   │ Thinking modes + output schemas (2)                                    │  │
│ │ goal-*        │ Goal setting and tracking (2)                                          │  │
│ │ system-*      │ Agent/skill creation, indexing, behavioral science (4)                 │  │
│ └─────────────────────────────────────────────────────────────────────────────────────────┘  │
└──────────────────────────────────────────────────────────────────────────────────────────────┘
                                          ↓
┌──────────────────────────────────────────────────────────────────────────────────────────────┐
│ THREADS LAYER (Decision Storage)                                                             │
│ Complete decision narratives with 6-stage causal flow                                        │
│ Location: threads/{type}/{thread-name}/                                                      │
│                                                                                              │
│ Thread structure:                                                                            │
│ ├─ 1-input.md                                                                               │
│ ├─ 2-hypothesis.md                                                                          │
│ ├─ 3-implication.md                                                                         │
│ ├─ 4-decision.md                                                                            │
│ ├─ 5-actions.md                                                                             │
│ └─ 6-learning.md                                                                            │
└──────────────────────────────────────────────────────────────────────────────────────────────┘
                                          ↓
┌──────────────────────────────────────────────────────────────────────────────────────────────┐
│ STATE LAYER (Derived, On-Demand)                                                             │
│ State is computed from goals + threads, not stored separately                                │
│                                                                                              │
│ Goal state: Derived by goal-tracker from linked threads                                      │
│ Snapshot: Computed on-demand (no daily file needed)                                          │
└──────────────────────────────────────────────────────────────────────────────────────────────┘
```

---

## Layer 1: Goals

**Location:** `strategy/goals/`

**Purpose:** Declared objectives that drive all work

**Structure:**
```
strategy/goals/
├── active/           # Current objectives
│   └── g-{name}.md   # Goal file with plan + state
├── completed/        # Achieved goals (archive)
└── abandoned/        # Dropped goals (archive)
```

**Goal file schema:**
```markdown
---
id: g-{kebab-case-name}
status: active
autonomy: auto | ask | hybrid
deadline: YYYY-MM-DD
---

# {Goal Title}

## Objective
{What you want to achieve}

## Success Criteria
- [ ] {Measurable criterion}

## Plan
### Subgoals
- SG1: {subgoal} → threads: {linked threads}

## State (derived by goal-tracker)
| Metric | Current | Target | Gap |
```

**Skills:**
- `goal-setter`: Creates goals from objectives, reads Canvas for context
- `goal-tracker`: Derives state from threads, computes gaps/trajectory

---

## Layer 2: Strategy

**Location:** `strategy/canvas/`

**Contents:** 15 living Lean Canvas documents

**Key files:**
- 00.mode.md - Business model mode (VENTURE/BOOTSTRAP)
- 01-04 - Context, constraints, opportunity, segments
- 05-09 - Problem, competitive, UVP, unfair advantage, solution
- 10-15 - Assumptions, channels, revenue, metrics, costs, GTM

**Updates:** Automatically updated by Stage 6 (Learning) in threads

---

## Layer 3: Cognitive

**Agent:** `.claude/agents/problem-solver.md`
**Skills:** `thinking-modes`, `shaping-schemas`

**Purpose:** Route tasks to appropriate reasoning mode and output schema

### Thinking Modes (6)

| Mode | Use When | Output |
|------|----------|--------|
| **Causal** | Operational execution (enforced for threads) | 6-stage thread |
| **Abductive** | Anomaly diagnosis | Root cause hypothesis |
| **Inductive** | Pattern detection | Validated pattern |
| **Analogical** | Novel situation | Adapted playbook |
| **Dialectical** | Stakeholder conflict | Synthesis decision |
| **Counterfactual** | Decision evaluation | Learning + recommendation |

### Shaping Schemas (11)

| Schema | Use When |
|--------|----------|
| **procedural** | Runbook, SOP, checklist |
| **validation** | Success criteria, test plan |
| **planning** | Roadmap, phases, timeline |
| **decision** | Choose, prioritize, go/no-go |
| **evaluative** | Review, assess, audit |
| **diagnostic** | Root cause, why did X happen |
| **risk** | Threats, what could go wrong |
| **constraint** | Requirements, must/must not |
| **alignment** | Stakeholder conflict, ownership |
| **prescriptive** | Recommendations, next steps |
| **descriptive** | Summarize, explain (default) |

---

## Layer 4: Skills

**Agents:** `.claude/agents/`
**Skills:** `.claude/skills/`

### Agents (2)

| Agent | Purpose | Skills Loaded |
|-------|---------|---------------|
| `foundations-research` | Startup discovery phase | market-sizing, customer-segmenting, problem-validating |
| `problem-solver` | Reasoning + output shaping | thinking-modes, shaping-schemas |

### Skills (14)

| Category | Skills | Purpose |
|----------|--------|---------|
| **Foundations** (6) | market-sizing, customer-segmenting, problem-validating, competitive-analyzing, value-positioning, solution-designing | Startup discovery |
| **Cognitive** (2) | thinking-modes, shaping-schemas | Reasoning + output structure |
| **Goals** (2) | goal-setter, goal-tracker | Goal management |
| **System** (4) | agent-creating, skill-creating, directory-indexing, behavioral-science | Meta-skills |

---

## Layer 5: Threads

**Location:** `threads/{type}/{name}/`

**Purpose:** Store complete decision narratives with 6-stage causal flow

**Thread structure:**
```
threads/{type}/{name}/
├── meta.json
├── 1-input.md
├── 2-hypothesis.md
├── 3-implication.md
├── 4-decision.md
├── 5-actions.md
└── 6-learning.md
```

---

## Layer 6: State

**Purpose:** State is computed, not stored. Goals track their own state.

**State derivation:**
```
goal-tracker reads:
  - Goal files (objectives, success criteria)
  - Linked threads (execution state)
  ↓
Computes:
  - Current metrics vs targets
  - Gap analysis
  - Recommendations
```

---

## Data Flow

**Goal-driven flow:**
```
User declares objective
    ↓
goal-setter (reads Canvas for context)
    ↓
Goal created with plan
    ↓
Subgoals spawn threads
    ↓
Threads execute (6-stage causal flow)
    ↓
Learning → Canvas updated
    ↓
goal-tracker derives state
    ↓
Gap detected → New threads or recommendations
```

---

## Next Steps

- See all skills: [Agents & Skills Index](agents-skills-index.md)
- Understand system overview: [What is LeanOS](what-is-leanos.md)

---

## LeanOS Pro

Need sales, marketing, product, engineering, and full business operations?

**LeanOS Pro** — A swiss knife for building and operating a business:
- 181 skills (all domains)
- 44 agents (full orchestration)
- Sales, marketing, product, engineering, customer success, RevOps
- One person operates with 5-10x effectiveness

[Learn more about LeanOS Pro](https://bellabe.gumroad.com/l/leanos-pro)
