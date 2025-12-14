# Goal-Driven Operations
**Workflow Specification (Authoritative)**

**Status:** Active
**Version:** 3.0
**Applies to:** Human operators and AI agents
**Skills:** `.claude/skills/goal-setter/SKILL.md`, `.claude/skills/goal-tracker/SKILL.md`

---

## Purpose

LeanOS operates through **goals, not daily dashboards**. This document defines the complete goal lifecycle:

1. **Setting goals** - Transform objectives into structured plans
2. **Tracking goals** - Derive state from execution, identify gaps
3. **Daily interaction** - Human touchpoints (<30 min/day)

---

## Position in the System

```
User Intent ("I want to...", "Goal is to...")
└── goal-setter ← CREATES GOALS
    └── strategy/goals/active/{goal-id}.md
        └── Subgoals → Threads (6-stage execution)
            └── Stage 6: Learning
                └── goal-tracker ← DERIVES STATE
                    ├── Updates goal state
                    ├── Identifies gaps
                    └── Triggers actions (respects autonomy)
```

### Key Distinctions

- **goal-setter** → creates and structures goals
- **goal-tracker** → derives state, tracks progress, triggers actions
- **Threads** → execute subgoals via 6-stage causal flow
- **Human** → approves high-impact decisions, sets direction

---

## Operating Model

```
PROACTIVE (primary):  Goal → Plan → Threads → Artifacts → Learning → Canvas
                                        ↑
                      goal-tracker derives state from execution

REACTIVE (fallback):  Signal → Thread → Link to Goal (or create new goal)
```

All execution links back to goals.

---

# Part 1: Goal Setting

## When to Use goal-setter

- User expresses intent: "I want to...", "Goal is to...", "Need to achieve..."
- Starting a new initiative without clear structure
- Breaking down a large objective into actionable pieces

## Goal Setting Process (7 Steps)

### Step 1: Capture Objective

Extract from user input:
- **What**: The desired outcome
- **Why**: Motivation/context (optional but valuable)
- **When**: Deadline or timeline (required)
- **Constraints**: Budget, resources, dependencies

**If vague, ask:**
```
What does success look like specifically?
By when do you need this achieved?
What resources/constraints should I know about?
```

### Step 2: Determine Goal Type

| Type | Signals | Example |
|------|---------|---------|
| `business` | Revenue, customers, growth, market | "Reach $50K MRR" |
| `brand` | Followers, reach, authority, audience | "Build LinkedIn presence" |
| `product` | Features, launches, technical milestones | "Ship v2.0" |
| `learning` | Skills, certifications, knowledge | "Learn Rust" |
| `custom` | Anything else | User-defined |

### Step 3: Apply Business Model Mode

For `business` goals, read `strategy/canvas/00-business-model-mode.md`:

| Aspect | VENTURE | BOOTSTRAP |
|--------|---------|-----------|
| **Primary metrics** | ARR, MAU, market share | MRR, profit, cash flow |
| **Success focus** | Growth rate, scale | Profitability, sustainability |
| **Decomposition** | Acquire → Activate → Monetize | Revenue → Margin → Scale |
| **Risk tolerance** | Higher (burn for growth) | Lower (preserve cash) |
| **Autonomy default** | `hybrid` | `ask` |

### Step 4: Define Success Criteria

Transform objective into measurable criteria:

```
Objective: "Grow revenue"
Criteria:
- [ ] MRR >= $50,000
- [ ] Customer count >= 10
- [ ] Net revenue retention >= 100%
```

**Good criteria:** Specific, verifiable, time-bound.

### Step 5: Decompose into Plan

**Subgoals** - intermediate objectives:
- Each has own success criterion
- Dependencies between subgoals
- Linked to thread types

**Milestones** - checkpoints at 25%, 50%, 75%, 100%

**Logic:**
```
Goal: Achieve X by deadline D
  ↓
What must be true for X to happen?
  ↓
Identify 3-5 necessary conditions (subgoals)
  ↓
Order by dependencies
  ↓
Set milestones
```

### Step 6: Set Autonomy Level

| Mode | Behavior |
|------|----------|
| `auto` | AI executes without asking |
| `ask` | AI recommends, waits for approval |
| `hybrid` | Auto for impact <0.5, ask for >=0.5 |

**Default:** `hybrid`

### Step 7: Initialize State

- Metrics at baseline (0 or current)
- Gap = target - current
- Trend = "→" (neutral)
- Trajectory = "Unknown"

## Goal File Output

Location: `strategy/goals/active/{goal-id}.md`

```markdown
---
id: g-{kebab-case-name}
type: business | brand | product | learning | custom
mode: VENTURE | BOOTSTRAP
status: active
autonomy: auto | ask | hybrid
created: {YYYY-MM-DD}
deadline: {YYYY-MM-DD}
canvas_refs: ["{section}.md", ...]
---

# {Goal Title}

## Objective
{Single sentence describing desired outcome}

## Success Criteria
- [ ] {Measurable criterion 1}
- [ ] {Measurable criterion 2}

## Plan

### Subgoals

#### SG1: {Subgoal Title}
- **Success:** {Specific criterion}
- **Depends on:** {None | SG#}
- **Thread type:** {business | sales | marketing | engineering}
- **Threads:** {None yet | thread-id, ...}
- **Status:** pending | in_progress | completed

### Milestones
- [ ] M1: {25% marker} (by {date})
- [ ] M2: {50% marker} (by {date})
- [ ] M3: {75% marker} (by {date})
- [ ] M4: {Goal achieved} (by {deadline})

## State

### Metrics
| Metric | Current | Target | Gap | Trend |
|--------|---------|--------|-----|-------|
| {metric} | {value} | {value} | {value} | → |

### Execution
- **Active threads:** 0
- **Completed threads:** 0
- **Blocked:** 0

### Trajectory
- **On track:** Unknown
- **Projected completion:** TBD
- **Risk level:** Low

## Canvas Links

**Validates assumptions:**
- {id}: "{assumption}" (10-assumptions.md)

## Log
- {date}: Goal created
```

## Canvas Integration

| Goal Type | Required Reading | Link To |
|-----------|------------------|---------|
| business | 00-mode, 11-pricing, 12-costs, 13-metrics | 10-assumptions |
| brand | 01-context, 07-uvp, 04-segments | 10-assumptions |
| product | 09-solution, 05-problem, 02-constraints | 10-assumptions |
| learning | 01-context | 10-assumptions |

---

# Part 2: Goal Tracking

## When to Use goal-tracker

- Daily/periodic goal review
- After thread completion
- User asks "How am I doing on {goal}?"
- Proactive gap detection

## Core Operations

### 1. State Derivation

State is **computed**, not manually tracked:

```
For goal G:
  1. Find linked threads (G.Plan.Subgoals[*].Threads)
  2. Aggregate: active, completed, blocked counts
  3. Extract metrics from Stage 6 (Learning)
  4. Calculate: current, gap, trend for each criterion
```

### 2. Subgoal Status Update

```
If SG.Threads empty → pending
If any thread active → in_progress
If all threads completed AND success met → completed
If any thread blocked → blocked
```

### 3. Trajectory Projection

```
progress_rate = (current - initial) / elapsed_time
projected_final = current + (progress_rate × remaining_time)
on_track = projected_final >= target

Risk:
  Low = on_track AND >30 days remaining
  Medium = on_track AND <=30 days
  High = NOT on_track
  Critical = NOT on_track AND <=14 days
```

### 4. Gap Analysis

```
gap_percent = (target - current) / target × 100

Flag if:
  - gap_percent > 50% ("Significant gap")
  - trend == "↓" AND gap_percent > 20% ("Declining metric")
```

### 5. Action Generation

Based on gaps and autonomy:

| Gap Type | Recommended Action |
|----------|-------------------|
| Pipeline gap | Outbound campaign thread |
| Conversion gap | Optimization thread |
| Content gap | Content thread |
| Technical gap | Engineering thread |

**Autonomy behavior:**
- `auto`: Create thread directly
- `ask`: Present recommendation with options
- `hybrid`: Auto if impact <0.5, ask if >=0.5

## Tracker Workflows

### On-Demand Snapshot

```
Trigger: "What's the status of my goals?"

1. Load all active goals
2. Derive current state for each
3. Check trajectories
4. Identify gaps and risks
5. Generate snapshot report
6. Execute auto actions if allowed
```

**No daily file generated.** Snapshot computed on-demand.

### Thread Completion

```
Trigger: Thread reaches Stage 6

1. Find linked goal
2. Update subgoal status
3. Extract metrics from learning
4. Update goal state
5. If all criteria met → complete goal
```

### Goal Completion

```
Trigger: All success criteria met

1. Mark status: completed
2. Move to strategy/goals/completed/
3. Update Canvas assumptions
4. Identify follow-on goals
```

---

# Part 3: Daily Interaction

Human touchpoint: **<30 min/day** on operations.

## Morning Review (5 minutes)

### Check Active Goals

```
Ask: "What's the status of my goals?"
Skill: goal-tracker
```

**Snapshot shows:**
- Goal progress (metrics vs targets)
- Gaps identified
- Recommended actions
- Threads needing attention

**Example output:**
```markdown
# Goal Snapshot - 2025-12-10

## g-mrr-50k: Reach $50K MRR by Q2
**Progress:** 48% ($24K / $50K)
**Trajectory:** On track
**Risk:** Low

### Gaps
- Pipeline needs 8 more qualified leads

### Recommended Actions
1. Create outbound campaign thread (auto-approved)
2. Review stalled deal: Acme Corp (needs attention)

## g-linkedin-authority: Build LinkedIn Presence
**Progress:** 62% (6.2K / 10K followers)
**Trajectory:** Ahead of schedule
**Risk:** Low
```

## Human Actions (3-5 minutes)

1. **Review recommendations** (1 min) - Approve/defer suggested actions
2. **Check flagged items** (1-2 min) - High-impact decisions (>=0.8 score)
3. **Unblock threads** (1 min) - Resolve any blocked items

## AI Handles Autonomously

Based on goal autonomy settings:

**Auto mode:**
- Thread creation for gap-closing
- Content generation
- Prospect research
- Low-impact decisions (<0.8)

**Ask mode:**
- High-impact decisions (>=0.8)
- Canvas-altering changes
- Budget commitments
- Strategic pivots

## Weekly Review (30 min)

### Goal Trajectory Review

```
Ask: "Review all goal trajectories"
```

**Review:**
- On-track vs off-track goals
- Completed subgoals this week
- Upcoming milestones
- Gaps requiring new threads

### Adjust Priorities

- Reprioritize goals if needed
- Adjust autonomy levels
- Close or abandon stalled goals
- Create new goals for emerging needs

---

## Interaction Patterns

| Intent | Command | Skill |
|--------|---------|-------|
| Check goal status | "How is g-mrr-50k progressing?" | goal-tracker |
| Check all goals | "What's the status of my goals?" | goal-tracker |
| Create new goal | "I want to launch mobile app by March" | goal-setter |
| Review gaps | "What gaps need attention?" | goal-tracker |
| Approve action | "Approve the outbound campaign" | (direct) |

---

## Error Handling

### goal-setter errors

| Error | Response |
|-------|----------|
| Objective too vague | Ask for 2-3 specific measurable outcomes |
| No deadline | Ask for date, relative time, or milestone |
| Conflicts with existing | Offer: merge, replace, or keep both |

### goal-tracker errors

| Error | Response |
|-------|----------|
| No linked threads | Warn, recommend creating threads for SG1 |
| Stale goal (>14 days) | Offer: review, pause, or abandon |
| Deadline passed | Offer: extend, mark complete, or abandon |

---

## Constraints

### goal-setter

- Must have: success criteria, deadline, 2+ subgoals, autonomy level
- Must NOT: create without confirmation, auto for high-impact, create duplicates

### goal-tracker

- Must NOT: modify goal structure, create threads without autonomy check, mark complete without verification
- State derivation: on-demand or daily
- Trajectory calculation: weekly minimum

---

## Key Principle

**Goals are your interface. Not dashboards, not daily files.**

- Goals track their own state
- Threads execute goal subgoals
- Snapshots are computed on-demand
- Canvas updates flow from goal completion

---

## References

- **Skills:** `.claude/skills/goal-setter/`, `.claude/skills/goal-tracker/`
- **Goal Storage:** `strategy/goals/active/`, `strategy/goals/completed/`
- **Canvas:** `strategy/canvas/`
- **Execution:** [Causal Flow](causal-flow.md)
- **All Skills:** [All Skills](../reference/all-skills.md)
