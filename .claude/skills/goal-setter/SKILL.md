---
name: goal-setter
description: Transform objectives into structured goals with plans. Use when user declares intent ("I want to...", "Goal is to...", "Achieve X by Y"). Decomposes into subgoals, milestones, success criteria.
---

# Goal Setter

Transform vague or precise objectives into structured, actionable goals.

## Operating Model

Goals are the **primary** operating mode for LeanOS. All work should be goal-driven.

```
PROACTIVE (primary):  Goal → Plan → Threads → Artifacts → Learning → Canvas
REACTIVE (fallback):  Signal → Thread → Link to Goal (or create new goal)
```

**Goal-setter reads:**
- Canvas (strategic context, assumptions, constraints)
- Existing goals (avoid conflicts, find linkages)

**Goal-setter does NOT read:**
- Threads (execution output, not input)
- Artifacts (deliverables, not context)

## Type Signature

```
GoalSetter : Objective × CanvasContext × ExistingGoals → Goal

Where:
  Objective     : string (user's stated intent)
  CanvasContext : strategy/canvas/* (beliefs, constraints, segments)
  ExistingGoals : strategy/goals/active/* (avoid conflicts)
  Goal          : Objective × SuccessCriteria × Plan × Autonomy × State
  Plan          : [Subgoal] × [Milestone] × [Dependency]
  Subgoal       : Objective × SuccessCriterion × ThreadType
```

## When to Use

- User expresses intent: "I want to...", "Goal is to...", "Need to achieve..."
- Starting a new initiative without clear structure
- Breaking down a large objective into actionable pieces
- Reviewing/refining existing goals

## Process

### 1. Capture Objective

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

### 2. Determine Goal Type

Infer from context or ask:

| Type | Signals | Example |
|------|---------|---------|
| `business` | Revenue, customers, growth, market | "Reach $50K MRR" |
| `brand` | Followers, reach, authority, audience | "Build LinkedIn presence" |
| `product` | Features, launches, technical milestones | "Ship v2.0" |
| `learning` | Skills, certifications, knowledge | "Learn Rust" |
| `custom` | Anything else | User-defined |

### 3. Define Success Criteria

Transform objective into measurable criteria:

**Good criteria:**
- Specific number or state
- Independently verifiable
- Time-bound (inherits from goal deadline)

**Examples:**
```
Objective: "Grow revenue"
Criteria:
- [ ] MRR >= $50,000
- [ ] Customer count >= 10
- [ ] Net revenue retention >= 100%

Objective: "Build LinkedIn presence"
Criteria:
- [ ] Followers >= 10,000
- [ ] Average post impressions >= 5,000
- [ ] 2+ inbound leads/month from content
```

### 4. Decompose into Plan

**Subgoals** - intermediate objectives that lead to main goal:
- Each subgoal has its own success criterion
- Identify dependencies between subgoals
- Link to thread types (business, sales, marketing, engineering)

**Milestones** - checkpoints with dates:
- Evenly distributed toward deadline
- Each milestone = measurable progress marker

**Decomposition reasoning:**
```
Goal: Achieve X by deadline D
  ↓
Ask: What must be true for X to happen?
  ↓
Identify 3-5 necessary conditions (subgoals)
  ↓
For each subgoal: What threads/actions achieve this?
  ↓
Order by dependencies
  ↓
Set milestones at 25%, 50%, 75%, 100% progress points
```

### 5. Set Autonomy Level

| Mode | When to Use | Behavior |
|------|-------------|----------|
| `auto` | Low-risk, well-understood domain | AI creates threads and executes without asking |
| `ask` | High-risk, novel, or user preference | AI recommends, waits for approval |
| `hybrid` | Default | Auto for impact <0.5, ask for impact ≥0.5 |

**Default: `hybrid`** unless user specifies otherwise.

### 6. Initialize State

Create initial state section:
- All metrics start at current values (0 or baseline)
- Gap = target - current
- Trend = "→" (neutral, no data yet)
- Trajectory = "Unknown" (insufficient data)

## Output

Create file: `strategy/goals/active/{goal-id}.md`

### Goal File Schema

```markdown
---
id: g-{kebab-case-short-name}
type: business | brand | product | learning | custom
status: active
autonomy: auto | ask | hybrid
created: {YYYY-MM-DD}
deadline: {YYYY-MM-DD}
canvas_refs: ["{section}.md", ...]  # Optional Canvas links
---

# {Goal Title}

## Objective
{Single sentence describing desired outcome}

## Success Criteria
- [ ] {Measurable criterion 1}
- [ ] {Measurable criterion 2}
- [ ] {Measurable criterion 3}

## Plan

### Subgoals

#### SG1: {Subgoal Title}
- **Success:** {Specific criterion}
- **Depends on:** {None | SG#}
- **Thread type:** {business | sales | marketing | engineering}
- **Threads:** {None yet | thread-id, ...}
- **Status:** pending | in_progress | completed

#### SG2: {Subgoal Title}
- **Success:** {Specific criterion}
- **Depends on:** SG1
- **Thread type:** {type}
- **Threads:** {None yet}
- **Status:** pending

### Milestones
- [ ] M1: {25% progress marker} (by {date})
- [ ] M2: {50% progress marker} (by {date})
- [ ] M3: {75% progress marker} (by {date})
- [ ] M4: {Goal achieved} (by {deadline})

### Dependencies
{External dependencies, blockers, or prerequisites}

## State

### Metrics
| Metric | Current | Target | Gap | Trend |
|--------|---------|--------|-----|-------|
| {Primary metric} | {value} | {value} | {value} | → |
| {Secondary metric} | {value} | {value} | {value} | → |

### Execution
- **Active threads:** 0
- **Completed threads:** 0
- **Blocked:** 0

### Trajectory
- **On track:** Unknown (insufficient data)
- **Projected completion:** TBD
- **Risk level:** Low

## Log
- {created date}: Goal created
```

## Integration

### With Canvas
- Reference relevant Canvas sections in `canvas_refs`
- Subgoals may validate Canvas assumptions
- Goal completion can trigger Canvas updates

### With Threads
- Subgoals spawn threads when activated
- Thread completion updates subgoal status
- Thread Stage 6 (Learning) feeds back to goal state

### With Reasoning Gateway
- Complex decomposition may route through reasoning modes
- Causal: For operational goals with clear cause-effect
- Analogical: For novel goals ("this is like...")
- Dialectical: For goals with competing priorities

## Examples

### Business Goal
```
User: "I want to hit $50K MRR by end of Q2"

Goal created:
- id: g-mrr-50k
- type: business
- deadline: 2025-06-30
- Success criteria: MRR >= $50K, Customers >= 10, Churn < 5%
- Subgoals:
  - SG1: Build pipeline (20 qualified leads)
  - SG2: Improve close rate (≥30%)
  - SG3: Reduce churn (<5%)
```

### Brand Goal
```
User: "Build my LinkedIn presence for thought leadership"

Goal created:
- id: g-linkedin-authority
- type: brand
- deadline: 2025-06-30 (asked user)
- Success criteria: 10K followers, 5K avg impressions, 2 leads/month
- Subgoals:
  - SG1: Define content pillars
  - SG2: Establish posting cadence (3x/week)
  - SG3: Build engagement network
```

### Product Goal
```
User: "Ship the mobile app"

Goal created:
- id: g-mobile-app-launch
- type: product
- deadline: 2025-03-31 (asked user)
- Success criteria: App in stores, 100 beta users, <1% crash rate
- Subgoals:
  - SG1: Core features complete
  - SG2: Beta testing
  - SG3: Store submission
```

## Constraints

### Must Have
- Clear success criteria (measurable)
- Deadline
- At least 2 subgoals
- Autonomy level set

### Must Ask If Missing
- Deadline not specified
- Success criteria ambiguous
- Type unclear from context

### Must NOT
- Create goals without user confirmation of structure
- Set autonomy to `auto` for high-impact goals without asking
- Create duplicate goals (check existing first)

## Error Handling

**Objective too vague:**
```
Ask: "What does '{objective}' look like when achieved?
     Give me 2-3 specific outcomes I can measure."
```

**No deadline:**
```
Ask: "By when do you want to achieve this?
     Options: specific date, relative (3 months), or milestone-based"
```

**Conflicting with existing goal:**
```
Flag: "This overlaps with existing goal '{goal-id}'.
      Should I: (1) Merge as subgoal, (2) Replace existing, (3) Keep both?"
```
