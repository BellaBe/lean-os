# System Workflow

How to use the goal lifecycle skills to define, decompose, activate, track, and execute goals.

---

## Overview

```
+---------------------------------------------------------------+
|                    SYSTEM SKILLS                                |
|                    6 skills                                     |
+---------------------------------------------------------------+
|                                                                 |
|  GOAL LIFECYCLE                                                 |
|  +----------------------------------------------------------+  |
|  | sys-defining-goals      Define ONE measurable goal        |  |
|  | sys-decomposing-goals   Break into subgoal hierarchies    |  |
|  | sys-activating-goals    Create execution thread           |  |
|  | sys-tracking-goals      Monitor progress, generate alerts |  |
|  | sys-executing-threads   Write agent outputs to stages     |  |
|  +----------------------------------------------------------+  |
|                                                                 |
|  UTILITY                                                        |
|  +----------------------------------------------------------+  |
|  | sys-indexing-directories  Generate index.md navigation    |  |
|  +----------------------------------------------------------+  |
|                                                                 |
+---------------------------------------------------------------+
```

---

## Goal System Architecture

```
User Input (Canvas / Natural Language / Hybrid)
        |
        v
+-------------------------------------+
| sys-defining-goals                   |  Define ONE goal
| Input --> Derive --> Write           |  --> strategy/goals/active/{id}.md
+-------------------------------------+
        |
        v (optional)
+-------------------------------------+
| sys-decomposing-goals                |  Break into subgoals
| Parent --> Formulas --> Children     |  --> multiple linked goal files
+-------------------------------------+
        |
        v
+-------------------------------------+
| sys-activating-goals                 |  Create execution thread
| Goal --> Thread --> Route            |  --> threads/{domain}/{name}/
+-------------------------------------+
        |
        v
+-------------------------------------+
| sys-executing-threads                |  Write outputs to stages
| Agent output --> Stage files         |  --> 2-hypothesis through 6-learning
+-------------------------------------+
        |
        v
+-------------------------------------+
| sys-tracking-goals                   |  Monitor and alert
| Goals --> Gaps --> Alerts            |  --> artifacts/system/alerts/
+-------------------------------------+
```

---

## Workflow: Define a Goal

**When:** Setting a new objective.

**Skill:** `sys-defining-goals`

```
1. CLASSIFY INPUT
   +-- Canvas: 00.mode.md, 13.metrics.md present
   +-- Natural Language: "I want to..."
   +-- Hybrid: Partial canvas + verbal context

2. EXTRACT INTENT
   +-- Category: revenue | activity | content | efficiency | retention
   +-- Metric: arr, customers, meetings, posts, etc.
   +-- Direction: maximize | minimize

3. CHECK CANVAS DEPENDENCIES
   +-- Required (blocking): 00.mode.md
   +-- Recommended (use defaults if missing): pricing, metrics

4. DERIVE TARGET (using formulas)

5. CALCULATE MILESTONES
   +-- Linear: even distribution
   +-- Front-loaded: 60/40
   +-- Back-loaded: 40/60

6. WRITE GOAL FILE
   --> strategy/goals/active/{goal_id}.md
```

---

## Workflow: Decompose a Goal

**When:** Breaking a high-level goal into actionable subgoals.

**Skill:** `sys-decomposing-goals`

```
1. READ PARENT GOAL

2. DETERMINE HIERARCHY LEVEL
   +-- Business Goal (annual) --> System Goals (quarterly)
   +-- System Goal (quarterly) --> Operational Goals (monthly)
   +-- Operational Goal (monthly) --> Tactical Goals (weekly)

3. APPLY DECOMPOSITION PATTERN
   Revenue cascade:
   Revenue Target
   +-- Pipeline = Revenue / Win Rate
   |   +-- Opportunities = Pipeline / Avg Deal
   |       +-- Meetings = Opps / Opp Rate
   +-- Expansion = Existing ARR x Expansion Rate
   +-- Retention = 100% - Churn Rate

4. ALLOCATE CONSTRAINTS proportionally

5. CREATE SUBGOAL FILES
   --> strategy/goals/active/{parent_id}_sub_{metric}.md

6. UPDATE PARENT with child_goals list

7. VALIDATE: children derive parent, periods align, constraints fit
```

---

## Workflow: Activate a Goal

**When:** Ready to begin execution.

**Skill:** `sys-activating-goals`

```
1. READ GOAL FILE

2. DETERMINE THREAD NAME
   --> {goal-metric}_{period-short}

3. CREATE THREAD DIRECTORY
   --> threads/{domain}/{thread-name}/

4. WRITE CAUSAL FLOW FILES
   1-input.md (populated with goal context)
   2-hypothesis.md (template)
   3-implication.md (template)
   4-decision.md (template)
   5-actions.md (template)
   6-learning.md (template)

5. UPDATE GOAL FILE
   --> thread: threads/{domain}/{name}
   --> status: activated

6. RETURN activation context
```

---

## Workflow: Execute Thread Stages

**When:** Agent has produced outputs and needs to write them to thread files.

**Skill:** `sys-executing-threads`

```
1. VALIDATE thread exists (1-input.md present)

2. DETERMINE stages to write from agent type

3. WRITE stage files with frontmatter:
   - status: completed
   - completed_by: {agent_name}
   - completed_at: {date}

4. VERIFY all mapped stages written
```

---

## Workflow: Track Goals

**When:** Monitoring progress of active goals.

**Skill:** `sys-tracking-goals`

```
1. SCAN ACTIVE GOALS
   --> strategy/goals/active/*.md

2. FOR EACH GOAL:
   a. CALCULATE GAPS
      Absolute: target - current
      Relative: gap / target
      Trajectory: current + (velocity x days_remaining) - target

   b. SCORE URGENCY
      - critical: gap > 50% AND days < 7
      - high: gap > 30% AND days < 14
      - medium: on pace but tight
      - low: on track

   c. ASSESS ACHIEVABILITY
      Historical (40%) + Resources (30%) + Trajectory (20%) + External (10%)

3. GENERATE ALERTS
   --> artifacts/system/alerts/{alert-id}.md

4. UPDATE DASHBOARD
   --> artifacts/system/goal-dashboard.md
```

---

## Workflow: Index Directories

**When:** Need navigation index for documentation.

**Skill:** `sys-indexing-directories`

```
1. SCAN directory for .md files
2. EXTRACT title and description from each
3. GENERATE index.md with links
4. WRITE to {directory}/index.md
```

---

## Planning Cycle

**When:** Starting a new quarter or project.

```
Phase 1: Canvas (Foundations)
  fnd-architect --> fnd-researcher
  --> strategy/canvas/ populated
        |
        v
Phase 2: Goal Definition
  INVOKE sys-defining-goals
  --> strategy/goals/active/{id}.md
        |
        v
Phase 3: Goal Decomposition (optional)
  INVOKE sys-decomposing-goals
  --> subgoal hierarchy
        |
        v
Phase 4: Activation
  INVOKE sys-activating-goals
  --> threads/{domain}/{name}/
        |
        v
Phase 5: Execution
  Work within threads, causal flow
  INVOKE sys-executing-threads to write outputs
        |
        v
Phase 6: Tracking
  sys-tracking-goals (continuous)
  --> monitor, alert, adjust
        |
        v
Phase 7: Learning
  Fill 6-learning.md
  --> feed next planning cycle
```

---

## Error Handling

| Error | Action |
|-------|--------|
| Missing required canvas | Block, request canvas completion |
| Goal already activated | Return existing thread |
| Child targets exceed parent | Reject, show constraint |
| No current metrics for tracking | Alert, request update |

---

## Artifact Structure

```
strategy/
+-- canvas/          # Business canvas (populated by fnd-architect + fnd-researcher)
+-- goals/
    +-- active/      # Live goals
    +-- achieved/    # Completed goals
    +-- index.md

threads/
+-- {domain}/        # Created by sys-activating-goals
    +-- {name}/
        +-- 1-input.md through 6-learning.md

artifacts/
+-- system/
    +-- alerts/      # Generated by sys-tracking-goals
    +-- goal-dashboard.md
```
