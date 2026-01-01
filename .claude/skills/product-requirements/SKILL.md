---
name: product-requirements
description: Transform Canvas strategy into user stories. Use when creating backlogs, writing requirements, defining features, or extracting product context from Canvas.
allowed-tools: Read, Grep, Glob
---


# Product Requirements

Transform Canvas strategy into actionable user stories.

## Purpose

Bridge strategy and execution by converting Canvas sections into structured product requirements. Based on Marty Cagan's Product Operating Model and Jeff Patton's User Story Mapping.

## When to Apply

- Translating Canvas (05-problem, 04-segments, 09-solution) into features
- Creating or refining product backlogs
- Writing user stories with acceptance criteria
- Building story maps for release planning
- 
## Boundaries

### This Skill Produces
- `context.md` — Canvas synthesis (problem, users, solution)
- `story-map.md` — Visual backbone of all stories
- `stories/{US-NNN}.md` — Individual user stories

### This Skill Does NOT Produce
- User flows → Use `product-design-flows` 
- Wireframes → Use `product-design-wireframes`
- Engineering handoffs → Use `product-handoff`

### Handoff Points
- Receives from: Canvas (strategy/canvas/), foundations-builder
- Provides to: product-design-flows (stories), product-prioritization (feature list)

## Process

### Step 1: Extract Product Context

Read Canvas sections and synthesize:

```
Canvas Files Required:
├── 05-problem.md  → Top 3 problems, intensity scores
├── 04-segments.md → Target users/personas
├── 09-solution.md → MVP features, key capabilities
└── 10-assumptions.md → Hypotheses to validate (optional)
```

**Output: context.md**
```markdown
# Product Context

## Target Users
- Primary: [segment from 04-segments]
- Secondary: [segment]

## Problems to Solve
1. [Problem #1] - Intensity: X/5
2. [Problem #2] - Intensity: X/5
3. [Problem #3] - Intensity: X/5

## Solution Direction
[Key capabilities from 09-solution]

## Critical Assumptions
- [Assumption that features must validate]
```

### Step 2: Build User Story Map

**2a. Define Backbone (User Activities)**
- Big activities user performs (left-to-right = time flow)
- These are goals, not features
- Example: "Find Product" → "Evaluate" → "Purchase" → "Use"

**2b. Break into User Tasks**
- Tasks within each activity (vertical slices)
- More specific actions within each goal
- Still user-focused, not feature-focused

**2c. Add User Stories**
- Stories under each task
- Format: "As a [user], I want [action] so that [benefit]"
- Organized by priority (top = higher)

**Output: story-map.md**
```
BACKBONE (Activities):
[Activity 1] → [Activity 2] → [Activity 3] → [Activity 4]

WALKING SKELETON (Minimum Path):
┌─────────────┬─────────────┬─────────────┬─────────────┐
│ Activity 1  │ Activity 2  │ Activity 3  │ Activity 4  │
├─────────────┼─────────────┼─────────────┼─────────────┤
│ Task 1.1    │ Task 2.1    │ Task 3.1    │ Task 4.1    │
│ - US-001   │ - US-003   │ - US-005   │ - US-007   │
│ - US-002   │ - US-004   │ - US-006   │             │
├─────────────┼─────────────┼─────────────┼─────────────┤
│ Task 1.2    │ Task 2.2    │ Task 3.2    │ Task 4.2    │
│ - US-008   │ - US-009   │ - US-010   │ - US-011   │
└─────────────┴─────────────┴─────────────┴─────────────┘

Release 1 (Walking Skeleton): US-001, US-003, US-005, US-007
Release 2: US-002, US-004, US-006, US-008
Release 3: US-009, US-010, US-011
```

### Step 3: Write User Stories

**Output: stories/US-{NNN}.md**

```markdown
# US-{NNN}: {Title}

**Story:**
As a [user type from 04-segments],
I want [action/capability],
so that [benefit/outcome].

**Acceptance Criteria:**
- [ ] GIVEN [context], WHEN [action], THEN [outcome]
- [ ] GIVEN [context], WHEN [action], THEN [outcome]
- [ ] [Edge case handled]

**Links:**
- Solves: [Problem from 05-problem]
- Validates: [Assumption from 10-assumptions]
- Depends on: [Other story ID or "None"]

**Priority:** P0/P1/P2
**Estimate:** S/M/L
```

**Story Quality Checklist:**
- [ ] Written from user perspective (not system)
- [ ] Describes outcome/benefit (not implementation)
- [ ] Independently valuable (can release alone)
- [ ] Testable (clear acceptance criteria)
- [ ] Links to validated problem
- [ ] Small enough to complete in one ai iteration

### Step 4: Ensure Outcome Focus

| Bad (Output) | Good (Outcome) |
|--------------|----------------|
| Build a dashboard | Users see progress at a glance |
| Add notifications | Users never miss important updates |
| Create settings page | Users customize their experience |
| Implement search | Users find what they need in <5 seconds |

For each feature/story verify:
- What user behavior does this change?
- What business metric does this move?
- How will we know if it worked?

## Output

This skill produces:
- `context.md`
- `story-map.md`
- `stories/US-{NNN}.md`

Agent handles placement in `artifacts/{product}/design/requirements/`

## Error Handling

### Canvas Not Found
```
Check: 05-problem.md, 04-segments.md, 09-solution.md exist
Action: "Canvas incomplete. Required files missing: [list]. 
        Run foundations-builder first or provide:
        - Target user segments
        - Top 3 problems to solve
        - Solution direction"
```

### Canvas Section Empty
```
Check: Required sections have content
Action: "Canvas section [X] exists but is empty.
        Provide [specific information needed] to proceed."
```

### Ambiguous Problem Definition
```
Check: Problems are specific and measurable
Action: "Problem '[X]' is too vague. Clarify:
        - Who experiences this?
        - When does it occur?
        - What's the impact?"
```

### Conflicting Inputs
```
Check: Stories align with Canvas
Action: "Story '[X]' conflicts with Canvas problem definition.
        Canvas says: [Y]. Story implies: [Z].
        Which takes precedence?"
```

## Key Principles

> "Fall in love with the problem, not the solution." — Marty Cagan

> "Your job isn't to build features, it's to build outcomes."

> "A story is a promise for a conversation." — Jeff Patton


## References

For patterns and examples, see:
- `references/story-examples.md` — Good/bad story examples
- `references/acceptance-criteria.md` — Writing testable criteria