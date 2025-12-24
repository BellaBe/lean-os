---
name: product-requirements
description: Transform Canvas strategy into product requirements and user stories. Use when translating business goals into features, creating user stories, or building product backlogs.
---

# Product Requirements

Transform Canvas strategy into actionable product requirements using empowered product team principles and user story mapping.

## Overview

This skill bridges strategy and execution by converting Canvas sections into structured product requirements. Based on Marty Cagan's Product Operating Model and Jeff Patton's User Story Mapping methodology.

**Primary Use Cases**: Feature definition, backlog creation, user story writing, requirements decomposition.

**Reads From Canvas**: 01-context, 05-problem, 09-solution, 04-segments, 10-assumptions

## Core Functions

### 1. Extract Product Context from Canvas

**Read and synthesize:**
- `05-problem.md` → Top 3 problems to solve
- `04-segments.md` → Target users/personas
- `09-solution.md` → MVP features and key capabilities
- `10-assumptions.md` → Hypotheses that requirements must validate

**Context Template:**
```
Product Context Summary

Target Users:
- Primary: [segment from 04-segments]
- Secondary: [segment]

Problems to Solve:
1. [Problem #1 from 05-problem] - Intensity: X/5
2. [Problem #2] - Intensity: X/5
3. [Problem #3] - Intensity: X/5

Solution Direction:
[Key capabilities from 09-solution]

Critical Assumptions:
- [Assumption that feature must validate]
- [Assumption]
```

### 2. Generate User Story Map

Create a visual map of the user's journey through the product.

**Step 1: Define the Backbone (User Activities)**
- Big activities user performs (left to right = time flow)
- These are goals, not features
- Example: "Find Product" → "Evaluate Options" → "Purchase" → "Use"

**Step 2: Break into User Tasks**
- Tasks within each activity (vertical slices)
- More specific actions within each goal
- Still user-focused, not feature-focused

**Step 3: Add User Stories**
- Stories under each task
- Format: "As a [user], I want [action] so that [benefit]"
- Organized by priority (top = higher priority)

**Output Template:**
```
User Story Map

BACKBONE (Activities):
[Activity 1] → [Activity 2] → [Activity 3] → [Activity 4]

WALKING SKELETON (Minimum Path):
┌─────────────┬─────────────┬─────────────┬─────────────┐
│ Activity 1  │ Activity 2  │ Activity 3  │ Activity 4  │
├─────────────┼─────────────┼─────────────┼─────────────┤
│ Task 1.1    │ Task 2.1    │ Task 3.1    │ Task 4.1    │
│ - Story A   │ - Story D   │ - Story G   │ - Story J   │
│ - Story B   │ - Story E   │ - Story H   │             │
├─────────────┼─────────────┼─────────────┼─────────────┤
│ Task 1.2    │ Task 2.2    │ Task 3.2    │ Task 4.2    │
│ - Story C   │ - Story F   │ - Story I   │ - Story K   │
└─────────────┴─────────────┴─────────────┴─────────────┘

Release 1 (Walking Skeleton): Stories A, D, G, J
Release 2: Stories B, E, H
Release 3: Stories C, F, I, K
```

### 3. Write User Stories

For each story in the map, create a complete specification.

**User Story Format:**
```
## US-{ID}: {Story Title}

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
```
□ Written from user perspective (not system)
□ Describes outcome/benefit (not implementation)
□ Independently valuable (can release alone)
□ Testable (clear acceptance criteria)
□ Links to validated problem
□ Small enough to complete in one sprint
```

### 4. Identify Outcome vs Output

Ensure requirements focus on outcomes, not outputs.

| Bad (Output) | Good (Outcome) |
|--------------|----------------|
| Build a dashboard | Users can see their progress at a glance |
| Add notifications | Users never miss important updates |
| Create settings page | Users can customize their experience |
| Implement search | Users can find what they need in <5 seconds |

**Outcome Questions:**
```
For each feature/story:
□ What user behavior does this change?
□ What business metric does this move?
□ How will we know if it worked?
□ What happens if we don't build it?
```

### 5. Create Product Requirements Document (PRD)

When formal documentation needed, create PRD from stories.

**PRD Template:**
```
# PRD: {Feature Name}

## Overview
**Objective:** [What we're trying to achieve - outcome]
**Owner:** [Product owner]
**Target Release:** [Date or release name]

## Context
**Problem:** [From 05-problem.md]
**User Segment:** [From 04-segments.md]
**Assumption Being Tested:** [From 10-assumptions.md]

## User Stories
[Include full stories from story map]

## Success Metrics
| Metric | Current | Target | How Measured |
|--------|---------|--------|--------------|
| [Activation] | X% | Y% | [Method] |
| [Engagement] | X | Y | [Method] |
| [Retention] | X% | Y% | [Method] |

## Scope

### In Scope
- [Feature/story included]
- [Feature/story included]

### Out of Scope
- [Explicitly excluded]
- [Future consideration]

## Risks & Dependencies
| Risk | Impact | Mitigation |
|------|--------|------------|
| [Risk] | [H/M/L] | [Strategy] |

## Open Questions
- [ ] [Question needing answer]
- [ ] [Question needing answer]
```

## Workflows

### Canvas → User Stories

```
1. Read Canvas sections (05-problem, 04-segments, 09-solution)
2. Extract product context summary
3. Build user story map (backbone → tasks → stories)
4. Identify walking skeleton (minimum viable release)
5. Write detailed stories with acceptance criteria
6. Link stories to assumptions (10-assumptions)
7. Output: Story map + prioritized backlog
```

### Feature Request → Requirements

```
1. Receive feature request
2. Map to existing Canvas problem (05-problem)
3. Identify target user segment (04-segments)
4. Write user stories (not feature specs)
5. Define success metrics (outcomes)
6. Link to assumptions to validate
7. Output: User stories with acceptance criteria
```

## Input Requirements

**Required:**
- Canvas files: 04-segments, 05-problem, 09-solution
- Feature area or objective to scope

**Optional:**
- 10-assumptions (for validation linkage)
- Existing backlog (for deduplication)
- User research (for story detail)

## Output Structure

```
Product Requirements Output:
├── context_summary.md     # Canvas synthesis
├── story_map.md           # Visual story map
├── stories/               # Individual story files
│   ├── US-001.md
│   ├── US-002.md
│   └── ...
└── release_plan.md        # Stories grouped by release
```

## Integration

**Receives from:**
- Canvas (strategy/canvas/) - problem, segment, solution context
- foundations-problem-solution-fit - validated problems

**Provides to:**
- product-design-flows - stories to map into journeys
- product-prioritization - stories to prioritize
- product-specification - stories to shape into pitches

## Best Practices

### Writing Stories
1. **User voice**: "As a user" not "The system shall"
2. **Independent**: Each story delivers value alone
3. **Negotiable**: Details can change, outcome is fixed
4. **Valuable**: Delivers user or business value
5. **Estimable**: Team can size it
6. **Small**: Fits in one sprint
7. **Testable**: Clear acceptance criteria

### Story Mapping
1. **Breadth first**: Map the whole journey before going deep
2. **Thin slices**: Walking skeleton spans all activities
3. **Priority by row**: Top row = must have, lower = nice to have
4. **Release by row**: Horizontal slices, not vertical features

### Avoiding Pitfalls
- Do NOT write feature specs ("The button shall...")
- Do NOT skip acceptance criteria
- Do NOT create stories without problem linkage
- Do NOT forget edge cases and error states

## Key Principles

> "Fall in love with the problem, not the solution." — Marty Cagan

> "Your job isn't to build features, it's to build outcomes." — Product Operating Model

> "A story is a promise for a conversation." — Jeff Patton

---

**Related Playbooks:**
- [product-operating-model](research/playbooks/product-operating-model.md)
- [user-story-mapping](research/playbooks/user-story-mapping.md)
