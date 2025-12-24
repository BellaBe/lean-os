---
name: product-specification
description: Create shaped specifications for engineering handoff. Use when preparing features for development, writing pitches, or defining fixed-time/variable-scope work.
---

# Product Specification

Create shaped, time-boxed specifications ready for engineering using Shape Up methodology and sprint-based validation.

## Overview

This skill converts prioritized features into shaped pitches with clear boundaries, risks identified, and engineering-ready specifications. Follows fixed-time, variable-scope approach.

**Based on**: Shape Up (Ryan Singer) + Design Sprint (Jake Knapp)

**Primary Use Cases**: Engineering handoff, pitch creation, scope hammering, risk identification.

## Core Functions

### 1. Shape the Work

Transform raw ideas into shaped pitches with proper boundaries.

**Shaping Principles:**
| Principle | Meaning |
|-----------|---------|
| Fixed time, variable scope | Appetite (time) is fixed; scope adjusts to fit |
| Rough, not abstract | Enough detail to build, not micromanaged steps |
| Solved at boundaries | Major risks/questions answered before building |
| Rabbit holes identified | Known unknowns called out upfront |

**Shaped Pitch Template:**
```
# Pitch: {Feature Name}

## Problem
[1-2 paragraphs describing the problem we're solving]

### Current State
- What happens today: [Current behavior/pain]
- Who is affected: [Segment from 04-segments]
- Why it matters: [Impact/severity from 05-problem]

### Evidence
- [User quote or data point]
- [User quote or data point]
- [Metric or observation]

## Appetite
**Time box:** [1 week / 2 weeks / 6 weeks]

Why this appetite:
- [Rationale for time investment]
- [What we're NOT willing to spend more time on]

## Solution

### Concept
[2-3 sentences describing the solution approach]

### Fat Marker Sketch
```
┌─────────────────────────────────────┐
│                                     │
│  [Rough layout showing key          │
│   elements and relationships]       │
│                                     │
│  ┌─────────┐      ┌─────────┐      │
│  │ Element │ ──── │ Element │      │
│  └─────────┘      └─────────┘      │
│                                     │
│  Key interactions:                  │
│  → User does X                      │
│  → System responds Y                │
│                                     │
└─────────────────────────────────────┘
```

### Breadboard
```
[Place] ──── [Affordance] ───→ [Place]
   │
   │──── [Affordance] ───→ [Place]
```

Key screens/states:
1. [Screen name]: [What user sees/does]
2. [Screen name]: [What user sees/does]
3. [Screen name]: [What user sees/does]

### Core Flow
1. User starts at [entry point]
2. User does [action]
3. System [response]
4. User sees [result]
5. Success = [outcome achieved]

## Rabbit Holes
Things that could derail this if not handled:

| Hole | Risk | Mitigation |
|------|------|------------|
| [Technical unknown] | [What could go wrong] | [How to avoid] |
| [Scope creep area] | [What might expand] | [Explicit boundary] |
| [Integration risk] | [Dependency concern] | [How to de-risk] |

## No-Gos
Explicitly out of scope for this appetite:

- [ ] {Feature/scope item} - Why: [Rationale]
- [ ] {Feature/scope item} - Why: [Rationale]
- [ ] {Feature/scope item} - Why: [Rationale]

## Nice-to-Haves
Can include if time permits, cut if needed:

- [ ] {Enhancement} - Value: [Why nice]
- [ ] {Enhancement} - Value: [Why nice]
```

### 2. Define Appetite Levels

Choose the right time investment.

**Appetite Options:**
| Appetite | Duration | Scope | When to Use |
|----------|----------|-------|-------------|
| Small Batch | 1-2 weeks | Single feature | Well-understood, low risk |
| Big Batch | 6 weeks | Feature set | Complex, cross-functional |
| Spike | 1 week | Learning only | Need to answer unknowns first |

**Appetite Decision:**
```
Is the problem well-understood?
  ├── No → Spike (1 week to learn)
  └── Yes → Is solution straightforward?
              ├── Yes → Small Batch (1-2 weeks)
              └── No → Does scope fit 6 weeks?
                        ├── Yes → Big Batch (6 weeks)
                        └── No → Hammer the scope OR decline
```

### 3. Scope Hammering

Force scope to fit appetite, not appetite to fit scope.

**Scope Hammering Process:**
```
1. State the core problem
2. Define minimum viable solution (walking skeleton)
3. List everything "nice to have"
4. For each nice-to-have: "Does cutting this prevent core value?"
   - Yes → Keep
   - No → Cut (move to No-Gos)
5. Repeat until scope fits appetite
```

**Scope Hammering Template:**
```
## Scope Hammering: {Feature}

### Core Problem
[Single sentence - the ONE thing we must solve]

### Minimum Viable Solution
[Simplest thing that solves core problem]

### Scope Reduction Passes

| Item | Keep/Cut | Rationale |
|------|----------|-----------|
| [Feature aspect] | Keep | Required for core value |
| [Feature aspect] | Cut | Nice but not essential |
| [Feature aspect] | Keep | Enables primary use case |
| [Feature aspect] | Cut | Edge case, handle manually |
| [Feature aspect] | V2 | Valuable but breaks appetite |

### Final Scope
After hammering, this appetite includes:
- [Included item]
- [Included item]
- [Included item]

And explicitly excludes:
- [Excluded item] → No-Go
- [Excluded item] → V2 consideration
```

### 4. Identify Rabbit Holes

Find the unknowns that could sink the project.

**Rabbit Hole Categories:**
| Category | Signs | Examples |
|----------|-------|----------|
| Technical | "We've never done..." | New integration, unfamiliar tech |
| Design | "Not sure how to..." | Complex interaction, edge cases |
| Integration | "Depends on..." | Third-party APIs, other teams |
| Data | "We don't know if..." | Missing data, migration needed |

**Rabbit Hole Discovery:**
```
## Rabbit Hole Analysis

### Discovery Questions
For each part of the solution, ask:
□ Have we built something like this before?
□ What could take 10x longer than expected?
□ What external dependencies exist?
□ What questions do we NOT know how to answer?
□ What would a skeptical engineer ask?

### Identified Holes

Hole 1: {Name}
├── Category: [Technical/Design/Integration/Data]
├── Risk: [What could go wrong]
├── Probability: [High/Medium/Low]
├── Impact: [High/Medium/Low]
├── De-risk approach:
│   ├── Option A: [Spike first]
│   ├── Option B: [Simplify approach]
│   └── Option C: [Accept risk with fallback]
└── Decision: [Chosen approach]

Hole 2: {Name}
...
```

### 5. Create Engineering Specification

Transform shaped pitch into engineering-ready spec.

**Engineering Spec Template:**
```
# Engineering Spec: {Feature Name}

## Overview
**Pitch:** [Link to shaped pitch]
**Appetite:** [X weeks]
**Team:** [Assigned team/engineers]
**Start:** [Date]

## Problem Statement
[From pitch - 1 paragraph]

## Solution Summary
[From pitch - key approach]

## Technical Requirements

### Data Model
```
Entity: {Name}
├── field_1: type
├── field_2: type
└── field_3: type

Relationships:
- {Entity} has_many {Other}
- {Entity} belongs_to {Other}
```

### API Endpoints (if applicable)
| Method | Endpoint | Purpose |
|--------|----------|---------|
| POST | /api/resource | Create new |
| GET | /api/resource/:id | Retrieve |
| PUT | /api/resource/:id | Update |

### User Interface
[Reference wireframes from product-design-wireframes]

Key screens:
1. [Screen]: [Purpose]
2. [Screen]: [Purpose]

### Acceptance Criteria
- [ ] [Criterion from user story]
- [ ] [Criterion]
- [ ] [Criterion]
- [ ] [Edge case handled]
- [ ] [Error state handled]

## Scope Boundaries

### In Scope
- [Feature/capability included]
- [Feature/capability included]

### Out of Scope (No-Gos)
- [Explicitly excluded - don't build]
- [Explicitly excluded]

### Nice-to-Have (If Time Permits)
- [Enhancement - cut first if needed]
- [Enhancement]

## Known Risks (Rabbit Holes)
| Risk | Mitigation | Owner |
|------|------------|-------|
| [From pitch] | [Approach] | [Who] |

## Dependencies
- [External dependency]
- [Internal dependency]
- [Data/infrastructure need]

## Testing Requirements
- [ ] Unit tests for [component]
- [ ] Integration tests for [flow]
- [ ] Edge cases: [list]
- [ ] Error states: [list]

## Definition of Done
- [ ] Acceptance criteria met
- [ ] Tests passing
- [ ] No-gos respected
- [ ] Code reviewed
- [ ] Deployed to staging
```

### 6. Sprint Validation (Design Sprint Integration)

For high-risk features, validate before full build.

**When to Sprint:**
- High uncertainty in solution
- Major investment (6-week appetite)
- Customer-facing changes
- New market/segment

**Sprint Output Template:**
```
## Validation Sprint: {Feature}

### Sprint Goal
Validate: [Core hypothesis to test]

### Prototype Scope
[Minimum needed to test hypothesis]

### Test Plan
- Target users: [From 04-segments]
- Number of tests: [5-8 recommended]
- Success criteria: [What must be true]

### Findings

| Participant | Task Success | Key Feedback |
|-------------|--------------|--------------|
| User 1 | [Yes/No/Partial] | [Quote/observation] |
| User 2 | [Yes/No/Partial] | [Quote/observation] |
...

### Patterns Observed
- [Pattern 1]: Seen in [X/5] users
- [Pattern 2]: Seen in [X/5] users

### Verdict
[ ] Proceed to build (hypothesis validated)
[ ] Iterate (adjust based on feedback)
[ ] Pivot (fundamental assumption wrong)
[ ] Kill (not worth pursuing)

### Adjustments for Build
Based on sprint learnings:
- Change: [Adjustment to make]
- Add: [Thing we learned we need]
- Remove: [Thing that didn't work]
```

## Workflows

### Feature → Shaped Pitch

```
1. Read prioritized feature (from product-prioritization)
2. Define problem clearly (from Canvas 05-problem)
3. Set appetite (1 week / 2 weeks / 6 weeks)
4. Sketch solution (fat marker, breadboard)
5. Hammer scope to fit appetite
6. Identify rabbit holes
7. Define no-gos explicitly
8. Output: Shaped pitch
```

### Shaped Pitch → Engineering Spec

```
1. Read shaped pitch
2. Extract technical requirements
3. Define data model and APIs
4. Reference wireframes (from product-design-wireframes)
5. Convert stories to acceptance criteria
6. Document risks and mitigations
7. Define testing requirements
8. Output: Engineering specification
```

### High-Risk → Validation Sprint

```
1. Identify high-risk assumption
2. Define sprint goal (what to validate)
3. Create minimal prototype
4. Test with 5-8 target users
5. Synthesize patterns
6. Make proceed/iterate/pivot/kill decision
7. Adjust specification based on learnings
8. Output: Validated (or invalidated) direction
```

## Input Requirements

**Required:**
- Prioritized feature (from product-prioritization)
- User stories (from product-requirements)
- Flow diagrams (from product-design-flows)

**Optional:**
- Wireframes (from product-design-wireframes)
- Technical constraints
- Previous sprint learnings

## Output Structure

```
Specification Output:
├── pitches/
│   ├── pitch-{feature-1}.md
│   ├── pitch-{feature-2}.md
│   └── ...
├── specs/
│   ├── spec-{feature-1}.md
│   ├── spec-{feature-2}.md
│   └── ...
└── sprints/
    ├── sprint-{feature}.md  # If validation run
    └── ...
```

## Integration

**Receives from:**
- product-prioritization - which features to shape
- product-requirements - user stories
- product-design-flows - interaction flows
- product-design-wireframes - visual specs

**Provides to:**
- Engineering teams - ready-to-build specifications
- Canvas 10-assumptions - hypotheses to validate
- goal-tracker - milestone completion

## Best Practices

### Shaping
1. **Problem before solution**: Shape the problem space first
2. **Fat marker sketches**: Just enough to communicate, not UI design
3. **Fixed appetite**: Time is non-negotiable; scope adjusts
4. **Identify unknowns**: Better to find rabbit holes now

### Scope Hammering
1. **Core value focus**: What's the ONE thing?
2. **Say no often**: Most things are nice-to-have
3. **V2 list**: Things to consider later, not now
4. **Walking skeleton**: Thinnest slice that works

### Risk Management
1. **Spikes for unknowns**: Learn before committing
2. **Fallback plans**: What if rabbit hole hits?
3. **Time buffers**: Built into appetite, not added
4. **No-go clarity**: Explicit > implicit boundaries

### Avoiding Pitfalls
- Do NOT shape too precisely (that's design)
- Do NOT expand appetite to fit scope
- Do NOT hide rabbit holes (surface them)
- Do NOT skip no-gos (scope creeps)

## Key Principles

> "Appetite is the amount of time we want to spend on a project. It's the input, not the output." — Shape Up

> "Fixed time, variable scope: If we decide to do it, we'll give it the time we've set aside but not more."

> "Shape the work before giving it to a team. Focus on the problem, set boundaries, reduce risk."

> "Declare out of bounds anything that could cause the project to balloon." — Shape Up

---

**Related Playbooks:**
- [product-shaping](research/playbooks/product-shaping.md)
- [product-sprint](research/playbooks/product-sprint.md)
