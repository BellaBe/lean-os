---
name: solution-designing
description: Designs MVP feature set, selects growth architecture (PLG/Network/Traditional), and maps features to problems. Produces 09.solution.md. Use when defining MVP scope, selecting growth model, designing product features, or planning what to build.
allowed-tools: Read, Write, Grep
license: Complete terms in LICENSE.txt
---

# Solution Designing

Design MVP feature set aligned with growth architecture.

## Canvas Files

- **Reads:** 05.problem.md (problems to solve), 07.uvp.md (value constraints), 04.segments.md (buyer characteristics)
- **Reads:** 00.mode.md (VENTURE/BOOTSTRAP affects scope)
- **Writes:** 09.solution.md

## Prerequisites

Before designing solution:
- `strategy/canvas/05.problem.md` must exist (features solve problems)
- `strategy/canvas/07.uvp.md` should exist (solution must deliver UVP)

If missing:
```
"Solution design requires problems from 05.problem.md.

Features are means to solve problems — without problems, features are guesses.

Run problem-validating skill or foundations-research agent first."
```

## Process

### Step 1: Load Context

Read from canvas:
- **Problems** from 05.problem.md — What to solve (ranked by severity)
- **UVP** from 07.uvp.md — Value to deliver
- **Segment** from 04.segments.md — Buyer characteristics
- **Mode** from 00.mode.md — Scope constraints

### Step 2: Select Growth Architecture

Growth model determines feature requirements. Gather inputs:

| Input | Question | Source |
|-------|----------|--------|
| ACV | Expected price point? | 12.revenue or ask |
| Buyer Type | User = buyer? Committee? | 04.segments |
| Time-to-Value | How fast to first value? | Product nature |
| Collaboration | Inherently collaborative? | Product nature |
| Shareability | Can users share output? | Product nature |

**Selection Matrix:**

| Factor | Traditional | PLG | Network-Led |
|--------|-------------|-----|-------------|
| ACV | >$25K | <$5K | <$5K |
| Buyer | Committee | User = Buyer | User = Buyer |
| Time-to-Value | Weeks+ | <1 day | <1 day |
| Collaboration | Optional | Optional | **Inherent** |
| Shareability | Low | Medium | **High** |

**Decision Logic:**
```
IF ACV >$25K OR Committee buyer:
    → Traditional (sales-led)
    
ELIF ACV <$5K AND User=Buyer AND Fast TTV:
    IF Inherently collaborative AND High shareability:
        → Network-Led (viral)
    ELSE:
        → PLG (product-led)
        
ELSE:
    → Hybrid (segment by buyer type)
```

### Step 3: Define Growth-Required Features

Based on selected model, identify required infrastructure:

**Traditional Model:**
| Requirement | Feature | Priority |
|-------------|---------|----------|
| Demo capability | Demo environment | P1 |
| Pilot support | Limited trial mode | P1 |
| Sales enablement | Analytics dashboard | P2 |

**PLG Model:**
| Requirement | Feature | Priority |
|-------------|---------|----------|
| Self-serve acquisition | Signup flow | P0 |
| Fast time-to-value | Onboarding wizard | P0 |
| Conversion triggers | Usage limits, upgrade prompts | P0 |
| PQL signals | Usage analytics | P1 |
| In-app guidance | Tooltips, empty states | P1 |

**Network-Led Model:**
| Requirement | Feature | Priority |
|-------------|---------|----------|
| Viral mechanics | Invite system | P0 |
| Collaboration core | Multi-user workspace | P0 |
| Shareable output | Public links, embeds | P0 |
| Team expansion | Org management | P1 |
| Referral program | Referral tracking | P1 |
| Network visualization | Connection graph | P2 |

### Step 4: Map Features to Problems

For each problem in 05.problem.md:

1. **Identify core feature** — What directly solves this problem?
2. **Define user story** — As [segment], I want [action] so that [outcome]
3. **Set acceptance criteria** — What proves it works?
4. **Estimate complexity** — S/M/L

**Problem-Feature Matrix:**
| Problem | Core Feature | User Story | Complexity |
|---------|--------------|------------|------------|
| P1: [Name] | [Feature] | [Story] | S/M/L |
| P2: [Name] | [Feature] | [Story] | S/M/L |
| P3: [Name] | [Feature] | [Story] | S/M/L |

### Step 5: Prioritize MVP Scope

Combine growth features + problem features:

**P0 (Launch Required):**
- Minimum to deliver core UVP
- Essential growth mechanics for selected model
- Must ship before any users

**P1 (Fast Follow):**
- Enhanced value delivery
- Growth optimization
- First 30 days post-launch

**P2 (Scale):**
- Nice-to-have value
- Advanced growth mechanics
- When PMF signals appear

**Prioritization Criteria:**
| Criterion | Weight |
|-----------|--------|
| Problem severity solved | 40% |
| Growth model requirement | 30% |
| Complexity (inverse) | 20% |
| Dependency (blocker for others) | 10% |

### Step 6: Define Growth Loops

Based on growth model, specify primary loops:

**PLG Loops:**
| Loop | Type | Mechanism |
|------|------|-----------|
| Acquisition | Content → Signup → Activate |
| Retention | Use → Value → Habit |
| Expansion | Usage → Limit → Upgrade |

**Network-Led Loops:**
| Loop | Type | Mechanism |
|------|------|-----------|
| Viral | User → Invite → New User → Invite |
| Content | Create → Share → View → Signup |
| Team | User → Add Member → Member → Add More |

**Traditional Loops:**
| Loop | Type | Mechanism |
|------|------|-----------|
| Demand | Content → Lead → Nurture → Demo |
| Sales | Demo → Trial → Close → Reference |
| Expand | Success → Upsell → Reference |

### Step 7: Define NOT in MVP

Explicitly list what's excluded and why:

| Excluded Feature | Reason | Add When |
|------------------|--------|----------|
| [Feature A] | [Why not now] | [Trigger condition] |
| [Feature B] | [Why not now] | [Trigger condition] |

This prevents scope creep and documents decisions.

### Step 8: Write Output

Write to `strategy/canvas/09.solution.md` using output format below.

## Output Format

```markdown
# 09. Solution

## Growth Architecture

**Model:** [Traditional | PLG | Network-Led | Hybrid]

### Selection Rationale

| Factor | Value | Points To |
|--------|-------|-----------|
| ACV | $[X] | [Model] |
| Buyer | [Type] | [Model] |
| Time-to-Value | [Duration] | [Model] |
| Collaboration | [Level] | [Model] |
| Shareability | [Level] | [Model] |

**Conclusion:** [Model] because [primary reason]

### Growth-Required Features

| Feature | Purpose | Priority |
|---------|---------|----------|
| [Feature] | [Growth mechanism] | P0/P1 |

### Growth Loops

| Loop Name | Type | Mechanism |
|-----------|------|-----------|
| [Name] | [Acquisition/Retention/Expansion/Viral] | [How it works] |

---

## Problem-Solution Mapping

### P1: [Problem Name] → [Feature Name]

**User Story:** As [segment], I want [action] so that [outcome].

**Acceptance Criteria:**
- [ ] [Criterion 1]
- [ ] [Criterion 2]

**Complexity:** [S/M/L]
**Priority:** [P0/P1/P2]

---

### P2: [Problem Name] → [Feature Name]

[Same structure]

---

### P3: [Problem Name] → [Feature Name]

[Same structure]

---

## MVP Feature Set

### P0 — Launch Required

| Feature | Problem Solved | Growth Role | Complexity |
|---------|----------------|-------------|------------|
| [Feature] | [Problem] | [Role] | S/M/L |

**Total P0 Complexity:** [Sum estimate]

### P1 — Fast Follow (30 days)

| Feature | Problem Solved | Growth Role | Complexity |
|---------|----------------|-------------|------------|
| [Feature] | [Problem] | [Role] | S/M/L |

### P2 — Scale Phase

| Feature | Problem Solved | Growth Role | Complexity |
|---------|----------------|-------------|------------|
| [Feature] | [Problem] | [Role] | S/M/L |

---

## NOT in MVP

| Feature | Why Excluded | Add When |
|---------|--------------|----------|
| [Feature] | [Reason] | [Trigger] |

---

## Technical Approach

**Architecture:** [High-level approach]

**Key Decisions:**
| Decision | Choice | Rationale |
|----------|--------|-----------|
| [Decision] | [Choice] | [Why] |

**Build vs Buy:**
| Component | Decision | Rationale |
|-----------|----------|-----------|
| [Component] | Build/Buy | [Why] |

---

## Success Criteria

| Milestone | Metric | Target |
|-----------|--------|--------|
| Activation | [What shows value delivered] | [Target] |
| Retention | [What shows ongoing value] | [Target] |
| Growth | [Model-specific metric] | [Target] |
```

## Quality Criteria

Before finalizing, verify:

- [ ] Growth model selected with rationale
- [ ] Every problem has at least one feature
- [ ] Every feature traces to problem or growth requirement
- [ ] P0 scope is minimal viable
- [ ] NOT in MVP section populated
- [ ] Growth loops defined for selected model
- [ ] Success criteria are measurable

## Growth Model Quick Reference

| Model | Key Feature | Key Metric | Risk |
|-------|-------------|------------|------|
| Traditional | Sales enablement | Win rate | High CAC |
| PLG | Self-serve + conversion | Activation rate | Conversion |
| Network-Led | Viral mechanics | K-factor | Cold start |
| Hybrid | Segment-specific paths | Blended CAC | Complexity |

## Mode Adjustments

| Mode | MVP Scope | Growth Investment |
|------|-----------|-------------------|
| VENTURE | Larger — capture market | Higher — optimize later |
| BOOTSTRAP | Smaller — revenue first | Lower — efficiency focus |
| HYBRID | Moderate — validate first | Moderate — optionality |

## Boundaries

- Does NOT validate technical feasibility
- Does NOT estimate development time
- Does NOT design UI/UX
- Growth model is hypothesis until proven
- Feature priorities are starting point, not fixed
- Does NOT handle technical architecture detail
- Requires problems from 05.problem.md before execution
- MVP scope assumes constrained resources