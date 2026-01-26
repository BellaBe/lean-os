---
name: value-positioning
description: Crafts value propositions, market positioning, and moat analysis. Use when creating UVP statements, defining market positioning, analyzing competitive differentiation, or building unfair advantages.
allowed-tools: Read, Grep
license: Complete terms in LICENSE.txt
---

# Value Positioning

Craft differentiated value propositions and defensible market positioning.

## Canvas Files

- **Reads:** 04.segments.md (target segment, pain intensity)
- **Reads:** 05.problem.md (top problems by severity)
- **Reads:** 06.competitive.md (positioning gaps, competitor weaknesses)
- **Writes:** 07.uvp.md, 08.unfair.md

## Prerequisites

Before crafting positioning:
- `strategy/canvas/04.segments.md` must exist with primary segment
- `strategy/canvas/05.problem.md` must exist with ranked problems
- `strategy/canvas/06.competitive.md` should exist for differentiation

If missing:
```
"Value positioning requires customer intelligence (G1).

Missing: [list missing files]

Run foundations-research agent first."
```

## Process

### Step 1: Load Context

Read from canvas:
- **Primary segment** from 04.segments.md
- **Top problem** from 05.problem.md (highest severity)
- **Positioning gaps** from 06.competitive.md

### Step 2: Select Positioning Strategy

| Strategy | When to Use | Risk | Reward |
|----------|-------------|------|--------|
| **Compete** | 10x better at existing category | High | Established demand |
| **Differentiate** | Same category, unique attribute | Medium | Clear comparison |
| **Subcategory** | New segment of existing | Low-Medium | Targeted |
| **Create** | Define new category | Very High | Category leadership |

**Decision factors:**
- Compete: Only if you have clear 10x advantage
- Differentiate: Default choice for most startups
- Subcategory: When serving underserved niche
- Create: When problem is real but unnamed

### Step 3: Craft UVP Statement

**For-Only-That Formula:**
```
For [target segment]
Who [has specific problem/need]
[Product name] is a [category]
That [primary benefit / key value]
Unlike [primary alternative]
We [key differentiator]
```

**Value Equation (maximize):**
```
Value = (Dream Outcome × Perceived Likelihood) / (Time Delay × Effort)
```

| Driver | How to Increase |
|--------|-----------------|
| Dream Outcome | Bigger promise, clearer benefit |
| Likelihood | Proof points, guarantees, social proof |
| Time (decrease) | Faster results, quick wins |
| Effort (decrease) | Easier to use, less change required |

### Step 4: Generate Alternatives

Create 3 UVP variations emphasizing different aspects:
1. **Outcome-focused:** Emphasize dream outcome
2. **Speed-focused:** Emphasize time savings
3. **Ease-focused:** Emphasize reduced effort

Select strongest based on segment pain signals.

### Step 5: Analyze Moats (for 08.unfair.md)

| Moat Type | Defensibility | Time to Build | Time to Copy |
|-----------|---------------|---------------|--------------|
| Network Effects | Very High | 2-5 years | 5-10+ years |
| Switching Costs | High | 1-3 years | 2-5 years |
| Scale Economies | High | 3-5 years | 5-10 years |
| Data Advantage | High | 2-4 years | 3-7 years |
| Brand | Medium | 5-10 years | 5-10 years |
| IP/Patents | Medium | 1-5 years | 1-5 years |
| Team Expertise | Low-Medium | 1-2 years | 1-2 years |

**Score each potential moat:**
- Strength (1-5): How strong today?
- Defensibility (1-5): How hard to replicate?
- Durability (1-5): How long will it last?

### Step 6: Write Output

Write to `strategy/canvas/07.uvp.md` and `strategy/canvas/08.unfair.md`.

## Output Format: 07.uvp.md

```markdown
# 07. Unique Value Proposition

## Target Segment
[From 04.segments — primary segment name and characteristics]

## Core Problem
[From 05.problem — highest severity problem statement]

## Positioning Strategy

**Approach:** [Compete | Differentiate | Subcategory | Create]
**Rationale:** [Why this approach fits]

## UVP Statement

For [segment]
Who [problem]
[Product] is a [category]
That [benefit]
Unlike [alternative]
We [differentiator]

## Value Drivers

| Driver | How We Deliver | Strength |
|--------|----------------|----------|
| Dream Outcome | [What success looks like] | [1-5] |
| Likelihood | [Why they'll believe] | [1-5] |
| Time Reduction | [How we're faster] | [1-5] |
| Effort Reduction | [How we're easier] | [1-5] |

## Proof Points

- [Evidence 1]
- [Evidence 2]
- [Evidence 3]

## Alternative UVPs Considered

| Alternative | Why Not Selected |
|-------------|------------------|
| [UVP 2] | [Reason] |
| [UVP 3] | [Reason] |
```

## Output Format: 08.unfair.md

```markdown
# 08. Unfair Advantage

## Current Moats

| Advantage | Type | Strength | Defensibility | Time to Copy |
|-----------|------|----------|---------------|--------------|
| [Advantage 1] | [Type] | [1-5] | [1-5] | [X months] |
| [Advantage 2] | [Type] | [1-5] | [1-5] | [X months] |

## Primary Moat

**Type:** [Strongest moat type]
**Description:** [How it works]
**Current Strength:** [Assessment]
**Defense Strategy:** [How to strengthen over time]

## Moat Building Plan

| Phase | Action | Moat Strengthened | Timeline |
|-------|--------|-------------------|----------|
| Now | [Action] | [Moat] | 0-3 mo |
| Next | [Action] | [Moat] | 3-6 mo |
| Later | [Action] | [Moat] | 6-12 mo |

## Honest Assessment

**What's Actually Defensible:**
- [Real advantage]

**What's NOT Defensible (be honest):**
- [Advantage that sounds good but isn't]

**Moats We Don't Have Yet:**
- [Future moat to build]
```

## Quality Criteria

Before finalizing, verify:

- [ ] UVP is single statement (not paragraph)
- [ ] Segment, problem, alternative all specific (not generic)
- [ ] Benefit is outcome, not feature
- [ ] Differentiator is defensible
- [ ] At least one moat scores 4+ on defensibility
- [ ] Honest assessment section is actually honest

## Positioning Matrix

```
                    HIGH PRICE
                        │
    Premium             │            Luxury
    (High value,        │       (Exclusivity)
     justified price)   │
                        │
LOW VALUE ──────────────┼────────────── HIGH VALUE
                        │
    Commodity           │            Value Leader
    (Race to bottom)    │       (Best value/price)
                        │
                    LOW PRICE
```

**Target positions:** Upper right (premium) or lower right (value leader)

## Boundaries

- Does NOT validate UVP resonance (requires customer testing)
- Does NOT guarantee market acceptance
- Does NOT assess competitor response capability
- Positioning is hypothesis until market-tested
- Moat assessment is current state, not prediction
- Does NOT handle brand positioning or messaging hierarchy
- Requires customer intelligence (G1) before execution