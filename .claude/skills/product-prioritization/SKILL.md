---
name: product-prioritization
description: Prioritize features using DHM framework. Use when deciding what to build next, scoring initiatives, stack ranking features, or managing roadmaps.
allowed-tools: Read, Grep, Glob
---

# Product Prioritization

Prioritize product work using DHM (Delight, Hard-to-copy, Margin) framework.

## Purpose

Score and rank features to decide what to build first.

## When to Apply

- Deciding which features to build next
- Scoring and comparing initiatives
- Building roadmaps
- Evaluating feature requests

## Boundaries

### This Skill Produces
- `{date}-dhm-scores.md` — Scored initiatives
- `{date}-stack-rank.md` — Prioritized list

### This Skill Does NOT Produce
- User stories → Use `product-requirements`
- Engineering handoffs → Use `product-handoff`

### Handoff Points
- Receives from: product-requirements (features to score)
- Provides to: product-handoff (what to build)

## Process

### Step 1: Score with DHM

**Dimensions:**
| Letter | Dimension | Question |
|--------|-----------|----------|
| **D** | Delight | Does this make customers love us? |
| **H** | Hard to copy | Can competitors replicate easily? |
| **M** | Margin | Does this improve economics? |

**Score Each Initiative (1-5):**
```markdown
## {Initiative Name}

### D: Delight
Score: [1-5]
Evidence: [Why users will love this]

### H: Hard to Copy
Score: [1-5]
Evidence: [What makes this defensible]
- Brand, Network effects, Technology, Scale, Switching costs

### M: Margin
Score: [1-5]
Evidence: [Revenue/cost impact]

### Total: [X/15]
```

### Step 2: Stack Rank

**Output: {date}-stack-rank.md**
```markdown
# Stack Rank: {Date}

## Ranked Features
| Rank | Feature | D | H | M | Total | Status |
|------|---------|---|---|---|-------|--------|
| 1 | [Name] | 5 | 4 | 4 | 13 | Ready |
| 2 | [Name] | 4 | 5 | 3 | 12 | Ready |
| 3 | [Name] | 5 | 2 | 4 | 11 | Needs design |

## Verdicts
- **Prioritize (12+):** [Features]
- **Consider (9-11):** [Features]
- **Deprioritize (<9):** [Features]

## Next Actions
1. [Feature X]: Ready for handoff
2. [Feature Y]: Needs flow design first
```

### Scoring Guide

**Delight (D):**
| Score | Meaning |
|-------|---------|
| 5 | Solves top pain, users will love |
| 3 | Nice to have, appreciated |
| 1 | Meh, won't notice |

**Hard to Copy (H):**
| Score | Meaning |
|-------|---------|
| 5 | >12 months to copy, builds moat |
| 3 | 3-6 months to copy |
| 1 | Days/weeks, easily copied |

**Margin (M):**
| Score | Meaning |
|-------|---------|
| 5 | Significant revenue/retention impact |
| 3 | Moderate impact |
| 1 | No measurable impact |

## Output

This skill produces:
- `{date}-dhm-scores.md`
- `{date}-stack-rank.md`

Agent handles placement in `artifacts/{product}/prioritization/`

## Error Handling

### No Features to Score
```
Action: "No features provided. Run product-requirements first or provide feature list."
```

### Missing Business Context
```
Action: "Missing context for scoring. Provide:
        - Who are target customers? (for D)
        - What's our moat? (for H)
        - Revenue model? (for M)"
```

### Tied Scores
```
Action: "Features [X] and [Y] tied at [score].
        Tiebreakers:
        1. H wins (defensibility)
        2. Lower effort wins
        3. Faster value wins"
```

## References

For patterns and examples, see:
- `references/dhm-examples.md` — Scoring examples