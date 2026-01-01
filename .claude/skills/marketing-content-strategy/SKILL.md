---
name: marketing-content-strategy
description: Motion-aware content discovery and opportunity detection. Use when: searching for content opportunities, detecting campaign triggers, finding engagement opportunities, evaluating content potential. Reads GTM motion from 15.gtm.md and adapts scoring accordingly.
allowed-tools: "Read,Write,WebSearch,WebFetch,AskUserQuestion"
---

# Content Strategy: Discovery & Opportunity Detection

Find opportunities that serve your GTM motion  -  loops for content-led, reviews for partner-led, enablement for sales-led.

## Core Principle

Opportunities are scored based on GTM motion. What matters for PLG differs from what matters for Partner-Led.

## Context Loading

**Required:**
- `strategy/canvas/04.segments.md`  -  Target audience
- `strategy/canvas/05.problem.md`  -  Problems we solve
- `strategy/canvas/07.uvp.md`  -  Value proposition
- `strategy/canvas/15.gtm.md`  -  Motion, channels, stage
- `artifacts/marketing/narrative/content-pillars.md`  -  What we talk about

If GTM file missing → Flag "Run go-to-market skill first"

## Motion Detection

```python
gtm = read("strategy/canvas/15.gtm.md")

if gtm.motion in ["PLG", "Content-Led"]:
    mode = "loop-driven"
elif gtm.motion == "Partner-Led":
    mode = "marketplace-driven"
elif gtm.motion == "SLG":
    mode = "sales-driven"
else:
    mode = "hybrid"
```

---

## Mode: Loop-Driven (PLG, Content-Led)

### Opportunity Sources

| Trigger Source | Loop Opportunity |
|----------------|------------------|
| User implements our method | Feature their before/after |
| Community question answered | Expand to article |
| Client success documented | Case study → authority |
| Strategic insight validated | Thought leadership |
| Someone shares our content | Engage, amplify |

### Scoring

```
Impact = (Loop Potential × Velocity Story × Audience Alignment) / 3
```

**Loop Potential:**

| Score | Criteria |
|-------|----------|
| 1.0 | Explicitly generates user response/implementation |
| 0.8 | High probability of sharing/engagement |
| 0.6 | Could trigger loop if executed well |
| 0.4 | Standalone value, weak loop |
| 0.2 | Pure broadcast, no loop possible |

**Velocity Story:**

| Score | Criteria |
|-------|----------|
| 1.0 | Clear before → after with time compression |
| 0.7 | Transformation story without time element |
| 0.4 | Insight without transformation |
| 0.2 | Information only |

**Audience Alignment:**

| Score | Criteria |
|-------|----------|
| 1.0 | Exact target segment problem |
| 0.7 | Adjacent segment or problem |
| 0.4 | General audience relevance |
| 0.2 | Tangential connection |

### Thresholds

- ≥0.7: Flag immediately
- 0.5-0.7: Add to backlog
- <0.5: Skip

---

## Mode: Marketplace-Driven (Partner-Led)

### Opportunity Sources

| Trigger Source | Marketplace Opportunity |
|----------------|------------------------|
| Merchant success in product | Request review |
| Common support question | Create help article |
| Feature shipped | Changelog + announcement |
| Competitor weakness identified | Listing optimization |
| Keyword ranking opportunity | Description update |

### Scoring

```
Impact = (Review Potential × Install Impact × Retention Value) / 3
```

**Review Potential:**

| Score | Criteria |
|-------|----------|
| 1.0 | Active user, clear success, never asked |
| 0.8 | Active user, moderate success |
| 0.6 | Active user, unclear success |
| 0.4 | Passive user |
| 0.2 | At-risk user |

**Install Impact:**

| Score | Criteria |
|-------|----------|
| 1.0 | Addresses top discovery keyword |
| 0.8 | Addresses high-volume keyword |
| 0.6 | Improves listing conversion |
| 0.4 | Marginal improvement |
| 0.2 | No install impact |

**Retention Value:**

| Score | Criteria |
|-------|----------|
| 1.0 | Reduces top churn reason |
| 0.8 | Addresses common confusion |
| 0.6 | Improves onboarding |
| 0.4 | Nice to have |
| 0.2 | No retention impact |

### Thresholds

- ≥0.7: Flag immediately
- 0.5-0.7: Add to backlog
- <0.5: Skip

---

## Mode: Sales-Driven (SLG)

### Opportunity Sources

| Trigger Source | Sales Opportunity |
|----------------|-------------------|
| Deal lost to competitor | Battle card needed |
| Objection repeated across deals | Objection handling content |
| Customer win with metrics | Case study |
| New vertical showing interest | Vertical-specific content |
| Sales requesting asset | Prioritize creation |

### Scoring

```
Impact = (Deal Enablement × Objection Coverage × Stage Fit) / 3
```

**Deal Enablement:**

| Score | Criteria |
|-------|----------|
| 1.0 | Sales explicitly requesting |
| 0.8 | Would help multiple active deals |
| 0.6 | Would help future deals |
| 0.4 | General sales support |
| 0.2 | Not deal-related |

**Objection Coverage:**

| Score | Criteria |
|-------|----------|
| 1.0 | Addresses top 3 objection |
| 0.8 | Addresses common objection |
| 0.6 | Addresses occasional objection |
| 0.4 | Preemptive positioning |
| 0.2 | No objection relevance |

**Stage Fit:**

| Score | Criteria |
|-------|----------|
| 1.0 | Gap at high-value stage (decision) |
| 0.8 | Gap at consideration stage |
| 0.6 | Gap at awareness stage |
| 0.4 | Content exists but outdated |
| 0.2 | Content exists and current |

### Thresholds

- ≥0.7: Flag immediately
- 0.5-0.7: Add to backlog
- <0.5: Skip

---

## Mode: Hybrid

When motion is Hybrid:
1. Identify which segment the opportunity serves
2. Apply that segment's motion scoring
3. Note cross-segment potential

---

## Output Format

```markdown
## Discovery Results - {date}

### Motion: {mode}

### High Priority Opportunities

| Source | Opportunity | Score | Motion Fit | Action |
|--------|-------------|-------|------------|--------|
| {where} | {what} | {score} | {why it fits motion} | {next step} |

### Backlog

| Opportunity | Score | Notes |
|-------------|-------|-------|
| {what} | {score} | {context} |

### Skipped (with rationale)

| Opportunity | Score | Why Skipped |
|-------------|-------|-------------|
| {what} | {score} | {doesn't fit motion because...} |
```

## Handoff to Execution

When opportunity approved:

1. Create thread: `threads/marketing/campaigns/{slug}/`
2. Complete stages 1-4:
   - 1-input.md: What triggered this opportunity
   - 2-hypothesis.md: Expected outcome
   - 3-implication.md: What success means
   - 4-decision.md: Content plan with motion-appropriate design
3. 4-decision.md triggers `marketing-execution`

## Boundaries

**DO:**
- Read GTM motion first
- Apply motion-appropriate scoring
- Prioritize based on motion fit
- Flag opportunities in ops/today.md
- Consider pillar alignment

**DON'T:**
- Apply loop scoring to Partner-Led opportunities
- Prioritize content that doesn't serve motion
- Ignore GTM stage (pre-launch vs scale)
- Create content for calendar, not strategy