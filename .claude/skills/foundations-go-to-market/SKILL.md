---
name: foundations-go-to-market
description: Generate or update go-to-market strategy. Use when defining GTM motion, selecting channels, or planning launch.
allowed-tools: "Read,Write,WebSearch,WebFetch,AskUserQuestion"
---

# Go-to-Market Generator

Generate GTM strategy that all downstream skills read and adapt to.

## Core Principle

This skill answers: **How do we acquire customers?**

It produces ONE artifact: `strategy/canvas/15.go-to-market.md`

All other skills (marketing-narrative, content-strategy, channel-optimization, marketing-execution) read this file and adapt their behavior.

## Input Requirements

**Required (Canvas):**
- `strategy/canvas/04.segments.md`
- `strategy/canvas/05.problem.md`
- `strategy/canvas/07.uvp.md`
- `strategy/canvas/09.solution.md`
- `strategy/canvas/14.pricing-plans-revenue-streams.md` (for ACV assessment)

**Optional:**
- Existing `strategy/canvas/15.go-to-market.md` (if updating)
- Channel performance data (if iterating)
- Competitor GTM analysis

## Output

```
strategy/canvas/15.go-to-market.md
```

Single file. All GTM decisions in one place.

## GTM Motion Framework

### Step 1: Determine Motion Type

| Factor | PLG | Content-Led | Partner-Led | SLG |
|--------|-----|-------------|-------------|-----|
| ACV | <$10K | $10-50K | Varies | >$50K |
| Buyer | User = buyer | User + champion | Marketplace user | Committee |
| Complexity | Low (self-serve) | Medium (needs education) | Medium | High (needs demo) |
| Sales cycle | Days/weeks | Weeks/months | Days (install) | Months |
| Distribution | Direct | Direct | Platform | Direct |

**Questions to ask:**
1. Where do customers discover products like ours?
2. Can they self-serve or need human help?
3. What's typical deal size?
4. Who makes the buying decision?

See `references/motion-decision-tree.md` for detailed decision flow.

### Step 2: Select Primary Channel

Based on motion:

| Motion | Likely Primary Channel |
|--------|------------------------|
| PLG | Product (self-serve), Content |
| Content-Led | Blog, Social, SEO with sales-assist |
| Partner-Led | Marketplace, App store, Integrations |
| SLG | Outbound sales, Events, ABM |

**Rule:** One primary channel until validated. Max 2-3 total.

### Step 3: Define Channel Tactics

For each active channel, define:
- Investment level (HIGH/MEDIUM/LOW)
- Key activities
- Metrics to track
- Owner

### Step 4: Set Stage-Appropriate Goals

| Stage | Focus |
|-------|-------|
| Pre-launch | Validate channel fit |
| Launch (0-10K MRR) | 1 channel, prove CAC |
| Growth (10-100K) | Scale primary, test secondary |
| Scale (100K+) | Optimize mix, add channels |

## Generation Modes

### Mode 1: Initial GTM Strategy

**Trigger:** New product, no existing GTM

**Process:**
1. Analyze Canvas (segments, pricing, solution complexity)
2. Determine motion type
3. Recommend primary channel
4. Generate `15.go-to-market.md`

### Mode 2: GTM Update

**Trigger:** Channel performance data, market shift, stage change

**Process:**
1. Read existing `15.go-to-market.md`
2. Analyze what's working/not working
3. Recommend adjustments
4. Update file with rationale

### Mode 3: Channel Addition

**Trigger:** Ready to add secondary channel

**Process:**
1. Validate primary channel is working (CAC, conversion)
2. Evaluate candidate channels
3. Add to `15.go-to-market.md` with experiment plan

## Output Template

See `references/go-to-market-template.md` for full structure.

**Core sections:**

```markdown
# Go-to-Market Strategy

## GTM Motion
**Type:** {PLG | Content-Led | Partner-Led | SLG | Hybrid}
{Rationale}

## Stage
**Current:** {Pre-launch | Launch | Growth | Scale}

## Channels

### Primary: {Channel Name}
- Investment: HIGH
- Activities: {list}
- Metrics: {what to track}
- Owner: {who}

### Secondary: {Channel Name} (if applicable)
- Investment: MEDIUM
- Activities: {list}
- Metrics: {what to track}
- Owner: {who}

## Growth Loops
{How acquisition compounds}

## Stage Goals
{Current stage targets}
```

## Validation

Before completing:

- [ ] Motion type justified by ACV + buyer + complexity
- [ ] Primary channel aligns with motion
- [ ] Max 2-3 channels for current stage
- [ ] Each channel has clear metrics
- [ ] Growth loop identified (how acquisition compounds)

## Downstream Skills

These skills read `15.go-to-market.md` and adapt:

| Skill | What It Reads | How It Adapts |
|-------|---------------|---------------|
| marketing-narrative | Nothing | Identity-only, no adaptation |
| content-strategy | Motion, channels | Weights opportunities for motion fit |
| channel-optimization | All channels | Activates relevant modules |
| content-generation | Motion | Adapts content mode |
| content-delivery | Motion, channels | Routes + tracks appropriately |
| marketing-execution | Motion, stage, channels | Orchestrates subskills |

## References

- `references/go-to-market-template.md` — Full artifact template
- `references/motion-decision-tree.md` — How to choose motion
