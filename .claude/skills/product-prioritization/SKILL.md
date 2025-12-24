---
name: product-prioritization
description: Prioritize features and tasks using DHM and LNO frameworks. Use when deciding what to build next, scoring initiatives, or managing daily work priorities.
---

# Product Prioritization

Prioritize product work at strategic and tactical levels using DHM (Delight, Hard-to-copy, Margin) and LNO (Leverage, Neutral, Overhead) frameworks.

## Overview

This skill provides two complementary prioritization systems:
- **Strategic (DHM)**: Which features/initiatives should we pursue?
- **Tactical (LNO)**: How should I spend my time today?

**Based on**: Gibson Biddle (DHM/Glee frameworks) + Shreyas Doshi (LNO framework)

**Primary Use Cases**: Feature prioritization, roadmap planning, daily task management, initiative scoring.

## Core Functions

### 1. DHM Scoring (Strategic Prioritization)

Score every initiative on three dimensions.

**The DHM Framework:**
| Letter | Dimension | Question |
|--------|-----------|----------|
| **D** | Delight | Does this make customers love us more? |
| **H** | Hard to copy | Can competitors replicate this easily? |
| **M** | Margin | Does this improve our economics? |

**DHM Scoring Template:**
```
## Initiative: {Name}

### D: Delight (1-5)
Score: [ ]

Evidence:
- Customer problem solved: [From 05-problem.md]
- User benefit: [Specific improvement]
- Differentiation: [How it's better than alternatives]

Checklist:
□ Solves a top-3 customer problem?
□ Customers will notice and appreciate?
□ Differentiates from alternatives?
□ Can measure customer response?

### H: Hard to Copy (1-5)
Score: [ ]

Evidence:
- Defensibility source: [brand/network/tech/scale/switching]
- Time to copy: [X months for competitor]
- Builds on existing moat: [Yes/No - how]

Checklist:
□ Competitor could copy in < 6 months?
□ Builds on existing defensibility?
□ Creates new switching costs?
□ Leverages unique assets?

Sources of Defensibility:
- Brand: Trust, reputation (Years)
- Network effects: Value grows with users (Permanent)
- Unique technology: Proprietary innovation (Years)
- Economies of scale: Cost advantages (Permanent)
- Switching costs: Hard to leave (Years)

### M: Margin-Enhancing (1-5)
Score: [ ]

Evidence:
- Revenue impact: [+$X per user/month]
- Cost impact: [-$X per user/month]
- LTV impact: [+X% retention]

Checklist:
□ Increases willingness to pay?
□ Decreases our costs?
□ Attracts higher-value customers?
□ Improves retention (LTV)?
□ Reduces support burden?

### Total: [ /15]

### Recommendation:
[ ] Prioritize (12+)
[ ] Consider (9-11)
[ ] Deprioritize (<9)

### Rationale:
[Why this score, what makes it strategic or not]
```

### 2. Initiative Stack Rank

Compare multiple initiatives.

**Stack Rank Template:**
```
## Initiative Stack Rank

| Rank | Initiative | D | H | M | Total | Notes |
|------|------------|---|---|---|-------|-------|
| 1 | [Name] | 5 | 4 | 4 | 13 | High delight + defensible |
| 2 | [Name] | 4 | 5 | 3 | 12 | Strong moat |
| 3 | [Name] | 5 | 2 | 4 | 11 | Easy to copy (H=2) |
| 4 | [Name] | 3 | 3 | 3 | 9 | Consider only |
| 5 | [Name] | 4 | 2 | 2 | 8 | Deprioritize |

## Recommended Portfolio

### Prioritize (60% of effort)
1. [Initiative]: [Why - DHM rationale]
2. [Initiative]: [Why - DHM rationale]

### Consider (30% of effort)
3. [Initiative]: [Conditions to prioritize]

### Deprioritize (10% or defer)
4. [Initiative]: [Why not now]
5. [Initiative]: [Why not now]

## Allocation Check
- Strategic Bets: 30% [List]
- Incrementals: 60% [List]
- Infrastructure: 10% [List]
```

### 3. LNO Classification (Tactical Prioritization)

Classify every task before working on it.

**The LNO Framework:**
| Type | Definition | ROI | Approach |
|------|------------|-----|----------|
| **L** (Leverage) | 10-100x return | Massive | Perfectionist mode |
| **N** (Neutral) | 1x return | Linear | Good enough |
| **O** (Overhead) | <1x return | Negative | Minimum viable |

**Identifying L Tasks:**
L tasks are usually:
- Strategic (define direction)
- High-stakes (hard to undo)
- Force-multiplying (enable others)
- Scary (you're procrastinating on them)

**The Tell:** "I know I should work on this, but I don't have time" = probably L task.

**Common L Tasks:**
- Strategy documents
- Critical PRDs
- Cross-team alignment
- Key stakeholder conversations
- Important presentations

**LNO Classification Template:**
```
## Daily LNO Classification

### L Tasks (Leverage - Perfectionist Mode)
| Task | Why L | Peak Hours | Block Time |
|------|-------|------------|------------|
| [Task] | [10-100x impact because...] | [Time] | [Duration] |

### N Tasks (Neutral - Good Enough)
| Task | Time Limit | "Done" Looks Like |
|------|------------|-------------------|
| [Task] | [X hours] | [Minimum acceptable] |

### O Tasks (Overhead - Minimum Viable)
| Task | Batch With | Can Delegate? | Can Eliminate? |
|------|------------|---------------|----------------|
| [Task] | [Other O tasks] | [Yes/No] | [Yes/No] |

## Today's Schedule
- [ ] 9-11am: [L Task - peak energy]
- [ ] 11-12pm: [N Tasks batch]
- [ ] 12-1pm: [Break]
- [ ] 1-2pm: [L Task continued]
- [ ] 2-4pm: [N Tasks]
- [ ] 4-5pm: [O Tasks batch]
```

### 4. Same Activity, Different Classification

The same activity can be L, N, or O depending on context.

**Examples:**
| Activity | L Version | N Version | O Version |
|----------|-----------|-----------|-----------|
| Bug report | Critical bug affecting revenue | Normal bug | Minor edge case |
| Meeting notes | Strategic decision with CEO | Team sync | Status update |
| Email | Partnership proposal | Colleague question | Newsletter |
| Presentation | Board deck | Sprint review | Internal update |
| Document | Product strategy | Feature spec | Meeting notes |

**Before Starting Any Task:**
```
1. Ask: "Is this L, N, or O?"
2. Set effort level accordingly:
   - L: Block time, change location if needed, iterate
   - N: Set timer, define "good enough", ship
   - O: Batch with other O tasks, minimum viable
```

### 5. Glee Model (Long-Term Strategy)

Think in chapters for long-term prioritization.

**Glee Framework:**
| Letter | Phase | Question |
|--------|-------|----------|
| **G** | Get big | What will you first become known for? |
| **L** | Lead | What will you lead in the market? |
| **E** | Expand | How will you grow beyond the first thing? |

**Glee Planning Template:**
```
## Glee Chapters

### Chapter 1: Get Big On _______
Timeframe: Years 1-3

- What trend/wave are we riding?
- What will we become known for?
- What's our wedge into the market?

Current Priority: [Initiative aligned to this phase]

### Chapter 2: Lead _______
Timeframe: Years 4-6

- What will we lead in our category?
- What makes us the obvious choice?
- How do we compound our advantage?

Future Priority: [Initiative that sets this up]

### Chapter 3: Expand Into _______
Timeframe: Years 7-10

- What adjacent opportunities exist?
- How do we leverage what we've built?
- What's the next wave to catch?

Long-term Vision: [Where this leads]
```

### 6. Opportunity Cost Check

Stop optimizing for positive ROI, start minimizing opportunity cost.

**The ROI Trap:**
- ROI thinking: "Is this a good use of time?" → Fill with quick wins
- Opportunity cost: "Is this the BEST use of time?" → Transformative work

**Opportunity Cost Template:**
```
## Opportunity Cost Analysis

### Current Allocation
- Quick wins / Incrementals: [X]%
- Big bets / Strategic: [X]%
- Infrastructure / Stability: [X]%

### Recommended Allocation
- Incrementals: 60% (well-defined, positive ROI)
- Big bets: 30% (1-2 major initiatives)
- Infrastructure: 10%

### Biggest Opportunity We're NOT Pursuing
[What transformative thing are we avoiding?]

### Why We're Avoiding It
- [Reason 1]
- [Reason 2]

### What It Would Take
- [Requirement to pursue]
- [Tradeoff required]

### Decision
[ ] Pursue (reallocate from incrementals)
[ ] Defer (not right time, document why)
[ ] Decline (not aligned with Glee phase)
```

### 7. Pre-Mortem for Priorities

Before committing, imagine failure.

**Pre-Mortem Template:**
```
## Pre-Mortem: {Initiative}

### Prompt
"Imagine we prioritized this and it failed miserably in 6 months. Why?"

### Tigers (Real Threats)
- [Threat that could kill this]
- [Another real threat]

### Paper Tigers (Not Actually Worried)
- [Seeming threat we can handle]
- [Fear that's overblown]

### Elephants (Unspoken Issues)
- [Thing nobody's discussing]
- [Uncomfortable truth]

### Verdict
[ ] Proceed with mitigations
[ ] Deprioritize due to risks
[ ] Need more information

### If Proceeding - Mitigations
| Risk | Mitigation |
|------|------------|
| [Tiger 1] | [How to address] |
| [Tiger 2] | [How to address] |
```

## Workflows

### Quarterly Strategic Prioritization

```
1. Assess current Glee chapter
2. List all initiatives/features on table
3. Score each on DHM (1-5 per dimension)
4. Stack rank by total score
5. Apply allocation (60/30/10)
6. Run pre-mortem on top 3
7. Output: Prioritized roadmap
```

### Daily Tactical Prioritization

```
1. List all tasks for today
2. Classify each as L, N, or O
3. Identify today's main L task
4. Schedule L for peak energy hours
5. Batch O tasks together
6. Set time limits for N tasks
7. Output: Prioritized daily schedule
```

### Feature Request Evaluation

```
1. Receive feature request
2. Score on DHM framework
3. Compare to current initiatives
4. Check alignment with Glee phase
5. Run opportunity cost check
6. Output: Prioritize / Consider / Deprioritize
```

## Input Requirements

**Required:**
- List of initiatives or tasks to prioritize
- Context on business goals (from Canvas)

**Optional:**
- Current roadmap/backlog
- Competitive landscape (06-competitive.md)
- Resource constraints (02-constraints.md)

## Output Structure

```
Prioritization Output:
├── dhm_scores.md          # All initiatives scored
├── stack_rank.md          # Prioritized list
├── glee_assessment.md     # Strategic phase
├── daily_lno.md           # Tactical priorities
└── premortem/             # Risk analysis
    ├── initiative-1.md
    └── initiative-2.md
```

## Integration

**Receives from:**
- product-requirements - features to prioritize
- Canvas 05-problem - problem severity for D scoring
- Canvas 08-advantage - moats for H scoring
- Canvas 11-pricing - revenue for M scoring

**Provides to:**
- product-specification - which features to shape
- Engineering - what to build first
- Stakeholders - prioritization rationale

## Best Practices

### Strategic (DHM)
1. **Bonus for H**: Give extra credit to hard-to-copy ideas
2. **Evidence over opinion**: Link D scores to validated problems
3. **Quantify M**: Specific revenue/cost numbers
4. **Pre-mortem top picks**: Don't skip risk analysis

### Tactical (LNO)
1. **Classify before starting**: Never dive in without asking L/N/O
2. **One L at a time**: Only one task is truly highest leverage
3. **Batch O tasks**: Never do overhead one at a time
4. **Protect L time**: Peak hours for leverage work

### Avoiding Pitfalls
- Do NOT prioritize by customer loudness
- Do NOT stack rank without DHM scores
- Do NOT treat all tasks as equally important
- Do NOT fill time with only quick wins

## Key Principles

> "I give extra bonus points to the things that are hard to copy in the long term." — Gibson Biddle

> "The same type of activity can actually be either an L task or an N task or an O task." — Shreyas Doshi

> "Stop doing work that simply provides a positive return on investment and start focusing on work that minimizes opportunity cost." — Shreyas Doshi

> "When people come to me with ideas I just nicely ask them how can you help describe to me why that idea is on strategy." — Gibson Biddle

---

**Related Playbooks:**
- [product-prioritization](research/playbooks/product-prioritization.md)
