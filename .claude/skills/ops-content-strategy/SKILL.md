---
name: content-strategy
description: Active content discovery with loop-aware opportunity detection. Use when: searching communities for engagement opportunities, detecting campaign triggers from patterns, finding warm leads, evaluating content loop potential. Reads strategy from Canvas and distribution-model.md.
allowed-tools: "Read,Write,WebSearch,WebFetch,AskUserQuestion"
---
# Content Strategy: Discovery & Loop Opportunity Detection

Proactively find opportunities that generate loops, not just content.

## Core Principle

> "Funnels is an f-word. Loops are so much better."

Every opportunity evaluated for loop potential — can it generate its own next input?

## Context Loading

**Required:**
- `strategy/canvas/04-segments.md` — Target audience, where to find them
- `strategy/canvas/05-problem.md` — Problems we solve
- `strategy/canvas/07-uvp.md` — Value proposition
- `strategy/canvas/15-gtm.md` — Channels, search queries, constraints
- `artifacts/marketing/narrative/distribution-model.md` — Loop mechanics, channel strategy

If distribution-model.md missing → Flag "Run marketing-narrative first"

## Mode 1: Active Discovery

1. Read search queries from `15-gtm.md`
2. Read segment locations from `04-segments.md`
3. Read channel priorities from `distribution-model.md`
4. Execute searches across configured platforms
5. Score by loop potential (not just relevance)
6. Flag actionable items in `ops/today.md`

**Prioritize channels from distribution-model.md** — invest where distribution physics work.

## Mode 2: Loop Opportunity Detection

Scan for triggers that fuel content loops:

| Trigger Source | Loop Opportunity |
|----------------|------------------|
| User implements our method | Feature their before/after |
| Community question answered | Expand to article, cite questioner |
| Client success documented | Case study → social proof → more clients |
| Strategic insight validated | Thought leadership → authority → inbound |
| Someone shares our content | Engage, amplify, strengthen relationship |

**User-generated content is loop fuel.** Prioritize opportunities to amplify others.

## Opportunity Scoring (Loop-Aware)
```
Impact = (Loop Potential × Velocity Story × Audience Alignment) / 3
```

### Loop Potential
| Score | Criteria |
|-------|----------|
| 1.0 | Explicitly generates user response/implementation |
| 0.8 | High probability of sharing/engagement |
| 0.6 | Could trigger loop if executed well |
| 0.4 | Standalone value, weak loop |
| 0.2 | Pure broadcast, no loop possible |

### Velocity Story
| Score | Criteria |
|-------|----------|
| 1.0 | Clear before → after with time compression |
| 0.7 | Transformation story without time element |
| 0.4 | Insight without transformation |
| 0.2 | Information only |

### Audience Alignment
| Score | Criteria |
|-------|----------|
| 1.0 | Exact target segment problem |
| 0.7 | Adjacent segment or problem |
| 0.4 | General audience relevance |
| 0.2 | Tangential connection |

**Thresholds:**
- ≥0.7: Flag immediately — high loop potential
- 0.5-0.7: Add to backlog
- <0.5: Skip unless strategic (or no loop = no priority)

## Output Format
```markdown
## Discovery Results - {date}

### Loop Opportunities (Priority)
| Source | Opportunity | Loop Mechanic | Score | Action |
|--------|-------------|---------------|-------|--------|
| {where} | {what} | {how it loops} | {score} | {next step} |

### User-Generated Loop Fuel
| User | Content | Amplification Action |
|------|---------|---------------------|
| {who} | {what they shared/implemented} | {how to amplify} |

### Questions to Answer
| Platform | Question | Loop Potential | Action |
|----------|----------|----------------|--------|
| {platform} | "{question}" | {can answer generate follow-up?} | {action} |
```

## Content Triggers (When to Create)

**Create when:**
- User success story available (loop fuel)
- Genuine learning occurred (from threads)
- Velocity story to tell (shipped fast)
- Community question has loop potential
- Strategic insight worth sharing

**Don't create:**
- Calendar says so
- Engagement bait without substance
- Content without loop potential
- Regurgitated advice

## Boundaries

**DO:**
- Search communities for loop opportunities
- Detect user-generated content to amplify
- Score by loop potential
- Flag opportunities in ops/today.md
- Prioritize distribution-model.md channels

**DON'T:**
- Prioritize SEO-first opportunities (dying channel)
- Recommend content without loop trigger
- Create for calendar, not learning
- Ignore user-generated loop fuel

## Handoff to Execution

When opportunity approved:
1. Create thread: `threads/marketing/campaigns/{slug}/`
2. Complete stages 1-4 (input → hypothesis → implication → decision)
3. 4-decision.md triggers marketing-execution