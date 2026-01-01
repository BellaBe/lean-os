# Marketing Workflow

Marketing is **motion-aware, not calendar-driven**. Content adapts to your GTM strategy. Execution adapts to motion.

## Goal Integration

Marketing activities execute brand goals. A brand goal spawns marketing threads:

```
Goal: "Build LinkedIn Presence"
  └── Subgoal: "Establish posting cadence"
        └── Thread: threads/marketing/campaigns/q4-content/ (goal-linked)
```

**Agent:** `marketing-execution` orchestrates marketing skills
**Skills:** `marketing-content-generation`, `marketing-content-delivery`, `marketing-channel-optimization`

**Reasoning mode:** Causal (enforced) - all marketing threads use 6-stage causal flow.
**When to use other modes:**
- Abductive: "Why did this campaign underperform?" → diagnose root cause
- Inductive: "Case studies always outperform guides" → detect pattern, update strategy
- Analogical: "This launch is like our marketplace launch" → adapt playbook
- Counterfactual: "Should we have launched on LinkedIn instead?" → inform future decisions

## Core Principles

> "Great product is not enough. Distribution wins."
> "Execution adapts to motion."

- GTM motion determines content mode (loop/marketplace/sales)
- Single source of truth: `strategy/canvas/15.go-to-market.md`
- Orchestrator detects mode, subskills receive it
- Identity (narrative) is channel-agnostic; distribution is motion-specific

---

## Skills Overview

```
.claude/skills/
├── foundations-go-to-market/           # Produces GTM strategy
├── marketing-narrative/    # Brand identity (channel-agnostic)
├── marketing-content-strategy/               # Opportunity detection (motion-aware)
├── marketing-content-generation/       # Create content (receives mode)
├── marketing-content-delivery/         # Publish + track (receives mode)
└── marketing-channel-optimization/     # Optimize channels

.claude/agents/
└── marketing-execution.md              # Orchestrator (routes to skills)
```

| Skill | Purpose | Reads GTM? | Detects Mode? |
|-------|---------|------------|---------------|
| **foundations-go-to-market** | Generate GTM strategy | Produces it | N/A |
| **marketing-narrative** | Brand identity, voice, patterns | No | No |
| **marketing-content-strategy** | Find opportunities | Yes | Yes (for scoring) |
| **marketing-execution (agent)** | Orchestrate campaigns | Yes | **Yes (single source)** |
| **marketing-content-generation** | Create content | No | No (receives mode) |
| **marketing-content-delivery** | Publish + track | No | No (receives mode) |
| **marketing-channel-optimization** | Optimize channels | Yes (channels only) | No |

---

## Phase 1: GTM Strategy (Once Per Product)

### Generate GTM Strategy
```
Skill: foundations-go-to-market
Input: Canvas (segments, problem, UVP, solution, pricing)
Output: strategy/canvas/15.gtm.md
```

**GTM file declares:**
- Motion type (PLG, Content-Led, Partner-Led, SLG, Hybrid)
- Stage (Pre-launch, Launch, Growth, Scale)
- Channels with investment levels
- Growth loops

**All downstream skills read this file.**

---

## Phase 2: Marketing Narrative (Once Per Product)

### Generate Brand Identity
```
Skill: marketing-narrative
Input: Canvas (segments, problem, UVP, advantage, solution)
Output: artifacts/marketing/narrative/
  ├── brand-voice.md
  ├── positioning.md
  ├── content-pillars.md
  └── patterns/
      ├── insight.md
      ├── tutorial.md
      ├── case-study.md
      └── story.md
```

**Narrative defines identity only:**
- How we sound (brand voice)
- What we stand for (positioning)
- What we talk about (pillars)
- How content is structured (patterns)

**Narrative does NOT define:**
- Which channels to use (→ GTM)
- How to optimize channels (→ channel-optimization)
- Loop mechanics (→ content-generation)

---

## Phase 3: Content Discovery (Continuous)

### Opportunity Detection
```
Skill: marketing-content-strategy
Reads: 15.gtm.md + narrative/content-pillars.md
```

**Motion determines scoring:**

| Motion | Scoring Formula |
|--------|-----------------|
| Loop-Driven (PLG, Content-Led) | (Loop Potential × Velocity Story × Audience Alignment) / 3 |
| Marketplace-Driven (Partner-Led) | (Review Potential × Install Impact × Retention Value) / 3 |
| Sales-Driven (SLG) | (Deal Enablement × Objection Coverage × Stage Fit) / 3 |

**Thresholds:**
- ≥0.7: Recommend thread creation (goal-linked if brand goal exists)
- 0.5-0.7: Add to backlog
- <0.5: Skip

---

## Phase 4: Content Execution (Thread-Driven)

### Marketing Campaign Thread
```
threads/marketing/campaigns/{slug}/
├── 1-input.md (trigger)
├── 2-hypothesis.md (expected outcome)
├── 3-implication.md (success definition)
├── 4-decision.md (content plan with motion-appropriate design)
├── 5-actions/
│   ├── execution-log.md
│   └── drafts/
└── 6-learning.md
```

### Stage 5: Execution
```
Agent: marketing-execution
Reads: strategy/canvas/15.gtm.md
Determines: mode (loop-driven | marketplace-driven | sales-driven)
Invokes: skills with mode parameter
```

**Composition pattern:**
```
marketing-execution (agent)
├── Reads: 15.gtm.md
├── Detects: motion → mode (ONLY HERE)
├── Passes: mode to all skills
│
├── marketing-content-generation
│   └── Input: mode (required)
│   └── Does NOT read GTM
│
├── marketing-content-delivery
│   └── Input: mode (required)
│   └── Does NOT read GTM
│
└── marketing-channel-optimization
    └── Reads: channels from GTM
    └── Activates: relevant modules
```

---

## Workflows by Mode

### Loop-Driven (PLG, Content-Led)

| Step | Action | Subskill | Human |
|------|--------|----------|-------|
| 1 | Read 4-decision.md | — | — |
| 2 | Generate drafts with loop triggers | content-generation | — |
| 3 | Validate loop trigger + velocity | — | — |
| 4 | Flag for review | — | Review |
| 5 | Format for channels | content-delivery | — |
| 6 | Flag "Ready to publish" | — | Publish |
| 7 | Post first-comment (LinkedIn) | — | Post |
| 8 | Confirm published, add URLs | — | Confirm |
| 9 | Delete drafts | — | — |
| 10 | Start loop tracking | content-delivery | — |

**4-decision.md must include:**
- Loop trigger type (implementation/question/challenge/offer)
- Velocity proof (before → after)
- First-comment text

**Tracking schedule:**
- Day 1: First-comment engagement
- Day 3: Initial loop activations
- Day 7: Loop performance report
- Day 14: UGC detection
- Day 30: Final assessment

**Metrics:**
| Track | Ignore |
|-------|--------|
| Shares | Impressions |
| Implementations | Likes |
| Inbound DMs | Followers |
| User-generated content | Page views |

### Marketplace-Driven (Partner-Led)

| Step | Action | Subskill | Human |
|------|--------|----------|-------|
| 1 | Read 4-decision.md | — | — |
| 2 | Generate marketplace content | content-generation | — |
| 3 | Validate platform guidelines | — | — |
| 4 | Flag for review | — | Review |
| 5 | Optimize listing | channel-optimization | — |
| 6 | Flag "Ready to publish" | — | Publish |
| 7 | Update listing/publish support | — | Update |
| 8 | Start marketplace tracking | content-delivery | — |

**4-decision.md must include:**
- Content type (listing/changelog/support/review-prompt)
- Platform (Shopify/Chrome/etc)
- Keywords

**Metrics:**
| Track | Ignore |
|-------|--------|
| Install velocity | Page views |
| Rating average | Social shares |
| Review count | Likes |
| Keyword rankings | |
| Uninstall rate | |

### Sales-Driven (SLG)

| Step | Action | Subskill | Human |
|------|--------|----------|-------|
| 1 | Read 4-decision.md | — | — |
| 2 | Generate sales content | content-generation | — |
| 3 | Validate ROI/objections | — | — |
| 4 | Flag for review | — | Review |
| 5 | Format for sales portal | content-delivery | — |
| 6 | Flag "Ready to publish" | — | Publish |
| 7 | Upload, notify sales | — | Upload |
| 8 | Start usage tracking | content-delivery | — |

**4-decision.md must include:**
- Content type (case-study/one-pager/battle-card/sequence)
- Target persona (user/champion/decision-maker/finance)
- Sales stage (awareness/consideration/decision)
- Key objections addressed

**Metrics:**
| Track | Ignore |
|-------|--------|
| Content used in deals | Downloads |
| Pipeline influenced | Page views |
| Deals closed with content | Social shares |
| Sales feedback | |

---

## Motion → Mode Mapping

| GTM Motion | Content Mode | Rationale |
|------------|--------------|-----------|
| PLG | loop-driven | Product virality needs content loops |
| Content-Led | loop-driven | Authority building needs content loops |
| Partner-Led | marketplace-driven | Platform mechanics dominate |
| SLG | sales-driven | Sales enablement dominates |
| Hybrid | hybrid | Per-segment mode selection |

---

## Skills

### marketing-content-generation
- **Input:** mode, campaign_slug, decision_path, piece_name
- **Reads:** brand-voice.md, positioning.md, patterns/
- **Output:** Drafts with mode-appropriate structure
- **Modes:**
  - loop-driven: Loop triggers, velocity framing
  - marketplace-driven: Platform-optimized copy
  - sales-driven: ROI focus, objection handling

### marketing-content-delivery
- **Input:** mode, drafts_path, campaign_slug, channels
- **Reads:** Nothing (receives mode)
- **Output:** Channel-formatted files, tracking initiated
- **Modes:**
  - loop-driven: Shares, DMs, UGC tracking
  - marketplace-driven: Installs, reviews, rankings
  - sales-driven: Usage in deals, pipeline attribution

### marketing-channel-optimization
- **Reads:** channels from 11.channels.md
- **Activates:** Relevant modules (app-store, seo, linkedin, sales)
- **Used:** When channel needs improvement (not per-campaign)

---

## Closed-Loop Attribution

```
Sales/Business thread completes Stage 6
    ↓
marketing-content-strategy detects opportunity (motion-aware scoring)
    ↓
Human approves (or auto if goal autonomy allows)
    ↓
Marketing thread created (goal-linked if brand goal exists)
    ↓
marketing-execution agent invoked
    ↓
Agent detects mode from 15.gtm.md
    ↓
Skills invoked with mode parameter
    ↓
Content published, mode-appropriate tracking
    ↓
Performance fed back to 6-learning.md
    ↓
Goal state updated (if goal-linked)
    ↓
Loop continues
```

---

## Success Definition

**Success = motion-appropriate metrics, not content published.**

- Loop-driven: Loops activated (shares, implementations, UGC)
- Marketplace-driven: Store performance (installs, ratings, rankings)
- Sales-driven: Pipeline impact (content in deals, revenue influenced)

---

## Next Steps

- Learn sales workflow: [Sales Workflow](sales-workflow.md)
- Understand 6-stage flow: [Causal Flow](causal-flow.md)
- See daily routine: [Daily Routine](daily-routine.md)