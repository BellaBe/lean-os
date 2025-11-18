# System Architecture

LeanOS operates in 4 layers: Strategy → Skills → Threads → Operations Dashboard.

## Architecture Diagram

```text
┌──────────────────────────────────────────────────────────────────────────────────────────────┐
│ STRATEGY LAYER                                                                               │
│ Source of Truth: Lean Canvas (15 living documents)                                           │
│ Location: strategy/canvas/                                                                   │
└──────────────────────────────────────────────────────────────────────────────────────────────┘
                                          ↓
┌──────────────────────────────────────────────────────────────────────────────────────────────┐
│ SKILLS LAYER (AI Execution)                                                                  │
│                                                                                              │
│ Foundation Builder (Pre-Launch Orchestration):                                               │
│ ├─ foundation-builder: Orchestrate 10 agents for Canvas population and validation            │
│ │                                                                                            │
│ │  Core Agents (7):                                                                          │
│ │  ├─ market-intelligence: Market analysis, competitive landscape, TAM/SAM/SOM               │
│ │  │                       → Canvas 01-04, 06                                                │
│ │  ├─ problem-solution-fit: Problem validation, solution design, MVP definition              │
│ │  │                         → Canvas 05, 09, 10                                             │
│ │  ├─ value-proposition: Unique value articulation, positioning, messaging                   │
│ │  │                     → Canvas 07-08                                                      │
│ │  ├─ business-model: Revenue design, pricing, unit economics, cost structure                │
│ │  │                   → Canvas 11-13                                                        │
│ │  ├─ validation: Assumption testing, experiment design, hypothesis validation               │
│ │  │              → Canvas 10 (validation status)                                            │
│ │  ├─ go-to-market: Channel strategy, launch planning, growth tactics                        │
│ │  │                → Canvas 14-15                                                           │
│ │  └─ execution: Task orchestration, daily operations within subscription budget             │
│ │                                                                                            │
│ │  Specialist Agents (3, on-demand):                                                         │
│ │  ├─ funding: Fundraising strategy, pitch development, investor targeting                   │
│ │  ├─ regulatory: Compliance requirements, licensing, regulated market entry                 │
│ │  └─ retention-optimizer: Cohort analysis, churn prediction, optimization                   │
│ │                                                                                            │
│ │  Lifecycle: Discovery → Definition → Validation → Execution → Launch → Archive             │
│                                                                                              │
│ Sales Strategy Skills:                                                                       │
│ ├─ icp-generator: Define target customers (per segment)                                      │
│ └─ sales-narrative: Create messaging (per segment)                                           │
│                                                                                              │
│ Sales Execution Skills:                                                                      │
│ ├─ sales-execution: Generate materials, find prospects                                       │
│ │  ├─ materials-generation: Pitch decks, scripts, emails                                     │
│ │  ├─ prospect-research: Find target companies                                               │
│ │  ├─ contact-finding: Find decision-makers                                                  │
│ │  ├─ outreach-sequencing: Email/phone cadences                                              │
│ │  └─ qualification-support: Discovery call prep                                             │
│                                                                                              │
│ Marketing Strategy Skills:                                                                   │
│ └─ marketing-narrative: Define content strategy                                              │
│    ├─ content-pillars.md: 3-5 strategic themes                                               │
│    ├─ seo-strategy.md: Keywords by funnel stage                                              │
│    ├─ brand-voice.md: Educational, non-promotional                                           │
│    └─ channel-guidelines.md: Format specs per channel                                        │
│                                                                                              │
│ Marketing Execution Skills:                                                                  │
│ └─ marketing-execution: Orchestrate content workflow                                         │
│    ├─ content-strategy: Identify opportunities from threads                                  │
│    ├─ content-generation: Create educational drafts                                          │
│    ├─ seo-optimization: Apply keywords naturally                                             │
│    ├─ content-distribution: Publish multi-channel                                            │
│    └─ performance-tracking: Measure impact, feed insights                                    │
│                                                                                              │
│ Orchestration (Evidence-Based Decision Flow):                                                │
│ ├─ causal-flow: 6-stage decision orchestrator for business, sales, and marketing threads     │
│ │                                                                                            │
│ │  6-Stage Flow:                                                                             │
│ │  Input → Hypothesis → Implication → Decision → Actions → Learning                          │
│ │                                                                                            │
│ │  Stage Skills (6):                                                                         │
│ │  ├─ causal-flow-input: Capture factual observations (not opinions)                         │
│ │  ├─ causal-flow-hypothesis: Challenge/validate Canvas assumptions                          │
│ │  │                           → Links to 10-assumptions.md                                  │
│ │  ├─ causal-flow-implication: Analyze business impact with numbers                          │
│ │  │                            (ROI, cost, timeline, risk)                                  │
│ │  ├─ causal-flow-decision: Official commitment, document alternatives considered            │
│ │  ├─ causal-flow-actions: Break into executable tasks (typed for sales/marketing)           │
│ │  └─ causal-flow-learning: Validate hypothesis, update Canvas automatically                 │
│ │                                                                                            │
│ │  Resources:                                                                                │
│ │  ├─ actions/templates/: Sales & marketing action templates                                 │
│ │  │                       (lead-intake, qualify, demo, pilot, close,                        │
│ │  │                        research, create, publish, promote, measure)                     │
│ │  └─ reference/: Thread architecture docs (business, sales, marketing threads)              │
│ │                                                                                            │
│ │  Thread Types: business/, sales/, marketing/                                               │
│ │  Key Feature: Stage 6 auto-updates Canvas from learning                                    │
│                                                                                              │
│ Operations Dashboard:                                                                        │
│ └─ ops-dashboard: Auto-generate daily ops/ dashboards                                        │
│                   (today.md, velocity.md, patterns.md, changes.md) from thread data          │
│                   → Pattern detection for meta-learning                                      │
│                                                                                              │
└──────────────────────────────────────────────────────────────────────────────────────────────┘
                                          ↓
┌──────────────────────────────────────────────────────────────────────────────────────────────┐
│ THREADS LAYER (Decision Storage)                                                             │
│ Complete decision narratives with causal flow                                                │
│ Location: threads/{type}/{thread-name}/                                                      │
│                                                                                              │
│ Thread Types:                                                                                │
│ ├─ business/: Strategic decisions                                                            │
│ ├─ sales/: Deal pipeline management                                                          │
│ │   ├─ campaigns/: Outbound prospecting (YYYY-MM-DD-name)                                    │
│ │   └─ {company-name}/: Individual deal threads                                              │
│ └─ marketing/: Content execution                                                             │
│     ├─ narrative/{product}/: Content strategy                                                │
│     └─ content/{topic}/: Individual content pieces                                           │
└──────────────────────────────────────────────────────────────────────────────────────────────┘
                                          ↓
┌──────────────────────────────────────────────────────────────────────────────────────────────┐
│ OPS DASHBOARD (Daily Interface)                                                              │
│ Auto-generated from thread data                                                              │
│ Location: ops/                                                                               │
│                                                                                              │
│ ├─ today.md: Bella's 5-min daily review                                                      │
│ ├─ velocity.md: Throughput analysis                                                          │
│ ├─ patterns.md: Detected anomalies                                                           │
│ └─ changes.md: Strategic flags for review                                                    │
└──────────────────────────────────────────────────────────────────────────────────────────────┘
```

## Layer 1: Strategy (Source of Truth)

**Location:** `strategy/canvas/`

**Contents:** 15 living Lean Canvas documents

**Purpose:** Single source of truth for all business decisions

**Key files:**
- 01-context.md - KBOS framework (Known, Believed, Objective, Subjective)
- 02-constraints.md - Budget, time, resource limits
- 03-opportunity.md - Market size, timing, trends
- 04-segments.md - Customer segments with observable filters
- 05-problem.md - Top 3 problems, existing alternatives
- 06-competitive.md - Competitive landscape, positioning gaps
- 07-uvp.md - Unique Value Proposition (single sentence)
- 08-advantage.md - Unfair advantages, secret sauce
- 09-solution.md - MVP feature set, solution approach
- 10-assumptions.md - Hypotheses, validation status, confidence levels
- 11-pricing.md - Revenue model, pricing tiers
- 12-costs.md - Cost structure, burn rate
- 13-metrics.md - Key metrics, unit economics
- 14-growth.md - Growth channels, acquisition tactics
- 15-gtm.md - Go-to-market strategy, launch plan

**Updates:** Automatically updated by Stage 6 (Learning) in threads

## Layer 2: Skills (AI Execution)

**Location:** `.claude/skills/`

**Purpose:** AI agents that execute operations autonomously

**Categories:**

### Foundation Builder
- Orchestrates 10 agents for Canvas population
- Phases: Discovery → Definition → Validation → Execution → Launch

### Sales Skills
- **Strategy:** icp-generator, sales-narrative
- **Execution:** materials-generation, prospect-research, contact-finding, outreach-sequencing, qualification-support

### Marketing Skills
- **Strategy:** marketing-narrative (content pillars, SEO, voice, channels)
- **Execution:** content-strategy, content-generation, seo-optimization, content-distribution, performance-tracking

### Orchestration Skills
- **causal-flow:** 6-stage decision framework (Input → Hypothesis → Implication → Decision → Actions → Learning)
- **ops-dashboard:** Auto-generate daily interface

### Engineering Skills
- **category-theoretic-system-design:** Compositional system design
- **standardization-layer:** Uniform cross-cutting concerns

## Layer 3: Threads (Decision Storage)

**Location:** `threads/{type}/{name}/`

**Purpose:** Store complete decision narratives with 6-stage causal flow

**Thread types:**

### Business Threads
- Strategic decisions affecting multiple segments
- Canvas updates
- Process improvements

### Sales Threads
- **Campaigns:** Outbound prospecting (`campaigns/YYYY-MM-DD-name/`)
- **Deals:** Individual deal progression (`{company-name}/`)
- 6-stage flow: Input → Hypothesis → Implication → Decision → Actions → Learning

### Marketing Threads
- **Narratives:** Content strategy (`narrative/{product}/`)
- **Campaigns:** Campaign execution (`campaigns/{campaign-slug}/`)
- **Content:** Individual pieces (`content/{topic}/`)
- 6-stage flow with content-specific actions

**Thread structure:**
```
threads/{type}/{name}/
├── metadata.yaml
├── 1-input.md
├── 2-hypothesis.md
├── 3-implication.md
├── 4-decision.md
├── 5-actions.md (or 5-actions/ directory)
└── 6-learning.md
```

## Layer 4: Operations Dashboard

**Location:** `ops/`

**Purpose:** Human touchpoint - single daily review interface

**Auto-generated files:**

### today.md
- High-priority items requiring human approval
- Decisions made by AI (last 24h)
- Active operations summary
- Performance alerts
- Anomalies detected

### velocity.md
- Throughput metrics per stage
- Cycle time analysis
- Bottleneck identification

### patterns.md
- Cross-thread pattern detection
- Anomaly flagging
- Meta-learning insights

### changes.md
- Strategic flags requiring review
- Canvas section updates
- Assumption validation status changes

## Supporting Directories

### research/customer/
- **icp/:** ICP definitions per segment
- **prospects/:** Prospect and contact lists

### artifacts/
- **sales/:** Sales materials per segment (pitch decks, scripts, templates)
- **marketing/:** Published content (blog, LinkedIn, email)
- **fundraising/:** Pitch decks, financial models

### engineering/
- **services/:** Technical specs (active development)
- **standards/:** Architecture patterns
- **domain/:** Business logic documentation

## Data Flow

**Typical decision flow:**

1. **Input captured** (Stage 1) → Thread created
2. **Hypothesis formed** (Stage 2) → Links to Canvas assumptions
3. **Implications analyzed** (Stage 3) → Business impact quantified
4. **Decision made** (Stage 4) → Official commitment recorded
5. **Actions executed** (Stage 5) → AI handles autonomously
6. **Learning captured** (Stage 6) → Canvas auto-updated
7. **Dashboard reflects** → ops/today.md shows result
8. **Next decision triggered** → Pattern detected, new thread started

**Closed-loop example:**

Sales thread → Learning (Stage 6) → Canvas updated → Marketing scans threads → Content opportunity detected → Marketing thread created → Content published → SEO drives traffic → Demos requested → Sales threads created → Learning captured → Loop continues

## Next Steps

- Learn the complete flow: [How It Works](how-it-works.md)
- Understand Canvas setup: [Canvas Setup](../foundation/canvas-setup.md)
- See timeline breakdown: [Timeline Guide](../foundation/timeline.md)