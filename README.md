# LeanOS: AI-Native Operating System for Startups - Operated by Claude AI

**Status:** Active Development
**Version:** 1.0 (Marketing Layer Complete)
**Last Updated:** 2024-11-16

## What is LeanOS?

LeanOS is an AI-native operating system designed to run a company with minimal human intervention. Initially built for GlamYouUp (AI fashion recommendations SaaS), it automates 95%+ of operational decisions while maintaining strategic human oversight.

## The Problem It Solves

Traditional startups face:

- **Founder bottleneck:** Every decision requires human input
- **Information fragmentation:** Data scattered across Notion, Slack, email, docs
- **Context switching:** 20+ switches per day destroying productivity
- **No clear priorities:** "What needs my attention NOW?" is unclear

## The LeanOS Solution

- AI agents process 95%+ of decisions autonomously
- Single source of truth: Lean Canvas + thread-based decision storage
- Human focuses on high-leverage activities: <30 min/day on operations
- Company scales without linear human scaling

## Core Principles

- **AI-first execution:** Claude skills handle operations, not just documentation
- **Context-shaping over generalization:** Each skill targets specific decision types
- **Zero redundancy:** Information exists in ONE location only
- **Evidence-based decisions:** All choices trace to Canvas assumptions or thread results
- **Human touchpoint:** ops/today.md - Single daily entry point (auto-generated)
- **Learning-driven content:** Marketing creates content when business generates insights


## System Architecture

```text
┌─────────────────────────────────────────────────────────────┐
│ STRATEGY LAYER                                              │
│ Source of Truth: Lean Canvas (15 living documents)          │
│ Location: strategy/canvas/                                  │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│ SKILLS LAYER (AI Execution)                                 │
│                                                             │
│ Foundation Builder (Pre-Launch Orchestration):              │
│ ├─ foundation-builder: Orchestrate 10 agents for Canvas    │
│ │                      population and validation            │
│ │                                                           │
│ │  Core Agents (7):                                         │
│ │  ├─ market-intelligence: Market analysis, competitive    │
│ │  │                       landscape, TAM/SAM/SOM          │
│ │  │                       → Canvas 01-04, 06              │
│ │  ├─ problem-solution-fit: Problem validation, solution   │
│ │  │                         design, MVP definition        │
│ │  │                         → Canvas 05, 09, 10           │
│ │  ├─ value-proposition: Unique value articulation,        │
│ │  │                     positioning, messaging            │
│ │  │                     → Canvas 07-08                    │
│ │  ├─ business-model: Revenue design, pricing, unit        │
│ │  │                   economics, cost structure           │
│ │  │                   → Canvas 11-13                      │
│ │  ├─ validation: Assumption testing, experiment design,   │
│ │  │              hypothesis validation                    │
│ │  │              → Canvas 10 (validation status)          │
│ │  ├─ go-to-market: Channel strategy, launch planning,     │
│ │  │                growth tactics                         │
│ │  │                → Canvas 14-15                         │
│ │  └─ execution: Task orchestration, daily operations      │
│ │                 within subscription budget               │
│ │                                                          │
│ │  Specialist Agents (3, on-demand):                       │
│ │  ├─ funding: Fundraising strategy, pitch development,    │
│ │  │           investor targeting                          │
│ │  ├─ regulatory: Compliance requirements, licensing,      │
│ │  │             regulated market entry                    │
│ │  └─ retention-optimizer: Cohort analysis, churn          │
│ │                          prediction, optimization        │
│ │                                                          │
│ │  Lifecycle: Discovery → Definition → Validation →        │
│ │             Execution → Launch → Archive when complete   │
│                                                            │
│ Sales Strategy Skills:                                     │
│ ├─ icp-generator: Define target customers (per segment)    │
│ └─ sales-narrative: Create messaging (per segment)         │
│                                                            │
│ Sales Execution Skills:                                     │
│ ├─ sales-execution: Generate materials, find prospects      │
│ │  ├─ materials-generation: Pitch decks, scripts, emails    │
│ │  ├─ prospect-research: Find target companies              │
│ │  ├─ contact-finding: Find decision-makers                 │
│ │  ├─ outreach-sequencing: Email/phone cadences             │
│ │  └─ qualification-support: Discovery call prep            │
│                                                             │
│ Marketing Strategy Skills:                                  │
│ └─ marketing-narrative: Define content strategy             │
│    ├─ content-pillars.md: 3-5 strategic themes              │
│    ├─ seo-strategy.md: Keywords by funnel stage             │
│    ├─ brand-voice.md: Educational, non-promotional          │
│    └─ channel-guidelines.md: Format specs per channel       │
│                                                             │
│ Marketing Execution Skills:                                 │
│ └─ marketing-execution: Orchestrate content workflow        │
│    ├─ content-strategy: Identify opportunities from threads │
│    ├─ content-generation: Create educational drafts         │
│    ├─ seo-optimization: Apply keywords naturally            │
│    ├─ content-distribution: Publish multi-channel           │
│    └─ performance-tracking: Measure impact, feed insights   │
│                                                             │
│ Orchestration (Evidence-Based Decision Flow):               │
│ ├─ causal-flow: 6-stage decision orchestrator for          │
│ │                business, sales, and marketing threads     │
│ │                                                           │
│ │  6-Stage Flow:                                            │
│ │  Input → Hypothesis → Implication → Decision →           │
│ │          Actions → Learning                              │
│ │                                                           │
│ │  Stage Skills (6):                                        │
│ │  ├─ causal-flow-input: Capture factual observations      │
│ │  │                      (not opinions)                    │
│ │  ├─ causal-flow-hypothesis: Challenge/validate Canvas    │
│ │  │                           assumptions                  │
│ │  │                           → Links to 10-assumptions.md│
│ │  ├─ causal-flow-implication: Analyze business impact     │
│ │  │                            with numbers (ROI, cost,   │
│ │  │                            timeline, risk)            │
│ │  ├─ causal-flow-decision: Official commitment, document  │
│ │  │                         alternatives considered       │
│ │  ├─ causal-flow-actions: Break into executable tasks     │
│ │  │                        (typed for sales/marketing)    │
│ │  └─ causal-flow-learning: Validate hypothesis, update    │
│ │                           Canvas automatically           │
│ │                                                           │
│ │  Resources:                                               │
│ │  ├─ actions/templates/: Sales & marketing action         │
│ │  │                       templates (lead-intake,         │
│ │  │                       qualify, demo, pilot, close,    │
│ │  │                       research, create, publish,      │
│ │  │                       promote, measure)               │
│ │  └─ reference/: Thread architecture docs                 │
│ │                 (business, sales, marketing threads)     │
│ │                                                           │
│ │  Thread Types: business/, sales/, marketing/             │
│ │  Key Feature: Stage 6 auto-updates Canvas from learning  │
│                                                             │
│ Operations Dashboard:                                       │
│ └─ ops-dashboard: Auto-generate daily ops/ dashboards      │
│                   (today.md, velocity.md, patterns.md,     │
│                   changes.md) from thread data             │
│                   → Pattern detection for meta-learning    │
│                                                             │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│ THREADS LAYER (Decision Storage)                            │
│ Complete decision narratives with causal flow               │
│ Location: threads/{type}/{thread-name}/                     │
│                                                             │
│ Thread Types:                                               │
│ ├─ business/: Strategic decisions                          │
│ ├─ sales/: Deal pipeline management                        │
│ │   ├─ campaigns/: Outbound prospecting (YYYY-MM-DD-name)  │
│ │   └─ {company-name}/: Individual deal threads            │
│ └─ marketing/: Content execution                           │
│     ├─ narrative/{product}/: Content strategy              │
│     └─ content/{topic}/: Individual content pieces         │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│ OPS DASHBOARD (Daily Interface)                             │
│ Auto-generated from thread data                             │
│ Location: ops/                                              │
│                                                             │
│ ├─ today.md: Bella's 5-min daily review                    │
│ ├─ velocity.md: Throughput analysis                        │
│ ├─ patterns.md: Detected anomalies                         │
│ └─ changes.md: Strategic flags for review                  │
└─────────────────────────────────────────────────────────────┘
```

## Directory Structure

```text
lean-os/
├── strategy/
│   ├── canvas/                      # Lean Canvas (15 files) = SOURCE OF TRUTH
│   │   ├── 01-context.md
│   │   ├── 04-segments.md           # Customer segments
│   │   ├── 10-assumptions.md        # Tracked hypotheses
│   │   └── ...
│   └── financials/                  # Financial models
│
├── threads/                         # Thread-based decision storage
│   ├── business/{name}/             # Strategic decisions
│   ├── sales/
│   │   ├── campaigns/               # Outbound prospecting campaigns
│   │   │   └── YYYY-MM-DD-{name}/   # Date-prefixed campaigns
│   │   │       ├── 1-input.md
│   │   │       ├── 2-hypothesis.md
│   │   │       ├── 3-implication.md
│   │   │       ├── 4-decision.md
│   │   │       ├── 5-actions.md
│   │   │       └── 6-learning.md
│   │   └── {company-name}/          # Individual deal threads
│   │       ├── 1-input.md
│   │       └── ... (6-stage flow)
│   └── marketing/
│       └── campaigns/{campaign-slug}/  # Campaign execution threads
│           ├── metadata.yaml
│           ├── 1-input.md
│           ├── 2-hypothesis.md
│           ├── 3-implication.md
│           ├── 4-decision.md       # Content plan
│           ├── 5-actions/
│           │   ├── execution-log.md
│           │   └── drafts/         # Temp, deleted after publishing
│           └── 6-learning.md       # Campaign results
│
├── research/
│   └── customer/                    # Customer research
│       ├── icp/                     # ICP definitions per segment
│       │   ├── {segment}-icp.md
│       │   └── {segment}-qualification.md
│       └── prospects/               # Prospect & contact lists
│           ├── {segment}-prospects.md
│           ├── {segment}-prospects-{date}.csv
│           └── {segment}-contacts-{date}.csv
│
├── artifacts/                       # Deliverables (output only)
│   ├── sales/                       # Sales materials per segment
│   │   ├── {segment}/               # e.g., dtc-fashion-smb
│   │   │   ├── materials/           # Sales collateral
│   │   │   │   ├── pitch-deck.md
│   │   │   │   ├── one-pager.md
│   │   │   │   ├── call-scripts.md
│   │   │   │   ├── email-templates.md
│   │   │   │   └── archive/         # Old versions
│   │   │   ├── narratives/          # Sales messaging
│   │   │   │   ├── {segment}-economic-buyer.md
│   │   │   │   ├── {segment}-technical-buyer.md
│   │   │   │   └── {segment}-objection-lib.md
│   │   │   ├── sequences/           # Outreach sequences
│   │   │   │   ├── tier1-{company}.md
│   │   │   │   ├── ALL-SEQUENCES-SUMMARY.md
│   │   │   │   └── archive/         # Old sequences
│   │   │   └── drafts/              # Awaiting approval
│   │   │       └── {date}/
│   ├── marketing/
│   │   ├── campaigns/{campaign-slug}/  # Published campaign content
│   │   │   ├── blog/{slug}.md
│   │   │   ├── linkedin/{date}-{slug}.md
│   │   │   ├── email/{date}-{slug}.md
│   │   │   └── distribution-record.yaml
│   │   ├── narrative/               # Content strategy (one-time)
│   │   │   ├── content-pillars.md
│   │   │   ├── seo-strategy.md
│   │   │   ├── brand-voice.md
│   │   │   └── channel-guidelines.md
│   │   └── website/                 # Pre-OS website content (legacy)
│   └── fundraising/
│
├── ops/                             # Daily interface (auto-generated)
│   ├── today.md                     # Bella's 5-min review
│   ├── velocity.md                  # Throughput metrics
│   ├── patterns.md                  # Detected anomalies
│   └── changes.md                   # Strategic flags
│
├── engineering/                     # Technical specs (active)
│   ├── services/
│   ├── standards/
│   └── domain/
│
└── .claude/skills/                  # AI execution layer
    ├── foundation-builder/
    ├── icp-generator/
    ├── sales-narrative/
    ├── sales-execution/
    │   ├── materials-generation/
    │   ├── prospect-research/
    │   ├── contact-finding/
    │   ├── outreach-sequencing/
    │   └── qualification-support/
    ├── marketing-narrative/
    │   └── references/
    │       ├── brand-voice-frameworks.md
    │       ├── channel-optimization-guide.md
    │       ├── content-pillar-examples.md
    │       └── messaging-hierarchy-templates.md
    ├── marketing-execution/
    │   ├── content-strategy/
    │   ├── content-generation/
    │   │   └── references/
    │   │       ├── blog-patterns.md
    │   │       ├── case-study-pattern.md
    │   │       ├── announcement-pattern.md
    │   │       ├── linkedin-patterns.md
    │   │       └── email-patterns.md
    │   ├── seo-optimization/
    │   ├── content-distribution/
    │   └── performance-tracking/
    ├── causal-flow/
    │   ├── actions/
    │   │   └── templates/
    │   │       ├── marketing-create.md
    │   │       ├── marketing-measure.md
    │   │       ├── marketing-promote.md
    │   │       ├── marketing-publish.md
    │   │       ├── marketing-research.md
    │   │       ├── sales-close.md
    │   │       ├── sales-demo.md
    │   │       ├── sales-lead-intake.md
    │   │       ├── sales-pilot.md
    │   │       └── sales-qualify.md
    │   ├── reference/
    │   │   ├── business-threads.md
    │   │   ├── marketing-threads.md
    │   │   └── sales-threads.md
    │   ├── stages/
    │   │   ├── causal-flow-input/
    │   │   ├── causal-flow-hypothesis/
    │   │   ├── causal-flow-implication/
    │   │   ├── causal-flow-decision/
    │   │   ├── causal-flow-actions/
    │   │   └── causal-flow-learning/
    │   └── SKILL.md
    └── ops-dashboard/
```

## How It Works: Complete Operations Flow

### The 6-Stage Causal Flow (Universal)

Every decision (business, sales, marketing) flows through 6 stages:

**Stage 1: INPUT**
```text
└─  Capture factual observation (not opinion)
    Example: "ElsaAI deal closed: $1.1M ARR, 38% return reduction"
    Skill: causal-flow/stages/causal-flow-input/SKILL.md
```

**Stage 2: HYPOTHESIS**
```text
└─  Challenge/validate Canvas assumptions
    Example: "Tests A4: Luxury brands prefer white-label (validated)"
    Skill: causal-flow/stages/causal-flow-hypothesis/SKILL.md
```

**Stage 3: IMPLICATION**
```text
└─  Analyze full cost/benefit with numbers
    Example: "Content opportunity: Case study, Priority: 0.85, Impact: 500 sessions/month"
    Skill: causal-flow/stages/causal-flow-implication/SKILL.md
```

**Stage 4: DECISION**
```text
└─  Official commitment, document alternatives
    Example: "CREATE - High-priority content, validates enterprise hypothesis"
    Skill: causal-flow/stages/causal-flow-decision/SKILL.md
```

**Stage 5: ACTIONS**
```text
└─  Break into executable tasks (typed for sales/marketing)
    Example: "marketing:create → marketing:publish → marketing:promote → marketing:measure"
    Skill: causal-flow/stages/causal-flow-actions/SKILL.md
```

**Stage 6: LEARNING**
```text
└─  Measure outcomes, validate hypothesis, update Canvas automatically
    Example: "Content drove 8 demos, ranking position 12, A4 confidence: 95%"
    Skill: causal-flow/stages/causal-flow-learning/SKILL.md
```

**Key Feature:** Stage 6 (Learning) automatically updates Canvas assumptions AND triggers new content opportunities.

### Sales Operations (Complete Flow)

#### Phase 1: Strategy (Pre-Thread, Runs Once Per Segment)

**1. Define ICP (Ideal Customer Profile)**
```text
skill: icp-generator
input: strategy/canvas/04-segments.md
output: research/customer/icp/{segment}-icp.yaml
```

Example outputs:
- `research/customer/icp/dtc-fashion-smb-icp.yaml`
- `research/customer/icp/marketplaces-resellers-icp.yaml`
- `research/customer/icp/luxury-brands-icp.yaml`

**2. Create Sales Narrative**
```text
skill: sales-narrative
input: Canvas + ICP
output: threads/sales/narrative/{segment}/
        ├── problem-narrative.md
        ├── solution-narrative.md
        └── specifics-narrative.md
```

**3. Generate Sales Materials**
```text
skill: sales-execution/materials-generation
input: Canvas + Narrative + ICP
output: artifacts/sales/current/
        ├── pitch-deck.md
        ├── one-pager.md
        ├── call-scripts.md
        ├── email-templates.md
        ├── pilot-agreement.md
        └── contract-template.md
```

### Phase 2: Execution (Thread-Driven, Per Deal)

**Deal Flow Example: ElsaAI (Luxury Brand)**
```text
Day 1-46: Deal progression
├─ Stage 1-4: Decide to pursue deal
└─ Stage 5 (Actions):
    ├─ sales:lead-intake → ICP score: 0.85 (high fit)
    ├─ sales:qualify → Discovery call, qualification score: 0.82
    ├─ sales:demo → Custom pitch deck, demo delivered
    ├─ sales:pilot → 30-day pilot, 38% return reduction achieved
    └─ sales:close → Contract signed, $1.1M ARR

Day 46: Deal closed
└─ Stage 6 (Learning): Metrics documented
    ├─ Canvas updated: A4 validated (luxury prefers white-label, 95% confidence)
    ├─ Metrics updated: ARR, cycle time, margins
    └─ TRIGGER: Marketing content opportunity detected

### Marketing Operations (Learning-Driven Flow)

#### Phase 1: Strategy (Pre-Content, Runs Once Per Product)

**Generate Marketing Narrative**
```text
skill: marketing-narrative
input: Canvas + Sales narratives (all segments)
output: artifacts/marketing/narrative/
        ├── content-pillars.md      # 3-5 strategic themes
        ├── seo-strategy.md          # Keywords by funnel stage
        ├── brand-voice.md           # Educational, technical tone
        └── channel-guidelines.md    # Format specs (blog, LinkedIn, email, website)
```

**Example: artifacts/marketing/narrative/**

**What's Generated:**

**content-pillars.md** (3-5 themes):
- Pillar 1: Return reduction economics
- Pillar 2: Product capabilities (white-label, co-branded)
- Pillar 3: Industry insights (luxury vs fast fashion)

**seo-strategy.md** (keywords by funnel):
- TOFU: "fashion returns problem", "fit issues ecommerce"
- MOFU: "reduce fashion returns", "virtual try-on SDK"
- BOFU: "white-label SDK", "GlamYouUp vs competitors"

**brand-voice.md** (tone guidelines):
- Educational, not promotional
- Technical depth included
- Data-driven (specific metrics)
- No sales CTAs in content

**channel-guidelines.md** (format specs):
- Blog: 800-2,500 words, SEO-optimized
- LinkedIn: 300-600 words, professional tone
- Email: 400-600 words, segmented
- Website: Scannable, conversion-focused

### Phase 2: Content Execution (Thread-Driven, Per Opportunity)

**Marketing execution is TRIGGERED by business learning**, not arbitrary calendars.

**Trigger Flow:**
```text
Sales thread completes (Stage 6: Learning)
    ↓
Thread: threads/sales/elsa-white-label/6-learning.md
Learning: "Luxury brands prefer white-label (N=5, 100% validation)"
    ↓
marketing-execution/content-strategy scans thread
    ↓
Opportunity detected:
- Topic: "Enterprise white-label case study"
- Pillar: Product capabilities
- Keyword: "white-label SDK"
- Priority: 0.85 (high)
    ↓
Flag in ops/today.md:
"[Priority: 0.85] Create case study: ElsaAI white-label success?"
    ↓
Bella approves: "Yes, create it"
    ↓
Campaign thread created: threads/marketing/campaigns/luxury-validation-nov-2024/
```

**Campaign Thread Execution (6-Stage Flow):**
```text
Stage 1: INPUT
└─ Business event: "5 luxury brands chose white-label (100% pattern)"
   Source: Pattern across threads/sales/*/6-learning.md

Stage 2: HYPOTHESIS
└─ Tests: "H1: Validation campaigns convert better than awareness"
   Canvas link: 10-assumptions.md → H1 (campaign performance)

Stage 3: IMPLICATION
└─ Business impact:
   - Target: 2,000 sessions → 20 demos (1% conversion)
   - Revenue impact: 10 deals × $500K = $5M pipeline influenced
   - Investment: 40 hours (2 case studies + 4 posts)
   - Timeline: 2 weeks to publish, 30 days to measure

Stage 4: DECISION
└─ Campaign plan: Launch luxury white-label validation campaign
   Content to produce:
   1. Case study: "ElsaAI Reduces Returns 38% with White-Label SDK"
   2. Case study: "How Luxury Brands Achieve Fit Accuracy"
   3. LinkedIn post: Key stat (38% reduction)
   4. LinkedIn post: Customer quote
   5. LinkedIn post: Technical approach
   6. LinkedIn post: White-label benefits
   Timeline: Nov 16-30, 2024
   Impact score: 0.85 (auto-execute)

Stage 5: ACTIONS (Campaign Execution)
└─ For each content piece in Stage 4:
   ├─ marketing-execution creates draft
   │   └─ Saved to: 5-actions/drafts/{piece}-draft.md
   │
   ├─ Human reviews (30 min per piece)
   │   └─ Verifies technical accuracy, approves
   │
   ├─ SEO optimization
   │   └─ Saved to: 5-actions/drafts/{piece}-optimized.md
   │
   ├─ Multi-channel distribution
   │   └─ Published to: artifacts/marketing/campaigns/luxury-validation-nov-2024/
   │       ├─ blog/elsaai-case-study.md
   │       ├─ linkedin/2024-11-17-elsaai.md
   │       └─ distribution-record.yaml (UTM tracking)
   │
   └─ Update execution-log.md
       └─ [x] ElsaAI case study: Published (blog + LinkedIn)

Stage 6: LEARNING (30-day campaign results)
└─ Campaign performance:
   ├─ Total sessions: 1,800 (90% of target)
   ├─ Total demos: 15 (75% of target)
   ├─ Conversion rate: 0.83% (below 1% target)
   ├─ Top performer: ElsaAI case study (1,200 sessions, 10 demos)
   ├─ Pipeline influenced: $7.5M (15 deals attributed)

   Hypothesis validation:
   └─ H1: Validation campaigns convert better
       Result: PARTIAL (0.83% vs 0.6% awareness = 38% better, but missed target)
       Confidence: 75%
       Canvas update: 10-assumptions.md → H1 status: partially validated

   Strategic insight:
   └─ Case studies outperform thought leadership
       Next campaign: Create follow-up luxury campaign (technical depth)
       Refinement: Increase case study allocation in content pillars

   New content opportunities triggered:
   └─ Follow-up content: "White-label SDK implementation guide"
       Priority: 0.72 (high)
       Rationale: SEO opportunity (keyword ranking #12, can reach top 10)
```

**Output Structure:**
```text
threads/marketing/content/elsaai-white-label-case-study/
├── metadata.yaml
│   ├── source_thread: "threads/sales/elsa-white-label/"
│   ├── pillar: "Product capabilities"
│   ├── keyword: "white-label SDK"
│   ├── priority: 0.85
│   ├── created: "2024-11-16"
│   └── status: "published"
├── draft.md (from content-generation)
├── optimized.md (from seo-optimization)
└── performance.yaml (from performance-tracking)
```

**Published Outputs:**
```text
artifacts/marketing/campaigns/luxury-validation-nov-2024/
├── blog/elsaai-white-label-sdk-case-study.md
├── linkedin/2024-11-17-elsaai-case-study.md
├── email/2024-11-19-newsletter.html
└── distribution-record.yaml
    └─ 2024-11-16: Published ElsaAI white-label case study (blog, LinkedIn, email)
```

---

## Getting Started: Foundation Building

### Why Start with Canvas?

The Lean Canvas (15 living documents in `strategy/canvas/`) is your **single source of truth**. Everything in LeanOS—sales narratives, marketing content, ICP definitions, business decisions—flows from the Canvas. Without it, you have no foundation.

**Critical principle:** Canvas is evidence-based, not aspirational. Every section must be validated through research, customer conversations, or experimentation.

### Canvas Creation Process

Use the `foundation-builder` skill to populate and validate all 15 Canvas sections through a structured 5-phase process:

#### Phase 0a: Discovery (Market Intelligence)

**Goal:** Understand the market, identify real customer problems, define segments

**Agents activated:**
- `market-intelligence`: Market analysis, TAM/SAM/SOM, competitive landscape
- `problem-solution-fit`: Problem validation through customer research

**Canvas sections populated:**
- 01-context.md (KBOS framework - Known, Believed, Objective, Subjective)
- 02-constraints.md (Budget, time, resource constraints)
- 03-opportunity.md (Market size, timing, trends)
- 04-segments.md (Customer segments with observable filters)
- 05-problem.md (Top 3 problems, existing alternatives)
- 06-competitive.md (Competitive landscape, positioning gaps)

**Example invocation:**
```text
skill: foundation-builder
phase: discovery
focus: "AI fashion recommendations for DTC brands"
```

**Output:** 6 Canvas sections with evidence-based market intelligence

---

#### Phase 0b: Definition (Value Proposition & Business Model)

**Goal:** Define unique value, positioning, revenue model, and MVP scope

**Agents activated:**
- `value-proposition`: UVP articulation, positioning, messaging hierarchy
- `business-model`: Revenue design, pricing strategy, unit economics
- `problem-solution-fit`: MVP definition, solution design

**Canvas sections populated:**
- 07-uvp.md (Unique Value Proposition - single sentence)
- 08-advantage.md (Unfair advantages, secret sauce)
- 09-solution.md (MVP feature set, solution approach)
- 11-pricing.md (Revenue model, pricing tiers)
- 12-costs.md (Cost structure, burn rate)
- 13-metrics.md (Key metrics, unit economics)

**Example invocation:**
```text
skill: foundation-builder
phase: definition
context: "Completed discovery, ready to define value prop and business model"
```

**Output:** 6 additional Canvas sections defining product and economics

---

#### Phase 1a: Validation (Assumption Testing)

**Goal:** Test critical assumptions before building, design experiments

**Agents activated:**
- `validation`: Experiment design, hypothesis testing, validation plans
- `execution`: Task orchestration for running experiments

**Canvas sections updated:**
- 10-assumptions.md (Hypotheses, validation status, confidence levels)

**Example invocation:**
```text
skill: foundation-builder
phase: validation
assumptions: "Luxury brands prefer white-label SDK, DTC brands will pay $500/month"
```

**Output:** Validated (or invalidated) assumptions with confidence scores

---

#### Phase 1b: Execution (MVP Build & Launch Prep)

**Goal:** Build MVP, prepare for launch, activate operations

**Agents activated:**
- `execution`: Development orchestration, sprint planning
- `go-to-market`: Channel strategy, launch planning

**Canvas sections populated:**
- 14-growth.md (Growth channels, acquisition tactics)
- 15-gtm.md (Go-to-market strategy, launch plan)

**Example invocation:**
```text
skill: foundation-builder
phase: execution
status: "Assumptions validated, ready to build MVP and plan launch"
```

**Output:** GTM strategy and operational readiness

---

#### Phase 2: Launch (Operational Mode)

**Goal:** Activate sales and marketing operations, maintain Canvas through learning

**Post-launch:** Canvas becomes living documentation
- Sales threads (Stage 6: Learning) update Canvas assumptions
- Marketing content reflects validated Canvas positioning
- Business decisions update Canvas sections continuously

**Validation criteria for launch readiness:**
- ✅ All 15 Canvas sections populated with evidence
- ✅ Critical assumptions validated (confidence ≥75%)
- ✅ ICP defined for at least 1 segment
- ✅ Sales narratives generated
- ✅ Marketing narratives created

---

### Specialist Agents (On-Demand)

**Use these agents for specific scenarios:**

**funding agent:**
- Trigger: Preparing to fundraise
- Output: `strategy/financials/fundraising.md` (pitch deck outline, investor targets, financial projections)

**regulatory agent:**
- Trigger: Entering regulated markets (healthcare, finance, insurance)
- Output: Compliance requirements, licensing roadmap

**retention-optimizer agent:**
- Trigger: Post-launch with cohort data
- Output: Churn analysis, retention experiments, optimization strategies

---

### Timeline: Pre-Launch to Operations

**Week 1-2: Discovery**
- Run market-intelligence and problem-solution-fit agents
- Populate Canvas 01-06
- Validate customer problems through interviews

**Week 3-4: Definition**
- Run value-proposition and business-model agents
- Populate Canvas 07-13
- Define MVP scope and pricing

**Week 5-6: Validation**
- Run validation agent
- Test critical assumptions (landing page, customer interviews, prototypes)
- Update 10-assumptions.md with results

**Week 7-8: Execution**
- Build MVP
- Run go-to-market agent
- Populate Canvas 14-15
- Generate sales/marketing narratives

**Week 9+: Launch**
- Activate sales operations (icp-generator, sales-execution)
- Activate marketing operations (marketing-narrative, marketing-execution)
- Canvas maintained through thread learning

---

## Marketing Activation

**Marketing is learning-driven, not calendar-driven.** But it doesn't wait for sales learning—it starts with Canvas/research, then improves with validation.

### Timeline: Marketing + Sales in Parallel

**Week 1:** Sales activation (DTC segment ready)

**Week 2 (PARALLEL):**
- **Sales:** DTC outreach begins (10 prospects contacted)
- **Marketing:** Initial content created (foundational, Canvas-based)

**Week 3-4:**
- **Sales:** Threads complete Stage 6 (learning captured)
- **Marketing:** Content refined based on sales learning

**Continuous:** Sales learning → Content opportunities → Published → Drives demos → More learning

### Prerequisites

1. ✅ Sales infrastructure operational (DTC segment activated)
2. ✅ Marketing skills installed (marketing-narrative, marketing-execution)
3. ⏭️ Marketing narratives generated (content pillars, brand voice) - **PRIORITY #1**

---

### One-Time Setup (30-45 minutes)

**Step 1: Generate Marketing Narratives (BEFORE sales campaign starts)**

Use marketing-narrative skill to create content foundation:

skill: marketing-narrative
**Output:** `threads/marketing/narrative/`
- content-pillars.md (3-5 strategic themes aligned with Canvas UVP)
- brand-voice.md (tone, style, vocabulary guidelines)
- seo-strategy.md (keyword priorities and search intent mapping)
- channel-guidelines.md (blog, LinkedIn, email format specs)
**Sources (Canvas + research, NOT sales learning yet):**
- Canvas: positioning, problems, solutions, value props
- Research: buyer personas, prospect insights, industry data
- Sales narratives: messaging consistency

---

### Initial Content Creation (Week 2)

**Don't wait for sales learning. Create foundational content from Canvas + research:**

**Initial content opportunities:**

**A. Educational Content (Problem-focused):**
- "Why 30% of Fashion Returns Are Fit-Related" (Canvas problem.md)
- "The Hidden Cost of Sizing Issues for DTC Brands" (research data)
- "Body Shape vs Measurements: Why Traditional Sizing Fails" (Canvas solution.md)

**B. Product Capabilities:**
- "Dual Intelligence: Fit + Color Analysis Explained" (Canvas UVP)
- "How Seasonal Color Analysis Reduces Color-Based Returns" (Canvas solution.md)
- "Brand Affinity Intelligence for Marketplaces" (marketplace narrative)

**C. Industry Insights:**
- "DTC Fashion: Return Reduction Benchmarks" (research/customer data)
- "What 191 Shopify Fashion Brands Share in Common" (prospect research)

**Process:**
1. Identify 2-3 initial topics (from Canvas + research)
2. Create marketing threads: `threads/marketing/content/{topic-slug}/`
3. Execute 6-stage flow (draft → review → publish → promote → measure)
4. Publish Week 2 (BEFORE or DURING DTC outreach)

**Goal:** 2-3 foundational pieces live when DTC outreach begins

---

### Validation Criteria

Marketing workflow is operational when:
- ✅ Narratives generated (content-pillars.md exists)
- ✅ 2-3 initial articles published (Canvas-based)
- ✅ Daily scan running (ops/today.md shows content section)
- ✅ Sales learning triggering refinements (content updated with real data)
- ✅ Attribution tracking active (content → demo pipeline measured)

**Success:** Marketing content live BEFORE or DURING sales outreach (not after)

---

## Complete Marketing Workflow (Automated)

### Daily Automated Scan

**Every morning (automated):**
```text
marketing-execution/content-strategy scans:
└─ All threads updated in last 30 days
    ├─ threads/sales/*/6-learning.md
    ├─ threads/business/*/6-learning.md
    └─ engineering/services/*/announcements.md

For each thread with learning:
└─ Extract signals:
    ├─ Validated hypothesis (≥3 data points)
    ├─ Quantified customer results
    ├─ Strategic Canvas update
    └─ Common pattern (≥3 similar threads)

Match to content pillars:
└─ threads/marketing/narrative/{segment}/content-pillars.md

Calculate priority score:
└─ Priority = (Impact × Confidence × Timeliness × SEO Value) / 4

If priority ≥ 0.7:
└─ Flag in ops/today.md for human approval
Example ops/today.md Output:
markdown# Today's Review - 2024-11-16

## Content Opportunities (Auto-Detected)

### High Priority (≥0.7)

1. **[0.85] Case Study: ElsaAI White-Label Success**
   - Source: threads/sales/elsa-white-label/6-learning.md
   - Pillar: Product capabilities
   - Keyword: "white-label SDK"
   - Impact: 500 sessions/month, 25 demos
   - Action: Approve to generate draft

2. **[0.78] Guide: Reducing Fit-Based Returns**
   - Source: Pattern across 8 deals (threads/sales/*/6-learning.md)
   - Pillar: Return reduction economics
   - Keyword: "reduce fashion returns"
   - Impact: 800 sessions/month, 15 demos
   - Action: Approve to generate draft

### Medium Priority (0.5-0.7)

3. **[0.65] Analysis: DTC vs Marketplace Fit Needs**
   - Source: threads/business/segment-analysis/6-learning.md
   - Pillar: Industry insights
   - Keyword: "fashion marketplace sizing"
   - Impact: 200 sessions/month, 5 demos
   - Action: Add to backlog
```

### Human Decision Point

**Bella's action (2 minutes):**
```text
Review high-priority opportunities:
1. "Case Study: ElsaAI" → Approve ✓
2. "Guide: Reducing Returns" → Approve ✓
3. "DTC vs Marketplace" → Defer (lower priority)
```

### Automated Content Pipeline

**Once approved, AI executes autonomously:**
```text
For each approved opportunity:

1. Create marketing thread:
   └─ threads/marketing/content/{topic-slug}/

2. Execute Stage 1-4 (Input → Hypothesis → Implication → Decision)
   └─ Auto-generated (no human input needed)

3. Execute Stage 5 (Actions):
   ├─ marketing:create
   │   └─ AI generates draft (1,450 words)
   │   └─ Save to drafts/ for human review
   │   └─ Flag in ops/today.md: "Draft ready for review"
   │
   ├─ Human reviews draft (30 minutes)
   │   └─ Checks technical accuracy, approves
   │
   ├─ marketing:publish
   │   ├─ AI optimizes SEO
   │   ├─ AI publishes to blog/LinkedIn/email
   │   └─ AI adds UTM tracking
   │
   ├─ marketing:promote
   │   └─ AI schedules cross-channel posts
   │
   └─ marketing:measure
       └─ AI tracks performance (7 days, 30 days, 90 days)

4. Execute Stage 6 (Learning - Day 30):
   ├─ AI compiles performance metrics
   ├─ AI validates content hypothesis
   ├─ AI updates Canvas assumptions
   └─ AI flags new opportunities (if top performer)
```

### Continuous Improvement Loop

**Performance feedback triggers new content:**
```text
If content performs well (conversion rate >2x average):
└─ marketing-execution/content-strategy flags:
    "Top performer: ElsaAI case study (1.23% conversion)"
    "Recommendation: Create follow-up content (implementation guide)"
    "New opportunity: Priority 0.72 (white-label implementation guide)"
    └─ Flag in ops/today.md for approval

If content underperforms (<50% expected traffic):
└─ marketing-execution/performance-tracking flags:
    "Underperformer: API rate limiting post (42 sessions, 0 demos)"
    "Issue: Niche topic, no pillar alignment"
    "Recommendation: Retire technical posts or move to dev docs"
    └─ Update content-pillars.md (reduce technical pillar allocation)

Complete Daily Workflow: Bella's 5-Minute Review
Morning Routine (8:00 AM)
bash# Read auto-generated daily summary
cat ops/today.md
Example Output:
markdown# Today's Review - 2024-11-16

## High-Priority Items (Human Approval Required)

### 1. Content Opportunity [Priority: 0.85]
Type: Case study
Topic: ElsaAI white-label success
Source: threads/sales/elsa-white-label/6-learning.md
Impact: 500 sessions/month, 25 demos
Action: Approve to generate draft?
  [ ] Approve
  [ ] Defer
  [ ] Reject

### 2. Content Draft Ready [Word count: 1,450]
Topic: ElsaAI white-label SDK case study
Location: artifacts/marketing/glamyouup/drafts/2024-11-16/
Quality checks: ✓ SEO optimized, ✓ Voice compliant, ✓ No confidential info
Action: Review for technical accuracy, approve for publication
  [ ] Approve
  [ ] Request revisions
  [ ] Reject

### 3. Demo Call Scheduled
Thread: threads/sales/allbirds-inbound/
Time: 2:00 PM today
Prep: Custom pitch deck generated
Action: Review prep materials (5 min recommended)

---

## Decisions Made by AI (Last 24h)

**Sales:**
✓ Qualified 3 leads (2 high priority, 1 medium)
✓ Sent 45 outreach emails (dtc-fashion-smb campaign)
✓ Generated pilot results for everlane-pilot

**Marketing:**
✓ Published: ElsaAI case study (blog, LinkedIn, email)
✓ Tracked: 650 sessions, 8 demos (1.23% conversion - top performer!)
✓ Detected: New opportunity (white-label implementation guide, priority 0.72)

**Canvas Updates:**
✓ A4: Luxury brands prefer white-label (validated, 95% confidence)
✓ H1: Case studies convert 2x better than guides (validated, 85% confidence)

---

## Active Operations Summary

**Sales Pipeline:**
- 5 in qualification
- 3 in demo prep
- 2 in pilot
- 1 in contract negotiation

**Sales Campaigns:**
- dtc-fashion-smb-2024-11: 45/100 prospects contacted, 8 responses

**Marketing Content:**
- 2 drafts awaiting review
- 1 published this week (ElsaAI case study)
- 3 LinkedIn posts scheduled (Days 2, 9, 16)

---

## Performance Alerts

🎉 **Top Performer (Last 7 Days)**
- ElsaAI case study: 650 sessions, 8 demos (1.23% rate vs 0.6% avg)
- Action: Create follow-up content, use in sales enablement

⚠️ **Underperformer (Last 30 Days)**
- API rate limiting post: 42 sessions, 0 demos
- Issue: Niche topic, no pillar alignment
- Action: Reassess technical content strategy

📈 **SEO Milestone**
- "luxury fashion returns" reached position 8 (top 10!)
- Traffic potential: +500 sessions/month
- Action: Create cluster content around this keyword

---

## Anomalies Detected

⚠️ Legal review taking 2x longer than estimated (5 days vs 3 days)
→ Meta-thread suggested: Investigate legal bottleneck
```

### Bella's Actions (3 minutes)

**1. Approve content opportunities:**
- [x] ElsaAI case study: Approve ✓
- Time: 30 seconds

**2. Review content draft:**
- Open: artifacts/marketing/glamyouup/drafts/2024-11-16/elsaai-white-label.md
- Check technical accuracy (metrics, customer name)
- Approve for publication ✓
- Time: 2 minutes

**3. Review demo prep:**
- Skim custom pitch deck
- Note key talking points
- Time: 30 seconds

**Total time: 3 minutes**

### Rest of Day

**Human-required touchpoints:**
- 2:00 PM: Demo call (45 min)

**AI handles autonomously:**
- Qualification call prep
- Follow-up emails
- Content publication (blog, LinkedIn, email)
- Performance tracking
- Pipeline updates
- Next content opportunity detection

---

## Marketing-Sales Integration

### Content Influences Sales (Closed Loop)

**Flow:**
```text
Marketing publishes case study
    ↓
SEO drives organic traffic
    ↓
Visitor reads: "ElsaAI reduced returns 38%"
    ↓
Visitor requests demo
    ↓
Sales thread created: threads/sales/{company}-inbound/
    ↓
Stage 1 (Input): "Came from blog article (elsaai-white-label-case-study)"
    ↓
Sales thread references marketing thread:
metadata.yaml:
  source: "marketing/content/elsaai-white-label-case-study/"
  attribution: "Blog article"
    ↓
Stage 6 (Learning - if deal closes):
"Won $500K ARR, attributed to blog article"
    ↓
marketing-execution/performance-tracking updates:
performance.yaml:
  pipeline_influenced: "$550K" (cumulative)
  conversions: 9 demos, 2 closed deals
    ↓
Canvas updated:
10-assumptions.md → H1: Case studies convert better (confidence: 95%)
```

### Sales Triggers Marketing (Learning Loop)

**Flow:**
```text
Sales closes 5 luxury brand deals
    ↓
Pattern detected: All 5 chose white-label SDK
    ↓
Stage 6 (Learning) in each thread:
"Luxury brands prefer white-label (validated)"
    ↓
Canvas updated:
10-assumptions.md → A4: Luxury prefers white-label (confidence: 95%)
    ↓
marketing-execution/content-strategy detects:
"Strong signal: Luxury white-label preference (N=5, 100% validation)"
"Content opportunity: Case study + implementation guide"
Priority: 0.85 (high)
    ↓
Flag in ops/today.md
    ↓
Bella approves
    ↓
Marketing thread created
    ↓
Content published
    ↓
SEO drives traffic
    ↓
Demos requested
    ↓
Sales threads created
    ↓
... (loop continues)

```

## Success Metrics

### Operational Efficiency

**Target:** <30 min/day human time on operations

**Breakdown:**
- ops/today.md review: 5 minutes
- Content draft review: 5-10 minutes (2-3x per week)
- Sales materials review: 5 minutes (monthly, when Canvas changes)
- **Total:** <30 minutes/day average

**AI autonomy rate:** >95% of decisions

### Marketing Performance

**Content creation efficiency:**
- Time from thread completion to published content: <7 days
- Human review time per draft: <30 minutes
- Content pieces per business learning: 1-3 (case study + follow-ups)

**Content quality:**
- Technical accuracy: 100% (verified by human)
- SEO optimization: All required elements present
- Brand voice: Educational, non-promotional

**Business impact:**
- Organic traffic: {target sessions/month}
- Demos from content: {target conversions/month}
- Pipeline influenced: {target revenue attributed}
- Top performer hit rate: >50% (content exceeds benchmarks)

### Sales Performance

**Pipeline velocity:**
- Lead response time: <24h
- Qualification time: <7 days
- Demo booking rate: >40%
- Pilot conversion: >60%
- Close rate (qualified): >50%

**Materials quality:**
- Pitch deck approval: >90% (minimal revisions)
- Email response rate: >10% (cold outreach)
- Proposal acceptance: >80%

### Information Quality

**Canvas integrity:**
- Sections tracked: 15 living documents
- Auto-update accuracy: >95% (Stage 6 → Canvas)
- Assumption validation: Tracked per thread
- Zero duplication: 1 source of truth

**Decision traceability:**
- 100% of decisions in threads
- Complete 6-stage flow
- Canvas linkage maintained


## Key AI Skills Reference

### Marketing Strategy

**marketing-narrative**

- **Purpose:** Generate content strategy (pillars, SEO, voice, channels)
- **Input:** Canvas + Sales narratives (all segments)
- **Output:** threads/marketing/narrative/{segment}/
  - content-pillars.md (3-5 themes)
  - seo-strategy.md (keywords by funnel)
  - brand-voice.md (educational tone)
  - channel-guidelines.md (format specs)
- **Trigger:** When Canvas positioning changes or sales narratives finalized
- **Human review:** Optional (review generated strategy)

### Marketing Execution

**marketing-execution (orchestrator)**

- **Purpose:** Coordinate content workflow (strategy → publication → tracking)
- **Input:** Thread learning or manual request
- **Output:** Published content + performance data
- **Trigger:** Thread completes OR manual content request
- **Human review:** Draft review (Stage 5, before publication)

**marketing-execution/content-strategy**

- **Purpose:** Scan threads for content opportunities
- **Input:** All completed threads (last 30 days)
- **Output:** Prioritized content opportunities
- **Trigger:** Daily automated scan
- **Human review:** Approve high-priority opportunities (≥0.7)

**marketing-execution/content-generation**

- **Purpose:** Generate educational drafts from thread learning
- **Input:** Content opportunity + source thread
- **Output:** Draft content (blog, case study, guide, etc.)
- **Trigger:** After opportunity approved
- **Human review:** Technical accuracy, voice compliance

**marketing-execution/seo-optimization**

- **Purpose:** Optimize content for search discovery
- **Input:** Draft content + target keyword
- **Output:** SEO-optimized content (title, meta, H1/H2, keywords, internal links)
- **Trigger:** After draft approved
- **Human review:** No (automated)

**marketing-execution/content-distribution**

- **Purpose:** Publish to blog/LinkedIn/email/website
- **Input:** Optimized content + distribution plan
- **Output:** Published content with UTM tracking
- **Trigger:** After SEO optimization
- **Human review:** Final approval before publication

**marketing-execution/performance-tracking**

- **Purpose:** Measure content impact, feed insights back to strategy
- **Input:** Published content URLs + analytics data
- **Output:** Performance reports, recommendations
- **Trigger:** Day 7, Day 30, Day 90 after publication
- **Human review:** Review top/underperformers monthly


## Current Status & Roadmap

### ✅ Completed (Phase 1: Sales Foundation)

- Lean Canvas (15 living documents)
- 6-stage causal flow orchestrator
- ICP generator (per segment)
- Sales narrative generator (per segment)
- Sales materials generator (6 types)
- Sales execution subskills (5 subskills)
- Sales thread architecture

### ✅ Completed (Phase 2: Marketing Foundation)

- Marketing narrative generator (content strategy)
- Marketing execution orchestrator
- Content strategy (opportunity detection)
- Content generation (educational drafts)
- SEO optimization (natural keyword integration)
- Content distribution (multi-channel publishing)
- Performance tracking (metrics analysis, insights)
- Marketing thread architecture
- Sales-marketing integration (closed loop attribution)

### 🚧 In Progress (Phase 3: Validation)

- Test sales operations with GlamYouUp (DTC Fashion SMB segment)
- Run first outbound campaign (50 prospects)
- Validate first marketing content (ElsaAI case study)
- Track full loop: Sales learning → Content → Demos → Closed deals

### 📋 Planned (Phase 4: Operations Dashboard)

- Ops dashboard auto-generation
  - today.md (daily review)
  - velocity.md (throughput metrics)
  - patterns.md (anomaly detection)
  - changes.md (strategic flags)
- Meta-learning (pattern detection across threads)
- Process improvement automation

### 🔮 Future (Phase 5: Full Automation)

- Customer success operations
- Fundraising operations
- Engineering operations (spec generation, code review)

---

## Engineering Skills (Technical Systems)

LeanOS includes engineering-focused skills for building technical systems:

### category-theoretic-system-design

**Purpose:** Transform natural language requirements into production-ready systems using category theory

**What it does:**
- Orchestrates 8 compositional skills for system design
- Provides mathematical guarantees of correctness
- Handles parsing, validation, optimization, and code generation
- Uses category theory and algebraic methods

**Use cases:**
- Building complex microservices from requirements
- Need mathematical correctness guarantees
- Multi-platform, multi-tenant, or versioned systems
- Formal verification of system properties

**8-Skill Workflow:**
1. ADT Analyzer - Parse requirements into algebraic expressions
2. Category Theory Foundation - Validate structure
3. Functor Generator - Design transformations
4. Natural Transformation Engine - Plan migrations
5. Curry-Howard Prover - Generate type signatures & proofs
6. System Optimizer - Apply algebraic laws
7. Architecture Validator - Verify correctness
8. Code Generator - Produce implementation

### standardization-layer

**Purpose:** Apply uniform cross-cutting concerns to microservices using natural transformations

**What it does:**
- Applies authentication (JWT, API Key, OAuth)
- Adds validation (schema, size limits, sanitization)
- Standardizes response formats
- Implements error handling (retries, circuit breakers)
- Adds observability (logging, metrics, tracing)
- Configures rate limiting

**Use cases:**
- Applying consistent middleware across microservices
- Standardizing authentication and authorization
- Ensuring uniform error handling and response formats
- Maintaining mathematical consistency through category theory

**Note:** These engineering skills are separate from business operations skills (sales, marketing, strategy). They're used for building the technical infrastructure that supports the business operations.

---

## Technology Stack

**Core AI:**
- Claude Sonnet 4.5 (primary model)
- Claude Skills system (execution layer)

**Languages:**
- Python (FastAPI, microservices)
- Bash (automation scripts)
- Markdown (all documentation)

**Tools:**
- web_search (prospect research, contact finding, SEO research)
- Read/Write (file operations)
- str_replace (Canvas updates)
- Bash (content publishing, sitemap generation)

**Custom Skills:**
- Business Operations: foundation-builder, icp-generator, sales-narrative, sales-execution, marketing-narrative, marketing-execution, causal-flow, ops-dashboard
- Engineering: category-theoretic-system-design, standardization-layer
- Utility (Third-Party): document-skills (© Anthropic, PBC - see [THIRD-PARTY-LICENSES.md](THIRD-PARTY-LICENSES.md))

**Infrastructure:**
- Local file system (no external services for MVP)
- Git (version control, Canvas history)


## FAQ

**Q: How does marketing content get created?**

A: Content is triggered by business learning (sales threads, strategic decisions), not arbitrary calendars. When threads complete Stage 6 (Learning), content-strategy scans for insights worth sharing. High-priority opportunities (≥0.7) are flagged for human approval. Once approved, AI generates draft, optimizes SEO, publishes multi-channel, and tracks performance.

**Q: Can I manually request content?**

A: Yes. Specify topic, keyword, content type (blog/case study/guide), and source thread (optional). AI skips content-strategy and goes directly to content-generation → SEO → distribution → tracking.

**Q: How is content quality maintained?**

A: (1) Brand voice guidelines enforce educational tone, (2) Human reviews drafts for technical accuracy before publication, (3) Content patterns (not templates) ensure structure, (4) Performance tracking identifies underperformers for improvement.

**Q: What if content underperforms?**

A: Performance-tracking flags underperformers (<50% expected traffic) in ops/today.md. AI recommends: (1) SEO optimization (if ranking issue), (2) Topic reassessment (if no audience interest), (3) Pillar retirement (if systematic underperformance).

**Q: How does marketing influence sales?**

A: Published content drives organic traffic → Demo requests → Sales threads created with attribution metadata → Stage 6 (Learning) tracks pipeline influenced → Performance-tracking updates content ROI → Canvas updates content performance assumptions.

**Q: How many content pieces per month?**

A: Variable, based on business learning. Target: 2-4 high-quality pieces/month (1 per major sales learning or strategic insight). Quality over quantity—no arbitrary "publish 20 posts/month" quotas.

**Q: What about social media engagement (likes, comments)?**

A: Not a focus. Success = pipeline influenced and organic discovery, not engagement metrics. Content is educational (builds authority), not engagement bait.

## Troubleshooting

### Marketing-Specific Issues

**Problem: Content opportunities not detected**
```bash
# Check thread completion
ls threads/sales/*/6-learning.md

# Check content-strategy execution
# (Manually trigger scan)
skill: marketing-execution/content-strategy

# Check priority threshold
# (Opportunities <0.7 won't flag automatically)


**Problem: Content draft quality low**
```bash
# Check source thread has sufficient learning
cat threads/sales/{deal}/6-learning.md

# Check brand voice guidelines exist
cat threads/marketing/narrative/{segment}/brand-voice.md

# Check content patterns loaded
ls .claude/skills/marketing-execution/content-generation/references/

# Request revisions with specific feedback
```

**Problem: SEO optimization not working**
```bash
# Check target keyword specified
cat threads/marketing/content/{topic}/metadata.yaml

# Check SEO strategy exists
cat threads/marketing/narrative/{segment}/seo-strategy.md

# Verify keyword not keyword-stuffed (check density <2%)
```

**Problem: Content not publishing**
```bash
# Check human approval received
cat threads/marketing/content/{topic}/metadata.yaml
# status: should be "approved" not "draft"

# Check blog publishing endpoint works
# (Test with simple post)

# Check UTM parameters generated
cat distribution-record-{date}-{slug}.yaml
```

**Problem: Performance tracking not updating**
```bash
# Check analytics access (if automated)
# (May require manual data entry if no API)

# Check distribution record exists
ls distribution-record-*.yaml

# Manually update performance.yaml if needed
```

## Contributing

Interested in improving LeanOS? See [CONTRIBUTING.md](CONTRIBUTING.md) for:
- How to contribute skills, documentation, and architecture improvements
- Contribution process and standards
- What to contribute (and what not to)
- Review process and timelines

**Note:** LeanOS is operated by Claude AI. Contributions focus on design and architecture, not local setup or execution.

## Support & Contact

**Primary maintainer:** Bella (https://www.linkedin.com/in/bellabelgarokova/)

**Documentation:**
- This README (complete system overview)
- [CLAUDE.md](CLAUDE.md) (AI agent operational instructions)
- [CONTRIBUTING.md](CONTRIBUTING.md) (contribution guidelines)
- strategy/canvas/ (business strategy)
- .claude/skills/*/SKILL.md (skill documentation)
- threads/*/reference/*.md (thread architecture)

**Philosophy:**
- Direct, no-nonsense communication
- Production-ready over theoretical
- Question assumptions, value simplicity
- Designed for universality
- Continuous improvement via feedback loops
- Learning-driven, not calendar-driven
- Authority through depth, not engagement tricks
- AI-operated, human-supervised

## License and Attribution

### LeanOS Components

**Copyright:** © 2025 Bella Belgarokova

**License:** MIT License

All LeanOS-created components (business operations skills, documentation, architecture, workflows) are open source under the MIT License. See [LICENSE](LICENSE) for full terms.

### Third-Party Components

**document-skills** (`.claude/skills/document-skills/`)

**Copyright:** © 2025 Anthropic, PBC. All rights reserved.

**License:** Proprietary - Use governed by Anthropic's service terms

These document handling skills (PDF, DOCX, PPTX, XLSX) are provided by Anthropic and remain their intellectual property. They cannot be modified, redistributed, or used outside of Anthropic's services.

See [THIRD-PARTY-LICENSES.md](THIRD-PARTY-LICENSES.md) for complete licensing information.

---

**Last updated:** 2024-11-16
**Next review:** After first 5 marketing threads complete
**Version:** 1.0 (Marketing Layer Complete)