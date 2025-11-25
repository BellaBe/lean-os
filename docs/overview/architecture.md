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
│ SKILLS LAYER (AI Execution) - 19 skills, 60+ sub-skills                                      │
│                                                                                              │
│ ┌─────────────────────────────────────────────────────────────────────────────────────────┐  │
│ │ ENGINEERING SKILLS (engineering-*) - 7 skills, 27 sub-skills                            │  │
│ │                                                                                         │  │
│ │ Full production flow: Requirements → Architecture → Maps → Code → Deployment            │  │
│ │                                                                                         │  │
│ │ system-architecture (9 sub-skills)                                          │  │
│ │ └─ NL requirements → mathematical specs (ADT, Curry-Howard proofs, categorical arch)    │  │
│ │                                                                                         │  │
│ │ standardization-definer                                                     │  │
│ │ └─ Extract cross-cutting concerns → contract maps (WHAT standards exist)                │  │
│ │                                                                                         │  │
│ │ backend-prover (4 sub-skills)                                               │  │
│ │ └─ Phase 1: Generate maps, verify composition                                           │  │
│ │ └─ Phase 2: Generate code from verified maps                                            │  │
│ │                                                                                         │  │
│ │ standardization-applier                                                     │  │
│ │ └─ Apply standards to code, verify naturality (HOW to inject)                           │  │
│ │                                                                                         │  │
│ │ frontend-prover (4 sub-skills)                                              │  │
│ │ └─ OpenAPI → TypeScript, framework adapters, type correspondence proofs                 │  │
│ │                                                                                         │  │
│ │   infrastructure-prover (5 sub-skills)                                        │  │
│ │ └─ Service specs → Docker, K8s, CI/CD, topology proofs                                  │  │
│ │                                                                                         │  │
│ │ proof-composer                                                              │  │
│ │ └─ Validate entire proof chain → deployment authorization                               │  │
│ └─────────────────────────────────────────────────────────────────────────────────────────┘  │
│                                                                                              │
│ ┌─────────────────────────────────────────────────────────────────────────────────────────┐  │
│ │ FOUNDATIONS SKILLS (foundations-*) - 4 skills                                           │  │
│ │                                                                                         │  │
│ │ foundations-builder (10 agents)                                                         │  │
│ │ └─ Canvas population: Discovery → Definition → Validation → Execution → Launch          │  │
│ │    Core Agents (7): market-intelligence, problem-solution-fit, value-proposition,       │  │
│ │                     business-model, validation, go-to-market, execution                 │  │
│ │    Specialist (3): funding, regulatory, retention-optimizer                             │  │
│ │                                                                                         │  │
│ │ icp-generator                                                               │  │
│ │ └─ Define ICP per segment → research/customer/icp/{segment}-icp.yaml                    │  │
│ │                                                                                         │  │
│ │ sales-narrative                                                             │  │
│ │ └─ Generate sales messaging per segment → artifacts/sales/{segment}/narratives/         │  │
│ │                                                                                         │  │
│ │ marketing-narrative                                                         │  │
│ │ └─ Generate content strategy → artifacts/marketing/narrative/                           │  │
│ └─────────────────────────────────────────────────────────────────────────────────────────┘  │
│                                                                                              │
│ ┌─────────────────────────────────────────────────────────────────────────────────────────┐  │
│ │ OPERATIONS SKILLS (ops-*) - 4 skills                                                    │  │
│ │                                                                                         │  │
│ │ causal-flow (6 stage skills)                                                        │  │
│ │ └─ 6-stage decision flow: Input → Hypothesis → Implication → Decision → Actions →      │  │
│ │    Learning                                                                             │  │
│ │ └─ Thread types: business, sales, marketing, engineering                                │  │
│ │ └─ Stage 6 auto-updates Canvas from validated learning                                  │  │
│ │                                                                                         │  │
│ │ content-strategy                                                                    │  │
│ │ └─ Daily scan: threads → campaign opportunities → ops/today.md                          │  │
│ │                                                                                         │  │
│ │ ops-dashboard                                                                           │  │
│ │ └─ Auto-generate: today.md, velocity.md, patterns.md, changes.md                        │  │
│ │                                                                                         │  │
│ │ business-metrics-tracker                                                            │  │
│ │ └─ Mode-aware metrics (VENTURE: ARR, MAU | BOOTSTRAP: MRR, profit)                      │  │
│ └─────────────────────────────────────────────────────────────────────────────────────────┘  │
│                                                                                              │
│ ┌─────────────────────────────────────────────────────────────────────────────────────────┐  │
│ │ RESEARCH SKILLS (research-*) - 2 skills                                                 │  │
│ │                                                                                         │  │
│ │ research-market-venture                                                                 │  │
│ │ └─ TAM sizing, growth rates, competitive landscape, defensibility (VENTURE mode)        │  │
│ │                                                                                         │  │
│ │ research-market-bootstrap                                                               │  │
│ │ └─ Spend mapping, arbitrage, immediate revenue (BOOTSTRAP mode)                         │  │
│ └─────────────────────────────────────────────────────────────────────────────────────────┘  │
│                                                                                              │
│ ┌─────────────────────────────────────────────────────────────────────────────────────────┐  │
│ │ EXECUTION SKILLS - 2 skills                                                             │  │
│ │                                                                                         │  │
│ │ sales-execution (5 sub-skills)                                                          │  │
│ │ └─ materials-generation, prospect-research, contact-finding,                            │  │
│ │    outreach-sequencing, qualification-support                                           │  │
│ │                                                                                         │  │
│ │ marketing-execution (4 sub-skills)                                                      │  │
│ │ └─ content-generation, seo-optimization, content-distribution, performance-tracking     │  │
│ └─────────────────────────────────────────────────────────────────────────────────────────┘  │
│                                                                                              │
└──────────────────────────────────────────────────────────────────────────────────────────────┘
                                          ↓
┌──────────────────────────────────────────────────────────────────────────────────────────────┐
│ THREADS LAYER (Decision Storage)                                                             │
│ Complete decision narratives with 6-stage causal flow                                        │
│ Location: threads/{type}/{thread-name}/                                                      │
│                                                                                              │
│ Thread Types:                                                                                │
│ ├─ business/: Strategic decisions                                                            │
│ ├─ sales/: Deal pipeline management                                                          │
│ │   ├─ campaigns/: Outbound prospecting (YYYY-MM-DD-name)                                    │
│ │   └─ {company-name}/: Individual deal threads                                              │
│ ├─ marketing/: Content execution                                                             │
│ │   ├─ campaigns/{campaign-slug}/: Campaign threads                                          │
│ │   └─ narrative/{product}/: Content strategy                                                │
│ └─ engineering/: Technical requirements                                                      │
│     └─ {requirement}/: Engineering decision threads                                          │
└──────────────────────────────────────────────────────────────────────────────────────────────┘
                                          ↓
┌──────────────────────────────────────────────────────────────────────────────────────────────┐
│ OPS DASHBOARD (Daily Interface)                                                              │
│ Auto-generated from thread data                                                              │
│ Location: ops/                                                                               │
│                                                                                              │
│ ├─ today.md: Founder's 5-min daily review                                                    │
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
- 00-business-model-mode.md - VENTURE/BOOTSTRAP/HYBRID mode declaration
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

**Total:** 19 skills with 60+ sub-skills organized by type prefix

### Skill Categories

| Prefix | Count | Purpose |
|--------|-------|---------|
| `engineering-*` | 7 | System building & mathematical verification |
| `foundations-*` | 4 | Business setup, ICP, narratives |
| `ops-*` | 4 | Causal flow, dashboards, metrics |
| `research-*` | 2 | Mode-aware market research |
| `sales-*` | 1 | Sales pipeline execution |
| `marketing-*` | 1 | Campaign execution |

### Engineering Skills (7)

Full production flow with mathematical verification:

```
Requirements → Architecture → Maps → Code → Deployment
     ↓              ↓           ↓       ↓         ↓
  system-      backend-    standard-  frontend-  infrastructure-
  architecture  prover      applier    prover      prover
```

**Key innovations:**
- **Two-phase verification:** Generate maps first, verify composition, then generate code
- **Split standardization:** Define WHAT standards exist (definer), then HOW to apply (applier)
- **Proof composition:** All proofs must compose for deployment authorization

### Foundations Skills (4)

- **foundations-builder:** Orchestrate 10 agents for Canvas population
- **icp-generator:** Define ICP per segment
- **sales-narrative:** Generate sales messaging
- **marketing-narrative:** Generate content strategy

### Operations Skills (4)

- **causal-flow:** 6-stage decision framework (Input → Learning)
- **content-strategy:** Scan threads for campaign opportunities
- **ops-dashboard:** Auto-generate daily operations interface
- **business-metrics-tracker:** Mode-aware metrics dashboards

### Research Skills (2)

- **research-market-venture:** TAM, growth, defensibility (VENTURE mode)
- **research-market-bootstrap:** Spend mapping, arbitrage (BOOTSTRAP mode)

### Execution Skills (2)

- **sales-execution:** Materials, prospects, outreach, qualification
- **marketing-execution:** Content, SEO, distribution, tracking

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
- **Campaigns:** Campaign execution (`campaigns/{campaign-slug}/`)
- **Narratives:** Content strategy (`narrative/{product}/`)
- 6-stage flow with content-specific actions

### Engineering Threads
- Technical requirements (`{requirement}/`)
- 6-stage flow producing specifications for engineering skills

**Thread structure:**
```
threads/{type}/{name}/
├── meta.json
├── 1-input.md
├── 2-hypothesis.md
├── 3-implication.md
├── 4-decision.md
├── 5-actions/ (or 5-actions.md)
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
- **marketing/:** Published content (campaigns, blog, LinkedIn)
- **engineering/:** Generated code, configs, proofs

### engineering/ (Thread-driven)
- **specifications/:** Mathematical specs (versioned)
- **maps/:** Code maps (backend, shared contracts)
- **code/:** Generated code (backend, frontend)
- **configs/:** Deployment configs (Docker, K8s, CI/CD)
- **proofs/:** All verification proofs

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

**Engineering flow example:**

Business decision (build feature) → Engineering thread → system-architecture generates specs → backend-prover generates maps → maps verified → code generated → standardization applied → frontend-prover generates client → infrastructure-prover generates configs → proof-composer validates chain → deployment authorized

## Next Steps

- Learn the complete flow: [How It Works](how-it-works.md)
- See all skills: [All Skills](../skills/all-skills.md)
- Understand Canvas setup: [Canvas Setup](../foundation/canvas-setup.md)
- See timeline breakdown: [Timeline Guide](../foundation/timeline.md)
