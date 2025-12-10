# System Architecture

LeanOS operates in 6 layers: Strategy → Reasoning → Skills → Threads → Artifacts → Operations Dashboard.

## Architecture Diagram

```text
┌──────────────────────────────────────────────────────────────────────────────────────────────┐
│ STRATEGY LAYER                                                                               │
│ Source of Truth: Lean Canvas (15 living documents)                                           │
│ Location: strategy/canvas/                                                                   │
└──────────────────────────────────────────────────────────────────────────────────────────────┘
                                          ↓
┌──────────────────────────────────────────────────────────────────────────────────────────────┐
│ REASONING LAYER (Meta-Reasoning Gateway)                                                     │
│ Agent: .claude/agents/reasoning-gateway.md                                                   │
│ Skills: .claude/skills/reasoning-*                                                           │
│                                                                                              │
│ Routes non-trivial tasks to appropriate reasoning mode:                                      │
│                                                                                              │
│ ┌─────────────────────────────────────────────────────────────────────────────────────────┐  │
│ │ CAUSAL (enforced)     │ Operational execution, known processes → 6-stage thread flow   │  │
│ │ ABDUCTIVE             │ Anomaly diagnosis → "Why did X happen?"                        │  │
│ │ INDUCTIVE             │ Pattern detection → "This keeps happening"                     │  │
│ │ ANALOGICAL            │ Novel situations → "This is like..."                           │  │
│ │ DIALECTICAL           │ Stakeholder conflicts → Trade-off resolution                   │  │
│ │ COUNTERFACTUAL        │ Decision evaluation → "What if we had..."                      │  │
│ └─────────────────────────────────────────────────────────────────────────────────────────┘  │
│                                                                                              │
│ Causal mode is ENFORCED for operational threads (business, sales, marketing, engineering)   │
│ Other modes used for analysis/diagnosis, then chain to causal for action                    │
└──────────────────────────────────────────────────────────────────────────────────────────────┘
                                          ↓
┌──────────────────────────────────────────────────────────────────────────────────────────────┐
│ AGENTS + SKILLS LAYER (Domain Execution)                                                     │
│ Agents: .claude/agents/    Skills: .claude/skills/                                           │
│                                                                                              │
│ AGENTS (Orchestrators):                                                                      │
│ ┌─────────────────────────────────────────────────────────────────────────────────────────┐  │
│ │ reasoning-gateway      │ Routes to reasoning-* skills                                   │  │
│ │ foundations-builder    │ Routes to foundations-*, icp-generator                         │  │
│ │ sales-execution        │ Routes to sales-* skills                                       │  │
│ │ marketing-execution    │ Routes to marketing-* skills                                   │  │
│ └─────────────────────────────────────────────────────────────────────────────────────────┘  │
│                                                                                              │
│ SKILLS (Flat, single-capability):                                                            │
│ ┌─────────────────────────────────────────────────────────────────────────────────────────┐  │
│ │ reasoning-*     │ Reasoning modes (causal, abductive, inductive, etc)                  │  │
│ │ foundations-*   │ Canvas/business setup                                                │  │
│ │ sales-*         │ Sales pipeline                                                       │  │
│ │ marketing-*     │ Campaign execution                                                   │  │
│ │ ops-*           │ Operations (dashboard, metrics)                                       │  │
│ │ research-*      │ Market research                                                       │  │
│ │ engineering/    │ Internal pipeline (nested)                                            │  │
│ └─────────────────────────────────────────────────────────────────────────────────────────┘  │
│                                                                                              │
│ STANDALONE SKILLS (No Agent):                                                                │
│ ┌─────────────────────────────────────────────────────────────────────────────────────────┐  │
│ │ sales-narrative        │ Sales messaging per segment                                    │  │
│ │ marketing-narrative    │ Brand identity, content patterns                               │  │
│ │ content-generation     │ Create content (any context)                                   │  │
│ └─────────────────────────────────────────────────────────────────────────────────────────┘  │
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
│ ARTIFACTS LAYER (Deliverables)                                                               │
│ Published outputs from thread execution                                                      │
│ Location: artifacts/                                                                         │
│                                                                                              │
│ ├─ sales/: Pitch decks, scripts, templates per segment                                       │
│ ├─ marketing/: Published content (campaigns, blog, social)                                   │
│ └─ engineering/: Specifications, code, configs, proofs                                       │
│     ├─ specifications/: Mathematical specs (versioned)                                       │
│     ├─ maps/: Code structure maps                                                            │
│     ├─ code/: Generated backend/frontend code                                                │
│     ├─ configs/: Docker, K8s, CI/CD                                                          │
│     └─ proofs/: Verification certificates                                                    │
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

## Layer 2: Reasoning (Meta-Reasoning Gateway)

**Agent:** `.claude/agents/reasoning-gateway.md`
**Skills:** `.claude/skills/reasoning-*/`

**Purpose:** Route non-trivial tasks to appropriate reasoning mode

### Reasoning Modes

| Mode | Use When | Output |
|------|----------|--------|
| **Causal** | Operational execution (enforced for threads) | 6-stage thread |
| **Abductive** | Anomaly diagnosis | Root cause hypothesis |
| **Inductive** | Pattern detection | Validated pattern/rule |
| **Analogical** | Novel situation | Adapted playbook |
| **Dialectical** | Stakeholder conflict | Synthesis decision |
| **Counterfactual** | Decision evaluation | Learning + recommendation |

### Flow

```
Task arrives → Gateway selects mode → Mode executes → (chains to causal if action needed)
```

**Enforced flows:** Operational threads (business, sales, marketing, engineering) always use causal mode.

## Layer 3: Agents + Skills (Domain Execution)

**Agents:** `.claude/agents/`
**Skills:** `.claude/skills/`

### Agents (Orchestrators)

| Agent | Purpose | Skills Loaded |
|-------|---------|---------------|
| `reasoning-gateway` | Route to reasoning modes | reasoning-* |
| `foundations-builder` | Canvas population | foundations-*, icp-generator |
| `sales-execution` | Sales pipeline | sales-* |
| `marketing-execution` | Campaign execution | marketing-* |

### Skills (Flat, single-capability)

| Category | Purpose |
|----------|---------|
| `reasoning-*` | Reasoning modes (causal, abductive, etc.) |
| `foundations-*` | Canvas/business setup |
| `sales-*` | Sales pipeline |
| `marketing-*` | Campaign execution |
| `ops-*` | Operations (dashboard, metrics) |
| `research-*` | Market research |
| `engineering/` | Internal pipeline (nested) |

### Standalone Skills (No Agent)

| Skill | Purpose |
|-------|---------|
| `sales-narrative` | Sales messaging per segment |
| `marketing-narrative` | Brand identity, content patterns |
| `content-generation` | Create content (any context) |

## Layer 4: Threads (Decision Storage)

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

## Layer 5: Artifacts (Deliverables)

**Location:** `artifacts/`

**Purpose:** Published outputs from thread execution

### Sales Artifacts
- Pitch decks, one-pagers per segment
- Call scripts, email templates
- Pilot agreements, contracts

### Marketing Artifacts
- Published blog posts, case studies
- Social media content
- Campaign performance records

### Engineering Artifacts
- `specifications/`: Mathematical specs (versioned, immutable)
- `maps/`: Code structure maps (backend, shared)
- `code/`: Generated code (backend, frontend)
- `configs/`: Deployment (Docker, K8s, CI/CD)
- `proofs/`: Verification certificates

## Layer 6: Operations Dashboard

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

## Data Flow

**Reasoning-first flow:**

```
Task arrives
    ↓
Reasoning Gateway (mode selection)
    ↓
┌─────────────────────────────────────────────────────┐
│ Abductive/Inductive/Analogical/Dialectical/         │
│ Counterfactual (analytical modes)                   │
│     ↓                                               │
│ Output: hypothesis, pattern, playbook, synthesis    │
│     ↓                                               │
│ Chain to Causal if action needed                    │
└─────────────────────────────────────────────────────┘
    ↓
Causal Mode (6-stage execution)
    ↓
Thread created → Actions executed → Learning captured → Canvas updated
    ↓
ops/today.md reflects result
```

**Enforced operational flow:**

Operational threads (business, sales, marketing, engineering) skip gateway selection and use causal mode directly:

```
Operational trigger → Causal mode → 6-stage thread → Learning → Canvas update
```

**Closed-loop example:**

Sales thread → Learning (Stage 6) → Canvas updated → Marketing scans → Content opportunity → Marketing thread → Published → Traffic → Demos → Sales threads → Loop continues

## Operational Flows

### Enforced Flows (Always Causal)

Operational threads use causal mode with 6-stage flow:

| Thread Type | Trigger | Output |
|-------------|---------|--------|
| Business | Strategic decision, feedback | Canvas update |
| Sales | Lead, referral | Pipeline tracking |
| Marketing | Opportunity detected | Campaign execution |
| Engineering | Build decision | Specifications |

### Impact-Based Autonomy

| Impact Score | Action |
|--------------|--------|
| < 0.8 | Auto-execute, log in thread |
| ≥ 0.8 | Flag in `ops/today.md`, wait for approval |
| Customer calls | Always human |
| Canvas-altering | Always require approval |

### Closed-Loop System

```
Sales thread completes (Stage 6)
    ↓
Learning captured → Canvas updated
    ↓
Content strategy scans → opportunity detected
    ↓
Marketing thread created → Content published
    ↓
Traffic → Demos → Sales threads → Loop continues
```

---

## Next Steps

- See all skills: [All Skills](all-skills.md)
- Understand Canvas setup: [Canvas Setup](../workflows/canvas-setup.md)
- Learn workflows: [Sales](../workflows/sales-workflow.md) | [Marketing](../workflows/marketing-workflow.md) | [Engineering](../workflows/engineering-workflow.md)
