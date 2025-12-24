# System Architecture

LeanOS operates in 7 layers: Goals → Strategy → Reasoning → Skills → Threads → Artifacts → State.

## Operating Model

**Goal-driven (primary):** All work flows from declared objectives
```
Goal → Plan → Threads → Artifacts → Learning → Canvas
```

**Reactive (fallback):** Handles unexpected signals, links back to goals
```
Signal → Thread → Link to Goal (or create new goal)
```

## Architecture Diagram

```text
┌──────────────────────────────────────────────────────────────────────────────────────────────┐
│ GOALS LAYER (Primary Operating Mode)                                                         │
│ Declared objectives that drive all work                                                      │
│ Location: strategy/goals/                                                                    │
│                                                                                              │
│ ├─ active/: Current objectives with plans                                                    │
│ ├─ completed/: Achieved goals (archive)                                                      │
│ └─ abandoned/: Dropped goals (archive)                                                       │
│                                                                                              │
│ Goal Structure: Objective → Success Criteria → Plan (Subgoals + Milestones) → State          │
│ Skills: goal-setter (creates goals), goal-tracker (derives state)                            │
│ Autonomy: auto | ask | hybrid (configurable per goal)                                        │
└──────────────────────────────────────────────────────────────────────────────────────────────┘
                                          ↓
┌──────────────────────────────────────────────────────────────────────────────────────────────┐
│ STRATEGY LAYER                                                                               │
│ Source of Truth: Lean Canvas (15 living documents)                                           │
│ Location: strategy/canvas/                                                                   │
│                                                                                              │
│ Goals READ Canvas for context (assumptions, constraints, segments)                           │
│ Learning WRITES to Canvas (feedback loop from completed threads)                             │
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
│ AGENTS (Orchestrators - 13 total):                                                           │
│ ┌─────────────────────────────────────────────────────────────────────────────────────────┐  │
│ │ lean-os                │ Main engineering orchestrator (SPEC→BUILD→VERIFY→GEN)         │  │
│ │ lean-os-spec           │ SPEC phase: engineering-spec-* skills                         │  │
│ │ lean-os-build          │ BUILD phase: engineering-build-* skills                       │  │
│ │ lean-os-verify         │ VERIFY phase: engineering-verify-* skills                     │  │
│ │ lean-os-gen            │ GEN phase: engineering-gen-*, apply-standards                 │  │
│ │ problem-solving-gateway│ Routes to action-* skills (deliverable contracts)             │  │
│ │ reasoning-gateway      │ Routes to reasoning-* skills                                  │  │
│ │ foundations-builder    │ Routes to foundations-* skills                                │  │
│ │ sales-execution        │ Routes to sales-* skills                                      │  │
│ │ marketing-execution    │ Routes to marketing-* skills                                  │  │
│ │ product-builder        │ Routes to product-* skills (Canvas → eng specs)               │  │
│ │ market-research        │ Routes to research-market-* skills (mode-aware)               │  │
│ │ knowledge-builder      │ Routes to research-source/playbook-* skills                   │  │
│ └─────────────────────────────────────────────────────────────────────────────────────────┘  │
│                                                                                              │
│ SKILLS (Flat, single-capability - 70 total):                                                 │
│ ┌─────────────────────────────────────────────────────────────────────────────────────────┐  │
│ │ action-*        │ Action skills - deliverable contracts (11)                           │  │
│ │ engineering-*   │ Categorical verification pipeline (20)                               │  │
│ │ foundations-*   │ Canvas/business setup (10)                                           │  │
│ │ goal-*          │ Goal setting and tracking (2)                                        │  │
│ │ marketing-*     │ Campaign execution (5)                                               │  │
│ │ product-*       │ Product requirements to specifications (5)                           │  │
│ │ reasoning-*     │ Reasoning modes (6)                                                  │  │
│ │ research-*      │ Market research and knowledge synthesis (5)                          │  │
│ │ sales-*         │ Sales pipeline (6)                                                   │  │
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
│ ├─ product/: Requirements, flows, wireframes, specs                                          │
│ └─ engineering/: Specifications, code, configs, proofs                                       │
│     ├─ specifications/: Mathematical specs (versioned)                                       │
│     ├─ maps/: Code structure maps                                                            │
│     ├─ code/: Generated backend/frontend code                                                │
│     ├─ configs/: Docker, K8s, CI/CD                                                          │
│     └─ proofs/: Verification certificates                                                    │
└──────────────────────────────────────────────────────────────────────────────────────────────┘
                                          ↓
┌──────────────────────────────────────────────────────────────────────────────────────────────┐
│ STATE LAYER (Derived, On-Demand)                                                             │
│ State is computed from goals + threads, not stored separately                                │
│                                                                                              │
│ Goal state: Derived by goal-tracker from linked threads                                      │
│ Snapshot: Computed on-demand (no daily file needed)                                          │
│ Metrics: Aggregated from thread Stage 6 (Learning)                                           │
│                                                                                              │
│ ops/ directory (supporting files):                                                           │
│ ├─ changes.md: Strategic changelog                                                           │
│ └─ patterns.md: Cross-goal pattern detection                                                 │
└──────────────────────────────────────────────────────────────────────────────────────────────┘
```

## Layer 1: Goals (Primary Operating Mode)

**Location:** `strategy/goals/`

**Purpose:** Declared objectives that drive all work

**Structure:**
```
strategy/goals/
├── active/           # Current objectives
│   └── g-{name}.md   # Goal file with plan + state
├── completed/        # Achieved goals (archive)
└── abandoned/        # Dropped goals (archive)
```

**Goal file schema:**
```markdown
---
id: g-{kebab-case-name}
type: business | brand | product | learning | custom
status: active
autonomy: auto | ask | hybrid
deadline: YYYY-MM-DD
---

# {Goal Title}

## Objective
{What you want to achieve}

## Success Criteria
- [ ] {Measurable criterion}

## Plan
### Subgoals
- SG1: {subgoal} → threads: {linked threads}
### Milestones
- M1: {checkpoint} (by {date})

## State (derived by goal-tracker)
| Metric | Current | Target | Gap | Trend |
```

**Skills:**
- `goal-setter`: Creates goals from objectives, reads Canvas for context
- `goal-tracker`: Derives state from threads, computes gaps/trajectory

**Autonomy modes:**
| Mode | Behavior |
|------|----------|
| `auto` | AI creates threads and executes without asking |
| `ask` | AI recommends, waits for approval |
| `hybrid` | Auto for impact <0.5, ask for ≥0.5 |

---

## Layer 2: Strategy (Source of Truth)

**Location:** `strategy/canvas/`

**Contents:** 15 living Lean Canvas documents

**Purpose:** Strategic context for goals, updated by learning

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

**Relationship to Goals:**
- Goals READ Canvas for strategic context
- Learning WRITES to Canvas (validates/invalidates assumptions)

---

## Layer 3: Reasoning (Meta-Reasoning Gateway)

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

---

## Layer 4: Agents + Skills (Domain Execution)

**Agents:** `.claude/agents/`
**Skills:** `.claude/skills/`

### Agents (Orchestrators - 13)

| Agent | Purpose | Skills Loaded |
|-------|---------|---------------|
| `lean-os` | Main engineering orchestrator | Routes to phase agents |
| `lean-os-spec` | SPEC phase | engineering-spec-* |
| `lean-os-build` | BUILD phase | engineering-build-* |
| `lean-os-verify` | VERIFY phase | engineering-verify-* |
| `lean-os-gen` | GEN phase | engineering-gen-*, apply-standards |
| `problem-solving-gateway` | Action skill routing | action-* |
| `reasoning-gateway` | Reasoning mode routing | reasoning-* |
| `foundations-builder` | Canvas population | foundations-* |
| `sales-execution` | Sales pipeline | sales-* |
| `marketing-execution` | Campaign execution | marketing-* |
| `product-builder` | Product design to eng specs | product-* |
| `market-research` | Mode-aware market analysis | research-market-*, reasoning-inductive |
| `knowledge-builder` | Knowledge synthesis | research-source/playbook-*, reasoning-inductive |

### Skills (Flat, single-capability - 70)

| Category | Count | Purpose |
|----------|-------|---------|
| `action-*` | 11 | Action skills (deliverable contracts) |
| `engineering-*` | 20 | Categorical verification pipeline |
| `foundations-*` | 10 | Canvas/business setup |
| `goal-*` | 2 | Goal setting and tracking |
| `marketing-*` | 5 | Campaign execution |
| `product-*` | 5 | Product requirements to specifications |
| `reasoning-*` | 6 | Reasoning modes |
| `research-*` | 5 | Market research and knowledge synthesis |
| `sales-*` | 6 | Sales pipeline |

---

## Layer 5: Threads (Decision Storage)

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

**Relationship to Goals:**
- Threads are linked to goals via subgoals
- Thread completion updates goal state
- Thread Stage 6 (Learning) feeds back to Canvas

---

## Layer 6: Artifacts (Deliverables)

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

### Product Artifacts
- `requirements/`: User stories, story maps, PRDs
- `flows/`: Journey maps, flow diagrams, state diagrams
- `wireframes/`: Component specs, layouts, inventories
- `prioritization/`: DHM scores, stack ranks, LNO classifications
- `specs/`: Shaped pitches, engineering specifications

### Engineering Artifacts
- `specifications/`: Mathematical specs (versioned, immutable)
- `maps/`: Code structure maps (backend, shared)
- `code/`: Generated code (backend, frontend)
- `configs/`: Deployment (Docker, K8s, CI/CD)
- `proofs/`: Verification certificates

---

## Layer 7: State (Derived, On-Demand)

**Purpose:** State is computed, not stored. Goals track their own state.

**Key principle:** No daily file needed. Snapshot computed on-demand by `goal-tracker`.

**State derivation:**
```
goal-tracker reads:
  - Goal files (objectives, success criteria)
  - Linked threads (execution state)
  - Thread Stage 6 (Learning outcomes)
  ↓
Computes:
  - Current metrics vs targets
  - Gap analysis
  - Trajectory projection
  - Risk level
  ↓
Updates:
  - Goal state section
  - Recommendations for action
```

**Supporting files in `ops/`:**
- `changes.md`: Strategic changelog
- `patterns.md`: Cross-goal pattern detection

## Supporting Directories

### research/
- **customer/icp/:** ICP definitions per segment
- **customer/prospects/:** Prospect and contact lists
- **sources/:** Processed expert content (insights.md per source)
- **playbooks/:** Actionable playbooks by domain
- **synthesis/:** Cross-source synthesis frameworks
- **market/:** Market analysis outputs

## Data Flow

**Goal-driven flow (primary):**

```
User declares objective
    ↓
goal-setter (reads Canvas for context)
    ↓
Goal created with plan (subgoals, milestones)
    ↓
Subgoals spawn threads (based on autonomy mode)
    ↓
Threads execute (6-stage causal flow)
    ↓
Learning → Canvas updated
    ↓
goal-tracker derives state from threads
    ↓
Gap detected → New threads or recommendations
    ↓
Goal completed → Move to completed/
```

**Reactive flow (fallback):**

```
Signal arrives (feedback, anomaly, external trigger)
    ↓
Reasoning Gateway selects mode
    ↓
Thread created → Prompt: "Link to goal or create new goal?"
    ↓
6-stage execution → Learning → Canvas update
```

**Closed-loop:**

```
Goal → Subgoals → Threads → Artifacts → Learning → Canvas
                     ↑                              ↓
                     └────── gap-closing actions ───┘
```

## Operational Flows

### Goal-Driven Execution

All work should be linked to a goal:

| Trigger | Flow |
|---------|------|
| User objective | goal-setter → Goal → Subgoals → Threads |
| Subgoal activation | Thread created, linked to goal |
| Thread completion | goal-tracker updates goal state |
| Gap detected | New thread or recommendation (based on autonomy) |

### Autonomy Modes

| Mode | Thread Impact < 0.5 | Thread Impact ≥ 0.5 |
|------|---------------------|---------------------|
| `auto` | Auto-execute | Auto-execute |
| `ask` | Ask user | Ask user |
| `hybrid` | Auto-execute | Ask user |

### Reactive (Fallback)

For signals not covered by existing goals:

```
Signal → Thread → "Link to goal or create new goal?"
```

Options:
1. Link to existing goal's subgoals
2. Create new goal (invokes goal-setter)
3. Execute as standalone thread (discouraged)

---

## Next Steps

- See all skills: [All Skills](all-skills.md)
- Understand Canvas setup: [Canvas Setup](../workflows/canvas-setup.md)
- Learn workflows: [Sales](../workflows/sales-workflow.md) | [Marketing](../workflows/marketing-workflow.md) | [Engineering](../workflows/engineering-workflow.md)
