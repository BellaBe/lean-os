# LeanOS Skills Reference

Complete reference of AI skills for business operations.

## Skill Organization (v2.0)

| Category | Purpose |
|----------|---------|
| `reasoning-gateway/` | Meta-reasoning with 6 modes (routes all non-trivial tasks) |
| `engineering/` | System building with categorical verification |
| `foundations-*` | Business setup, ICP, narratives |
| `ops-*` | Dashboards, metrics, content strategy |
| `research-*` | Mode-aware market research |
| `sales-execution` | Sales pipeline management |
| `marketing-execution` | Campaign execution |

---

## Reasoning Gateway (6 modes)

**Purpose:** Route non-trivial tasks to appropriate reasoning mode

**Skill:** `.claude/skills/reasoning-gateway/SKILL.md`

| Mode | Use When | Skill |
|------|----------|-------|
| **Causal** | Operational execution, known processes | `stages/reasoning-causal/` |
| **Abductive** | Anomaly diagnosis, "why did X happen?" | `stages/reasoning-abductive/` |
| **Inductive** | Pattern detection, "this keeps happening" | `stages/reasoning-inductive/` |
| **Analogical** | Novel situations, "this is like..." | `stages/reasoning-analogical/` |
| **Dialectical** | Stakeholder conflicts, trade-offs | `stages/reasoning-dialectical/` |
| **Counterfactual** | Decision evaluation, "what if..." | `stages/reasoning-counterfactual/` |

**Causal mode** (enforced for threads) includes:
- 6 stage sub-skills (input, hypothesis, implication, decision, actions, learning)
- Thread references (business, sales, marketing, engineering)
- Action templates (sales, marketing)

---

## Engineering Skills

Full production flow: Requirements → Architecture → Maps → Code → Deployment

### system-architecture (9 sub-skills)
**Purpose:** Transform natural language requirements into mathematically verified specifications
**Input:** `threads/engineering/{requirement}/` (6-stage causal flow)
**Output:** `artifacts/engineering/specifications/v{X}/`

**Sub-skills:**
1. `adt-analyzer` - Parse requirements into algebraic expressions
2. `algebraic-structure-validator` - Validate algebraic laws
3. `functor-generator` - Generate functors for patterns
4. `natural-transformation-engine` - Version migrations
5. `curry-howard-prover` - Type proofs via Curry-Howard
6. `system-optimizer` - Apply algebraic laws for optimization
7. `architecture-validator` - Validate categorical laws (10K tests)
8. `state-machine-validator` - Validate state transitions
9. `version-compatibility-prover` - Prove backward compatibility

### backend-prover (4 sub-skills)
**Purpose:** Generate verified backend code through two-phase architecture
**Input:** Specifications + shared contracts
**Output:** `artifacts/engineering/code/backend/`

**Phase 1 (Maps):**
1. `code-map-generator` - Generate structural specifications
2. `composition-map-validator` - Verify composition laws on maps

**Phase 2 (Code):**
3. `code-implementation-generator` - Generate code from verified maps
4. `runtime-monitor-generator` - Generate runtime validators

### frontend-prover (4 sub-skills)
**Purpose:** Generate type-safe frontend matching backend API
**Input:** `api.openapi.json`
**Output:** `artifacts/engineering/code/frontend/`

**Sub-skills:**
1. `openapi-parser` - Parse OpenAPI schema
2. `typescript-generator` - Generate TypeScript interfaces
3. `framework-adapter` - Generate framework-specific code (Remix, React, Vue)
4. `type-correspondence-prover` - Prove bijection with backend types

### infrastructure-prover (5 sub-skills)
**Purpose:** Generate deployment configs with topology proofs
**Input:** `services.spec.yaml`
**Output:** `artifacts/engineering/configs/`

**Sub-skills:**
1. `service-topology-analyzer` - Extract service dependencies
2. `docker-generator` - Generate Dockerfiles and compose
3. `kubernetes-generator` - Generate K8s manifests
4. `ci-cd-generator` - Generate GitHub Actions workflows
5. `topology-prover` - Prove deployment isomorphic to spec

### standardization-definer
**Purpose:** Extract cross-cutting concerns from specs, generate contracts
**When:** BEFORE backend code generation
**Output:** `artifacts/engineering/maps/shared/` (contracts)

Defines WHAT standards exist (auth, validation, responses, rate limiting, observability).

### standardization-applier
**Purpose:** Apply standards to generated code, verify naturality
**When:** AFTER backend code generation
**Output:** Modified backend code + naturality proofs

Applies HOW standards are injected while preserving composition laws.

### proof-composer
**Purpose:** Validate entire proof chain composes correctly
**Input:** All proofs from all engineering skills
**Output:** `artifacts/engineering/proofs/composed/system-proof.certificate`

**Deployment gate:** Certificate must be valid for deployment authorization.

---

## Foundations Skills (4 skills)

Business setup and strategy definition.

### foundations-builder (10 agents)
**Purpose:** Orchestrate Canvas population through 5 phases
**Phases:** Discovery → Definition → Validation → Execution → Launch
**Output:** Complete 15-section Canvas

**Core Agents (7):**
- `market-intelligence` → Canvas 01-04, 06
- `problem-solution-fit` → Canvas 05, 09, 10
- `value-proposition` → Canvas 07-08
- `business-model` → Canvas 11-13
- `validation` → Canvas 10 (status)
- `go-to-market` → Canvas 14-15 (produces `strategy/canvas/15.go-to-market.md`)
- `execution` → Task orchestration

**Specialist Agents (3, on-demand):**
- `funding` - Fundraising strategy
- `regulatory` - Compliance navigation
- `retention-optimizer` - Post-launch retention

**Key subskill: go-to-market**
Generates GTM strategy that all downstream marketing skills read. Determines motion type (PLG, Content-Led, Partner-Led, SLG) and channel priorities. Single source of truth for acquisition strategy.

**Docs:** See [Canvas Setup](../foundation/canvas-setup.md)

### icp-generator
**Purpose:** Define Ideal Customer Profile per segment
**Input:** Canvas 04-segments.md
**Output:** `research/customer/icp/{segment}-icp.yaml`

Generates observable characteristics, qualification questions, and prospecting tool mappings.

### sales-narrative
**Purpose:** Generate sales messaging per segment
**Input:** Canvas + ICP
**Output:** `artifacts/sales/{segment}/narratives/`

Creates persona-specific problem-solution-specifics narratives for buyers.

### marketing-narrative
**Purpose:** Generate brand identity and content patterns (channel-agnostic)
**Input:** Canvas (segments, problem, UVP, advantage, solution)
**Output:** `artifacts/marketing/narrative/`

**Generates:**
- `brand-voice.md` - Tone and style
- `positioning.md` - What we stand for
- `content-pillars.md` - 3-5 strategic themes
- `patterns/` - Content structure templates (insight, tutorial, case-study, story)

**Note:** Channel-agnostic. Does not determine channels (→ GTM) or loop mechanics (→ content-generation).

---

## Operations Skills (3 skills)

Operational dashboards and monitoring.

### content-strategy
**Purpose:** Motion-aware content discovery and opportunity detection
**Schedule:** Daily automated scan
**Reads:** `strategy/canvas/15.go-to-market.md` (for motion type)
**Output:** Prioritized opportunities in `ops/today.md`

**Motion-aware scoring:**
- **Loop-Driven (PLG, Content-Led):** Loop Potential × Velocity Story × Audience Alignment
- **Marketplace-Driven (Partner-Led):** Review Potential × Install Impact × Retention Value
- **Sales-Driven (SLG):** Deal Enablement × Objection Coverage × Stage Fit

**Thresholds:** ≥0.7 flag immediately, 0.5-0.7 backlog, <0.5 skip

### ops-dashboard
**Purpose:** Auto-generate daily operations interface
**Output:** `ops/today.md`, `ops/velocity.md`, `ops/patterns.md`, `ops/changes.md`
**Schedule:** Daily automated

### business-metrics-tracker
**Purpose:** Generate mode-aware business metrics dashboards
**Output:** `artifacts/business/metrics.md`

**VENTURE mode metrics:** MAU, ARR, market share, runway, CAC, LTV
**BOOTSTRAP mode metrics:** MRR, profit, cash flow, margins

---

## Research Skills (2 skills)

Mode-aware market research.

### research-market-venture
**Purpose:** Venture-focused market analysis
**Mode:** VENTURE only
**Output:** `research/market/venture-analysis-{date}.md`

**Key analyses:**
- Total Addressable Market (TAM/SAM/SOM)
- Market growth rate (CAGR projections)
- Competitive positioning
- Defensibility & moat assessment
- 10x opportunity validation

### research-market-bootstrap
**Purpose:** Bootstrap-focused market analysis
**Mode:** BOOTSTRAP only
**Output:** `research/market/bootstrap-analysis-{date}.md`

**Key analyses:**
- Who pays what today (spend mapping)
- Budget holder identification
- Pricing intelligence & arbitrage
- Procurement process analysis
- Q1 revenue potential

**Selection:** Check `strategy/canvas/00-business-model-mode.md` to determine which skill to use.

---

## Sales Skills (1 skill, 5 sub-skills)

### sales-execution (orchestrator)
**Purpose:** Orchestrate sales workflow
**Output:** `artifacts/sales/{segment}/`

**Sub-skills:**
1. `materials-generation` - Pitch decks, scripts, templates
2. `prospect-research` - Find target companies (web search)
3. `contact-finding` - Find decision-makers
4. `outreach-sequencing` - Email/phone cadences
5. `qualification-support` - Discovery call prep

---

## Marketing Skills (1 skill, 3 sub-skills)

### marketing-execution (orchestrator, motion-aware)
**Purpose:** Orchestrate campaign execution (Stage 5 only)
**Reads:** `strategy/canvas/15.go-to-market.md` (detects mode once, passes to subskills)
**Output:** `artifacts/marketing/campaigns/{campaign-slug}/`

**Modes:**
- **Loop-Driven (PLG, Content-Led):** Loop triggers, velocity proof, first-comment
- **Marketplace-Driven (Partner-Led):** Reviews, ratings, store presence
- **Sales-Driven (SLG):** Pipeline attribution, enablement, objection handling

**Sub-skills:**
1. `content-generation` - Create content (receives mode from orchestrator)
2. `content-delivery` - Publish + track (receives mode from orchestrator)
3. `channel-optimization` - Optimize channel performance

**Composition pattern:** Orchestrator detects mode ONCE, subskills receive mode as parameter (do NOT read GTM).

---

## Skill Discovery

**By function:**
- Need to reason through a problem? → `reasoning-gateway/`
- Building systems? → `engineering/`
- Setting up business? → `foundations-*`
- Daily operations? → `ops-*`
- Market research? → `research-*`
- Sales pipeline? → `sales-execution`
- Marketing campaigns? → `marketing-execution`

---

## Related Documentation

- [Architecture Overview](../overview/architecture.md)
- [Sales Workflow](../operations/sales-workflow.md)
- [Marketing Workflow](../operations/marketing-workflow.md)
- [Causal Flow](../operations/causal-flow.md)
- [Canvas Setup](../foundation/canvas-setup.md)
