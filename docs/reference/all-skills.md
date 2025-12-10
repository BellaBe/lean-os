# LeanOS Skills Reference

Complete reference of AI skills and agents for business operations.

## Architecture (v2.2 - Goal-Oriented)

| Component | Purpose |
|-----------|---------|
| **Agents** (`.claude/agents/`) | Orchestrators that route to skills |
| **Skills** (`.claude/skills/`) | Flat, single-capability instructions |

### Agents (4)

| Agent | Purpose | Skills Loaded |
|-------|---------|---------------|
| `reasoning-gateway` | Route non-trivial tasks to reasoning modes | 6 reasoning-* skills |
| `foundations-builder` | Orchestrate Canvas population | 9 foundations-* skills |
| `sales-execution` | Route sales activities | 5 sales-* skills |
| `marketing-execution` | Route campaign execution | 3 marketing-* skills |

### Skills by Category

| Prefix | Count | Purpose |
|--------|-------|---------|
| `goal-*` | 2 | Goal setting and tracking (primary operating mode) |
| `reasoning-*` | 6 | Reasoning modes (causal, abductive, etc.) |
| `foundations-*` | 9 | Business setup, Canvas sections |
| `sales-*` | 5 | Sales pipeline activities |
| `marketing-*` | 3 | Campaign execution |
| `ops-*` | 1 | Content strategy |
| `research-*` | 1 | Mode-aware market research |
| `engineering/` | 1 | Categorical verification (nested, internal) |

---

## Agents

### reasoning-gateway

**Location:** `.claude/agents/reasoning-gateway.md`

**Purpose:** Route non-trivial tasks to appropriate reasoning mode

| Mode | When to Use |
|------|-------------|
| **Causal** | Operational execution, known processes (enforced for threads) |
| **Abductive** | Anomaly diagnosis, "why did X happen?" |
| **Inductive** | Pattern detection, "this keeps happening" |
| **Analogical** | Novel situations, "this is like..." |
| **Dialectical** | Stakeholder conflicts, trade-offs |
| **Counterfactual** | Decision evaluation, "what if we had..." |

**Skills loaded:** reasoning-causal, reasoning-abductive, reasoning-inductive, reasoning-analogical, reasoning-dialectical, reasoning-counterfactual

---

### foundations-builder

**Location:** `.claude/agents/foundations-builder.md`

**Purpose:** Orchestrate Canvas population through 5 phases

**Phases:** Discovery → Definition → Validation → Execution → Launch

**Output:** Complete 15-section Canvas

| Skill | Canvas Sections |
|-------|-----------------|
| `foundations-market-intelligence` | 01-04, 06 |
| `foundations-problem-solution-fit` | 05, 09, 10 |
| `foundations-value-proposition` | 07-08 |
| `foundations-business-model` | 11-13 |
| `foundations-validation` | 10 (status) |
| `foundations-go-to-market` | 14-15 |
| `foundations-funding` | Fundraising (on-demand) |
| `foundations-regulatory` | Compliance (on-demand) |
| `foundations-retention-optimizer` | Post-launch retention (on-demand) |

**Docs:** See [Canvas Setup](../workflows/canvas-setup.md)

---

### sales-execution

**Location:** `.claude/agents/sales-execution.md`

**Purpose:** Orchestrate sales workflow by activity type

**Output:** `artifacts/sales/{segment}/`

| Activity Type | Skill |
|---------------|-------|
| materials | `sales-materials-generation` |
| prospecting | `sales-prospect-research` |
| contact-finding | `sales-contact-finding` |
| outreach | `sales-outreach-sequencing` |
| qualification | `sales-qualification-support` |

---

### marketing-execution

**Location:** `.claude/agents/marketing-execution.md`

**Purpose:** Orchestrate campaign execution (motion-aware)

**Reads:** `strategy/canvas/15.go-to-market.md`

**Output:** `artifacts/marketing/campaigns/{campaign-slug}/`

| Activity Type | Skill |
|---------------|-------|
| content | `marketing-content-generation` |
| delivery | `marketing-content-delivery` |
| optimization | `marketing-channel-optimization` |

**Modes:**
- **Loop-Driven (PLG, Content-Led):** Loop triggers, velocity proof
- **Marketplace-Driven (Partner-Led):** Reviews, ratings, store presence
- **Sales-Driven (SLG):** Pipeline attribution, enablement

---

## Goal Skills (2)

Goals are the **primary operating mode** for LeanOS. All work should be goal-driven.

| Skill | Purpose | Input | Output |
|-------|---------|-------|--------|
| `goal-setter` | Transform objectives into structured goals | User intent + Canvas context | `strategy/goals/active/{id}.md` |
| `goal-tracker` | Derive state from execution, track progress | Goal + Threads | Updated goal state, recommendations |

### goal-setter

**Trigger:** User expresses intent ("I want to...", "Goal is to...", "Achieve X by Y")

**Process:**
1. Capture objective (what, why, when)
2. Read Canvas for strategic context
3. Define success criteria (measurable)
4. Decompose into subgoals + milestones
5. Set autonomy level (auto/ask/hybrid)

**Output:** Goal file with plan structure

### goal-tracker

**Trigger:** Status check, thread completion, periodic review

**Process:**
1. Load goal and linked threads
2. Derive metrics from thread outcomes
3. Calculate gap to targets
4. Project trajectory
5. Generate recommendations or auto-create threads

**Output:** Updated goal state section, action recommendations

---

## Reasoning Skills (6)

| Skill | Purpose | When to Use |
|-------|---------|-------------|
| `reasoning-causal` | Execute known processes with 6-stage flow | Operational execution, threads |
| `reasoning-abductive` | Diagnose anomalies, form hypotheses | "Why did X happen?" |
| `reasoning-inductive` | Detect patterns, generalize from examples | "This keeps happening" |
| `reasoning-analogical` | Transfer knowledge across domains | "This is like..." |
| `reasoning-dialectical` | Resolve conflicts through synthesis | Stakeholder disagreements |
| `reasoning-counterfactual` | Evaluate decisions via alternatives | "What if we had..." |

**Causal mode** (enforced for threads) includes:
- 6 stage references (input, hypothesis, implication, decision, actions, learning)
- Thread references (business, sales, marketing, engineering)
- Action templates (sales, marketing)

---

## Foundations Skills (9)

| Skill | Purpose | Canvas Sections |
|-------|---------|-----------------|
| `foundations-market-intelligence` | Market size, competitive landscape | 01-04, 06 |
| `foundations-problem-solution-fit` | Problem validation, solution fit | 05, 09, 10 |
| `foundations-value-proposition` | UVP and unfair advantage | 07-08 |
| `foundations-business-model` | Revenue streams, cost structure | 11-13 |
| `foundations-validation` | Assumption tracking and validation | 10 (status) |
| `foundations-go-to-market` | GTM strategy, motion selection | 14-15 |
| `foundations-funding` | Fundraising strategy | On-demand |
| `foundations-regulatory` | Compliance navigation | On-demand |
| `foundations-retention-optimizer` | Post-launch retention | On-demand |

**Related skills (not part of agent):**

| Skill | Purpose |
|-------|---------|
| `foundations-icp-generator` | ICP per segment from Canvas 04 |
| `foundations-sales-narrative` | Sales messaging per segment |
| `foundations-marketing-narrative` | Brand identity and content patterns |

---

## Sales Skills (5)

| Skill | Purpose | Output |
|-------|---------|--------|
| `sales-materials-generation` | Pitch decks, scripts, templates | `artifacts/sales/{segment}/materials/` |
| `sales-prospect-research` | Find target companies | `research/customer/prospects/` |
| `sales-contact-finding` | Find decision-makers | Contact lists |
| `sales-outreach-sequencing` | Email/phone cadences | Sequence templates |
| `sales-qualification-support` | Discovery call prep | Qualification guides |

---

## Marketing Skills (3)

| Skill | Purpose | Output |
|-------|---------|--------|
| `marketing-content-generation` | Create content (receives mode) | Content drafts |
| `marketing-content-delivery` | Publish + track | Published content |
| `marketing-channel-optimization` | Optimize channel performance | Optimization reports |

**Composition pattern:** Agent detects mode ONCE, skills receive mode as parameter (do NOT read GTM).

---

## Operations Skills (1)

| Skill | Purpose | Output |
|-------|---------|--------|
| `ops-content-strategy` | Motion-aware opportunity detection | Content opportunities |

**Mode-aware scoring (content-strategy):**
- **Loop-Driven:** Loop Potential × Velocity Story × Audience Alignment
- **Marketplace-Driven:** Review Potential × Install Impact × Retention Value
- **Sales-Driven:** Deal Enablement × Objection Coverage × Stage Fit

---

## Research Skills (1)

| Skill | Purpose | Mode |
|-------|---------|------|
| `research-market-venture` | TAM, growth, defensibility | VENTURE only |

**Selection:** Check `strategy/canvas/00-business-model-mode.md` to determine mode.

---

## Engineering Skills

**Location:** `.claude/skills/engineering/` (kept nested - internal pipeline)

Full production flow: Requirements → Architecture → Maps → Code → Deployment

### V2 (Active) - 12-Level Pipeline

| Level | Purpose |
|-------|---------|
| L0 | Primitives (base types, operations) |
| L1 | Domain objects |
| L2 | Transformations |
| L3 | Validation |
| L4 | State management |
| L5 | Artifacts (outputs, persistence) |
| L6 | API composition |
| L7 | Workflows |
| L8 | Integration |
| L9 | Code implementation |
| L10 | Testing |
| L11 | Infrastructure |

**Orchestrators:**
- `engineering/` - Main orchestrator with 12-level pipeline
- `engineering-code-architect/` - Code generation from specs
- `engineering-maps-architect/` - Language-agnostic patterns
- `engineering-proofs-architect/` - Formal verification with Lean 4
- `engineering-standards-architect/` - Cross-cutting standards

See `.claude/skills/v2/README.md` for details.

### V1 (Deprecated)

Phase-based "Prover" pattern. Preserved for reference.

See `.claude/skills/v1/README.md` for migration path.

---

## Skill Discovery

**By function:**
- Need to reason through a problem? → `reasoning-gateway` agent
- Building systems? → `engineering/`
- Setting up business? → `foundations-builder` agent
- Daily operations? → `ops-*` skills
- Market research? → `research-*` skills
- Sales pipeline? → `sales-execution` agent
- Marketing campaigns? → `marketing-execution` agent

**By invocation:**
- Agents: Spawned via Task tool, run in separate context
- Skills: Auto-loaded by description, share main context

---

## Related Documentation

- [Skills and Agents Architecture](skills-and-agents.md)
- [Architecture Overview](architecture.md)
- [Sales Workflow](../workflows/sales-workflow.md)
- [Marketing Workflow](../workflows/marketing-workflow.md)
- [Causal Flow](../workflows/causal-flow.md)
- [Canvas Setup](../workflows/canvas-setup.md)
