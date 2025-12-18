# LeanOS Skills Reference

Complete reference of AI skills and agents for business operations.

## Architecture (v3.0 - Goal-Oriented)

| Component | Purpose |
|-----------|---------|
| **Agents** (`.claude/agents/`) | Orchestrators that route to skills |
| **Skills** (`.claude/skills/`) | Flat, single-capability instructions |

### Agents (10)

| Agent | Purpose | Skills Loaded |
|-------|---------|---------------|
| `lean-os` | Main engineering orchestrator | Routes to phase agents |
| `lean-os-spec` | SPEC phase orchestration | engineering-spec-* |
| `lean-os-build` | BUILD phase orchestration | engineering-build-* |
| `lean-os-verify` | VERIFY phase orchestration | engineering-verify-* |
| `lean-os-gen` | GEN phase orchestration | engineering-gen-*, apply-standards |
| `problem-solving-gateway` | Route tasks to action skills | action-* skills |
| `reasoning-gateway` | Route to reasoning modes | reasoning-* skills |
| `foundations-builder` | Canvas population | foundations-* skills |
| `sales-execution` | Sales pipeline | sales-* skills |
| `marketing-execution` | Campaign execution | marketing-* skills |

### Skills by Category

| Prefix | Count | Purpose |
|--------|-------|---------|
| `action-*` | 11 | Action skills (deliverable contracts) |
| `engineering-*` | 20 | Categorical verification pipeline |
| `foundations-*` | 10 | Business setup, Canvas sections |
| `goal-*` | 2 | Goal setting and tracking |
| `marketing-*` | 5 | Campaign execution |
| `reasoning-*` | 6 | Reasoning modes |
| `research-*` | 2 | Mode-aware market research |
| `sales-*` | 6 | Sales pipeline activities |

**Total:** 62 skills

---

## Agents

### lean-os (Main Orchestrator)

**Location:** `.claude/agents/lean-os.md`

**Purpose:** Main engineering orchestrator for categorical verification pipeline

**Phases:**
1. SPEC → `lean-os-spec`
2. BUILD → `lean-os-build`
3. VERIFY → `lean-os-verify`
4. GEN → `lean-os-gen`

**Docs:** [Engineering Workflow](../workflows/engineering-workflow.md)

---

### lean-os-spec

**Location:** `.claude/agents/lean-os-spec.md`

**Purpose:** SPEC phase - transform requirements to categorical specifications

**Skills loaded:** engineering-spec-objects, engineering-spec-morphisms, engineering-spec-effects, engineering-spec-constraints

**Output:** `spec/*.yaml`

---

### lean-os-build

**Location:** `.claude/agents/lean-os-build.md`

**Purpose:** BUILD phase - construct categorical structure

**Skills loaded:** engineering-build-category, engineering-build-effects, engineering-build-functors, engineering-build-transformations

**Output:** `build/*.yaml`

---

### lean-os-verify

**Location:** `.claude/agents/lean-os-verify.md`

**Purpose:** VERIFY phase - verify laws and coverage

**Skills loaded:** engineering-verify-laws, engineering-verify-constraints, engineering-verify-coverage

**Output:** `verify/*.yaml`

---

### lean-os-gen

**Location:** `.claude/agents/lean-os-gen.md`

**Purpose:** GEN phase - generate runnable code

**Skills loaded:** engineering-gen-types, engineering-gen-maps, engineering-verify-maps, engineering-gen-code, engineering-apply-standards, engineering-gen-wiring

**Output:** `gen/python/`

---

### problem-solving-gateway

**Location:** `.claude/agents/problem-solving-gateway.md`

**Purpose:** Route tasks to appropriate action skills based on deliverable intent

**Action types:**

| Action Skill | Question Answered |
|--------------|-------------------|
| `action-descriptive` | What is happening? |
| `action-diagnostic` | Why did this happen? |
| `action-evaluative` | Is this good enough? |
| `action-decision` | Which option do we choose? |
| `action-prescriptive` | What should we do? |
| `action-planning` | How do we execute this once? |
| `action-procedural` | How do we execute this every time? |
| `action-validation` | How do we know it worked? |
| `action-risk` | What could go wrong? |
| `action-constrain` | What must not change? |
| `action-alignment` | Why are we misaligned? |

---

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

**Docs:** [Canvas Setup](../workflows/canvas-setup.md)

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

---

## Action Skills (11)

Action skills are **output contracts** used by `problem-solving-gateway`.

| Skill | Question Answered | Output |
|-------|-------------------|--------|
| `action-descriptive` | What is happening? | Situation analysis |
| `action-diagnostic` | Why did this happen? | Root cause analysis |
| `action-evaluative` | Is this good enough? | Assessment report |
| `action-decision` | Which option do we choose? | Decision document |
| `action-prescriptive` | What should we do? | Recommendations |
| `action-planning` | How do we execute this once? | One-time plan |
| `action-procedural` | How do we execute this every time? | SOP/Runbook |
| `action-validation` | How do we know it worked? | Validation criteria |
| `action-risk` | What could go wrong? | Risk assessment |
| `action-constrain` | What must not change? | Constraint documentation |
| `action-alignment` | Why are we misaligned? | Alignment analysis |

---

## Engineering Skills (20)

4-phase categorical verification pipeline.

### SPEC Phase (4 skills)

| Skill | Purpose | Output |
|-------|---------|--------|
| `engineering-spec-objects` | Define domain objects | `spec/objects.yaml` |
| `engineering-spec-morphisms` | Define transformations | `spec/morphisms.yaml` |
| `engineering-spec-effects` | Define side effects | `spec/effects.yaml` |
| `engineering-spec-constraints` | Define invariants | `spec/constraints.yaml` |

### BUILD Phase (4 skills)

| Skill | Purpose | Output |
|-------|---------|--------|
| `engineering-build-category` | Assemble category | `build/category.yaml` |
| `engineering-build-effects` | Build effect system | `build/effects.yaml` |
| `engineering-build-functors` | Define functors | `build/functors.yaml` |
| `engineering-build-transformations` | Define natural transformations | `build/transformations.yaml` |

### VERIFY Phase (4 skills)

| Skill | Purpose | Output |
|-------|---------|--------|
| `engineering-verify-laws` | Verify category laws | `verify/laws-report.yaml` |
| `engineering-verify-constraints` | Verify business rules | `verify/constraints-report.yaml` |
| `engineering-verify-coverage` | Ensure morphism coverage | `verify/coverage-report.yaml` |
| `engineering-verify-maps` | Verify code maps | `maps-verification.yaml` |

### GEN Phase (6 skills)

| Skill | Purpose | Output |
|-------|---------|--------|
| `engineering-gen-types` | Generate types (effects first) | `types/`, `effects/` |
| `engineering-gen-morphisms` | Generate morphism implementations | `morphisms/` |
| `engineering-gen-maps` | Generate code structure maps | `maps/*.map.yaml` |
| `engineering-gen-code` | Generate operations/handlers | `operations/`, `handlers/` |
| `engineering-gen-wiring` | Generate entry point + deployment | `main.py`, `Dockerfile` |
| `engineering-apply-standards` | Apply middleware | `middleware/` |

### Foundation Skills (2)

| Skill | Purpose | Output |
|-------|---------|--------|
| `engineering-foundation-schema` | Project schema/conventions | Structure |
| `engineering-foundation-targets` | Build targets | Configuration |

**Docs:** [Engineering Workflow](../workflows/engineering-workflow.md)

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

### goal-tracker

**Trigger:** Status check, thread completion, periodic review

**Process:**
1. Load goal and linked threads
2. Derive metrics from thread outcomes
3. Calculate gap to targets
4. Project trajectory
5. Generate recommendations or auto-create threads

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

---

## Foundations Skills (10)

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
| `foundations-icp-generator` | ICP per segment from Canvas 04 | Customer profiles |

---

## Sales Skills (6)

| Skill | Purpose | Output |
|-------|---------|--------|
| `sales-materials-generation` | Pitch decks, scripts, templates | `artifacts/sales/{segment}/materials/` |
| `sales-prospect-research` | Find target companies | `research/customer/prospects/` |
| `sales-contact-finding` | Find decision-makers | Contact lists |
| `sales-outreach-sequencing` | Email/phone cadences | Sequence templates |
| `sales-qualification-support` | Discovery call prep | Qualification guides |
| `sales-narrative` | Sales messaging per segment | Sales narratives |

---

## Marketing Skills (5)

| Skill | Purpose | Output |
|-------|---------|--------|
| `marketing-content-generation` | Create content (receives mode) | Content drafts |
| `marketing-content-delivery` | Publish + track | Published content |
| `marketing-channel-optimization` | Optimize channel performance | Optimization reports |
| `marketing-content-strategy` | Motion-aware opportunity detection | Content opportunities |
| `marketing-narrative` | Brand identity, content patterns | Brand guidelines |

**Mode-aware scoring (content-strategy):**
- **Loop-Driven:** Loop Potential × Velocity Story × Audience Alignment
- **Marketplace-Driven:** Review Potential × Install Impact × Retention Value
- **Sales-Driven:** Deal Enablement × Objection Coverage × Stage Fit

---

## Research Skills (2)

| Skill | Purpose | Mode |
|-------|---------|------|
| `research-market-venture` | TAM, growth, defensibility | VENTURE |
| `research-market-bootstrap` | Spend flows, arbitrage, immediate revenue | BOOTSTRAP |

**Selection:** Check `strategy/canvas/00-business-model-mode.md` to determine mode.

---

## Skill Discovery

**By function:**
- Need to solve a problem? → `problem-solving-gateway` agent
- Need to reason through something? → `reasoning-gateway` agent
- Building systems? → `lean-os` agent
- Setting up business? → `foundations-builder` agent
- Market research? → `research-*` skills
- Sales pipeline? → `sales-execution` agent
- Marketing campaigns? → `marketing-execution` agent
- Setting goals? → `goal-setter` skill
- Checking progress? → `goal-tracker` skill

**By invocation:**
- Agents: Spawned via Task tool, run in separate context
- Skills: Auto-loaded by description, share main context

---

## Related Documentation

- [Skills and Agents Architecture](skills-and-agents.md)
- [Architecture Overview](architecture.md)
- [Engineering Workflow](../workflows/engineering-workflow.md)
- [Sales Workflow](../workflows/sales-workflow.md)
- [Marketing Workflow](../workflows/marketing-workflow.md)
- [Research Workflow](../workflows/research-workflow.md)
- [Causal Flow](../workflows/causal-flow.md)
- [Canvas Setup](../workflows/canvas-setup.md)
- [Problem-Solving Workflow](../workflows/problem-solving-workflow.md)
