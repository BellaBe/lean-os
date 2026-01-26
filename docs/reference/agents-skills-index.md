# LeanOS Core Agents & Skills Reference

Complete reference of AI agents and skills for startup foundations, reasoning, and goal management.

## Overview

| Component | Count | Purpose |
|-----------|-------|---------|
| **Agents** | 2 | Orchestrators that route to skills |
| **Skills** | 14 | Single-capability instructions |

---

## Agents (2)

### foundations-research

**Location:** `.claude/agents/foundations-research.md`

**Purpose:** Run startup discovery phase — market research, customer segmentation, problem validation, competitive analysis.

**Trigger Phrases:** "discovery", "TAM", "segments", "ICP", "target market", "validate assumptions"

**Skills Loaded:** market-sizing, customer-segmenting, problem-validating

**Canvas Ownership:**
| Section | File | Purpose |
|---------|------|---------|
| 03 | opportunity.md | TAM/SAM/SOM, market timing |
| 04 | segments.md | Customer segments with observable filters |
| 05 | problem.md | Problems ranked by severity |
| 06 | competitive.md | Direct/indirect competitors |

---

### problem-solver

**Location:** `.claude/agents/problem-solver.md`

**Purpose:** Orchestrate shaping-schemas and thinking-modes skills to produce rigorous outputs. Default entry point for non-trivial tasks.

**Skills Loaded:** shaping-schemas, thinking-modes

**Process:**
1. Select structuring mode(s) via shaping-schemas
2. Pair with appropriate thinking-modes
3. Produce output matching mode's schema exactly

**Mode-Reasoning Pairings:**
| Action Mode | Default Reasoning |
|-------------|-------------------|
| diagnostic | abductive |
| decision | dialectical or counterfactual |
| planning | causal |
| evaluative | dialectical or causal |
| prescriptive | causal |

---

## Skills by Category

| Category | Count | Purpose |
|----------|-------|---------|
| `foundations-*` | 6 | Startup discovery and positioning |
| `cognitive-*` | 2 | Reasoning and output shaping |
| `goal-*` | 2 | Goal setting and tracking |
| `system-*` | 3 | Meta-skills for creating and organizing |
| `intelligence-*` | 1 | Domain expertise |

**Total:** 14 skills

---

## Foundations Skills (6)

Skills for startup discovery, market analysis, and positioning.

| Skill | Purpose | Canvas Output |
|-------|---------|---------------|
| `market-sizing` | TAM/SAM/SOM calculation, market timing | 03.opportunity.md |
| `customer-segmenting` | Observable segment definitions, pain scores | 04.segments.md |
| `problem-validating` | Problem severity scoring (F×I×WTP) | 05.problem.md |
| `competitive-analyzing` | Competitor mapping, positioning gaps | 06.competitive.md |
| `value-positioning` | UVP statements, moat analysis | 07.uvp.md, 08.unfair.md |
| `solution-designing` | MVP feature set, growth architecture | 09.solution.md |

### market-sizing

**Location:** `.claude/skills/market-sizing/SKILL.md`

**Purpose:** Calculate market opportunity with TAM/SAM/SOM and timing analysis.

**Process:**
1. Load context (mode, constraints)
2. Calculate TAM (top-down + bottom-up)
3. Calculate SAM (apply filters)
4. Calculate SOM (realistic capture based on constraints)
5. Assess timing (Why Now?)
6. Validate against mode requirements

---

### customer-segmenting

**Location:** `.claude/skills/customer-segmenting/SKILL.md`

**Purpose:** Generate strategic customer segment definitions with observable filters.

**Output:** Segments with 2+ searchable filters, pain intensity scores (1-5), segment sizing.

---

### problem-validating

**Location:** `.claude/skills/problem-validating/SKILL.md`

**Purpose:** Validate and prioritize problems by severity.

**Scoring:** Severity = Frequency × Intensity × WTP (max 125)

**Output:** Top 3 problems with evidence-backed scores.

---

### competitive-analyzing

**Location:** `.claude/skills/competitive-analyzing/SKILL.md`

**Purpose:** Map competitive landscape and identify positioning opportunities.

**Output:** Direct/indirect competitors, positioning matrix, gaps and threats.

---

### value-positioning

**Location:** `.claude/skills/value-positioning/SKILL.md`

**Purpose:** Craft differentiated value propositions and defensible positioning.

**Output:** UVP statement (For-Only-That formula), moat analysis with defensibility scores.

---

### solution-designing

**Location:** `.claude/skills/solution-designing/SKILL.md`

**Purpose:** Design MVP feature set aligned with growth architecture.

**Process:**
1. Select growth model (Traditional/PLG/Network-Led)
2. Define growth-required features
3. Map features to problems
4. Prioritize MVP scope (P0/P1/P2)
5. Define growth loops

---

## Cognitive Skills (2)

Skills for structured reasoning and output formatting.

| Skill | Purpose | When to Use |
|-------|---------|-------------|
| `thinking-modes` | Multi-perspective reasoning | "reason through", "think through", "why did" |
| `shaping-schemas` | Deliverable structure selection | "decide", "plan", "diagnose", "recommend" |

### thinking-modes

**Location:** `.claude/skills/thinking-modes/SKILL.md`

**Purpose:** Route to appropriate cognitive mode and execute multi-perspective reasoning.

**Modes:**
| Mode | Question | Trigger |
|------|----------|---------|
| **causal** | How do we execute? | Known process, goal execution |
| **abductive** | Why did this happen? | Single anomaly, diagnosis |
| **inductive** | What pattern exists? | Multiple observations |
| **analogical** | How is this like that? | Novel situation |
| **dialectical** | How do we resolve this? | Conflicting positions |
| **counterfactual** | What if we had/do X? | Decision evaluation |

**Core Principle:** Societies of Thought — reasoning emerges from simulated dialogue between diverse personas with mandatory disagreement.

---

### shaping-schemas

**Location:** `.claude/skills/shaping-schemas/SKILL.md`

**Purpose:** Format outputs into rigorous deliverable structures.

**Relationship:** thinking-modes = HOW to reason, shaping-schemas = WHAT to deliver

**Schemas:**
| Schema | Purpose |
|--------|---------|
| procedural | SOPs, checklists, playbooks |
| validation | Success criteria, test plans |
| planning | Roadmaps, phased plans |
| decision | Option evaluation, recommendations |
| evaluative | Assessments, audits |
| diagnostic | Root cause analysis |
| risk | Threat identification |
| constraint | Requirements, guardrails |
| alignment | Stakeholder conflicts |
| prescriptive | Actionable guidance |
| descriptive | Neutral summaries (default) |

---

## Goal Skills (2)

| Skill | Purpose | Input | Output |
|-------|---------|-------|--------|
| `goal-setter` | Transform objectives into structured goals | User intent | `strategy/goals/active/{id}.md` |
| `goal-tracker` | Derive state from execution, track progress | Goal + Threads | Updated goal state |

### goal-setter

**Location:** `.claude/skills/goal-setter/SKILL.md`

**Trigger:** User expresses intent ("I want to...", "Goal is to...", "Achieve X by Y")

**Process:**
1. Capture objective (what, why, when)
2. Determine goal type (business, brand, product, learning)
3. Apply mode from Canvas (VENTURE/BOOTSTRAP)
4. Define success criteria (measurable)
5. Decompose into subgoals + milestones
6. Set autonomy level (auto/ask/hybrid)

---

### goal-tracker

**Location:** `.claude/skills/goal-tracker/SKILL.md`

**Trigger:** Status check, thread completion, periodic review

**Process:**
1. Load goal and linked threads
2. Derive metrics from thread outcomes (state is computed, not tracked)
3. Calculate gap to targets
4. Project trajectory
5. Generate recommendations based on gaps

---

## System Skills (3)

Meta-skills for creating agents, skills, and organizing documentation.

| Skill | Purpose | When to Use |
|-------|---------|-------------|
| `agent-creating` | Create Claude Code subagents | "create an agent", "make an orchestrator" |
| `skill-creating` | Create Claude Code skills | "create a skill", "make a capability" |
| `directory-indexing` | Generate index.md files | "index", "catalog", "build index" |

### agent-creating

**Location:** `.claude/skills/agent-creating/SKILL.md`

**Purpose:** Create subagents with proper YAML frontmatter, system prompts, and tool configuration.

**Patterns:** Orchestrator, Pipeline, Specialist

---

### skill-creating

**Location:** `.claude/skills/skill-creating/SKILL.md`

**Purpose:** Create skills with proper SKILL.md format, references, and optional scripts.

**Key Rule:** Skills are instructions first. SKILL.md is required; scripts and assets are optional.

---

### directory-indexing

**Location:** `.claude/skills/directory-indexing/SKILL.md`

**Purpose:** Generate index.md files listing .md documentation. Pure navigation.

**Excludes:** Code files, node_modules, .git, src, lib, dist, build

---

## Intelligence Skills (1)

Domain expertise skills.

| Skill | Purpose | When to Use |
|-------|---------|-------------|
| `behavioral-science` | Apply behavioral science to revenue | "persuade", "convert", "landing page", "copy" |

### behavioral-science

**Location:** `.claude/skills/behavioral-science/SKILL.md`

**Purpose:** Apply behavioral science to revenue touchpoints (landing pages, emails, sales).

**Modes:**
| Mode | Signal | Output |
|------|--------|--------|
| AUDIT | review, analyze, assess | Scored assessment + gaps |
| CREATE | write, draft, generate | Content with bias annotations |
| FIX | fix, improve, optimize | Before/after transformation |

**Core 10 Biases:** Loss Aversion, Scarcity, Social Proof, Anchoring, Commitment, Reciprocity, Distinctiveness, Framing, Peak-End, Choice Architecture

---

## Skill Discovery

**By function:**
- Market sizing? → `market-sizing` skill
- Customer segments? → `customer-segmenting` skill
- Problem validation? → `problem-validating` skill
- Competitive analysis? → `competitive-analyzing` skill
- Value proposition? → `value-positioning` skill
- MVP design? → `solution-designing` skill
- Need to reason through something? → `thinking-modes` skill
- Need structured output? → `shaping-schemas` skill
- Setting goals? → `goal-setter` skill
- Checking progress? → `goal-tracker` skill
- Creating agents? → `agent-creating` skill
- Creating skills? → `skill-creating` skill
- Building indexes? → `directory-indexing` skill
- Revenue optimization? → `behavioral-science` skill

**Discovery phases:**
- Discovery phase? → `foundations-research` agent (orchestrates market-sizing, customer-segmenting, problem-validating)

---

## Related Documentation

- [What is LeanOS](what-is-leanos.md)
- [Architecture Overview](architecture.md)

---

## LeanOS Pro

Need sales, marketing, product, engineering, and full business operations?

**LeanOS Pro** — A swiss knife for building and operating a business:
- 181 skills (all domains)
- 44 agents (full orchestration)
- Sales, marketing, product, engineering, customer success, RevOps
- One person operates with 5-10x effectiveness

[Learn more about LeanOS Pro](https://bellabe.gumroad.com/l/leanos-pro)
