# LeanOS Core Skills Reference

Complete reference of AI skills and agents for reasoning and problem-solving.

## Overview

| Component | Count | Purpose |
|-----------|-------|---------|
| **Agents** | 2 | Orchestrators that route to skills |
| **Skills** | 15 | Single-capability instructions |

---

## Agents (2)

| Agent | Purpose | Skills Loaded |
|-------|---------|---------------|
| `reasoning-gateway` | Route to appropriate reasoning mode | reasoning-* |
| `problem-solving-gateway` | Route to appropriate action skill | action-* |

---

## Skills by Category

| Prefix | Count | Purpose |
|--------|-------|---------|
| `reasoning-*` | 6 | Reasoning modes |
| `action-*` | 5 | Deliverable contracts |
| `goal-*` | 2 | Goal setting and tracking |
| `foundations-*` | 2 | Market and problem analysis |

**Total:** 15 skills

---

## Reasoning Skills (6)

Route through `reasoning-gateway` agent for non-trivial reasoning tasks.

| Skill | Purpose | When to Use |
|-------|---------|-------------|
| `reasoning-causal` | Execute known processes with 6-stage flow | Operational execution, threads |
| `reasoning-abductive` | Diagnose anomalies, form hypotheses | "Why did X happen?" |
| `reasoning-inductive` | Detect patterns, generalize from examples | "This keeps happening" |
| `reasoning-analogical` | Transfer knowledge across domains | "This is like..." |
| `reasoning-dialectical` | Resolve conflicts through synthesis | Stakeholder disagreements |
| `reasoning-counterfactual` | Evaluate decisions via alternatives | "What if we had..." |

### reasoning-causal

**Location:** `.claude/skills/reasoning-causal/SKILL.md`

**Purpose:** Execute known processes through structured 6-stage flow

**Stages:**
1. **Input** — Gather context, constraints
2. **Hypothesis** — Form testable propositions
3. **Implication** — Derive expected outcomes
4. **Decision** — Select action path
5. **Actions** — Execute steps
6. **Learning** — Capture outcomes, update knowledge

**Enforced for:** All threads in `threads/` directory

---

### reasoning-abductive

**Location:** `.claude/skills/reasoning-abductive/SKILL.md`

**Purpose:** Generate explanatory hypotheses from incomplete observations

**Output:** Ranked hypotheses with evidence and confidence scores

---

### reasoning-inductive

**Location:** `.claude/skills/reasoning-inductive/SKILL.md`

**Purpose:** Extract patterns and generalizations from multiple observations

**Output:** Validated patterns with confidence bounds and exception handling

---

### reasoning-analogical

**Location:** `.claude/skills/reasoning-analogical/SKILL.md`

**Purpose:** Transfer knowledge from source domains to novel situations

**Output:** Adapted solutions with explicit mappings and context adjustments

---

### reasoning-dialectical

**Location:** `.claude/skills/reasoning-dialectical/SKILL.md`

**Purpose:** Synthesize competing positions through thesis-antithesis-synthesis

**Output:** Integrated positions with acknowledged trade-offs

---

### reasoning-counterfactual

**Location:** `.claude/skills/reasoning-counterfactual/SKILL.md`

**Purpose:** Evaluate alternative scenarios by simulating interventions

**Output:** Comparative analysis with probability-weighted outcomes

---

## Action Skills (5)

Route through `problem-solving-gateway` agent for task execution.

| Skill | Question Answered | Output |
|-------|-------------------|--------|
| `action-descriptive` | What is happening? | Situation analysis |
| `action-diagnostic` | Why did this happen? | Root cause analysis |
| `action-prescriptive` | What should we do? | Recommendations |
| `action-planning` | How do we execute this? | Execution plan |
| `action-decision` | Which option do we choose? | Decision document |

### action-descriptive

**Purpose:** Describe and summarize current state

**Use when:** User asks to describe, summarize, analyze, or explain something

---

### action-diagnostic

**Purpose:** Identify root causes of problems

**Use when:** User asks why something happened, debugging, incident analysis

---

### action-prescriptive

**Purpose:** Recommend next steps or best approaches

**Use when:** User asks for recommendations, "what should I do" guidance

---

### action-planning

**Purpose:** Create execution roadmap

**Use when:** User asks for timeline, phased plan, or execution sequence

---

### action-decision

**Purpose:** Choose between options

**Use when:** User needs to prioritize or make go/no-go decisions

---

## Goal Skills (2)

| Skill | Purpose | Input | Output |
|-------|---------|-------|--------|
| `goal-setter` | Transform objectives into structured goals | User intent | `strategy/goals/active/{id}.md` |
| `goal-tracker` | Derive state from execution, track progress | Goal + Threads | Updated goal state |

### goal-setter

**Trigger:** User expresses intent ("I want to...", "Goal is to...", "Achieve X by Y")

**Process:**
1. Capture objective (what, why, when)
2. Read Canvas for strategic context (if exists)
3. Define success criteria (measurable)
4. Decompose into subgoals + milestones
5. Set autonomy level (auto/ask/hybrid)

---

### goal-tracker

**Trigger:** Status check, thread completion, periodic review

**Process:**
1. Load goal and linked threads
2. Derive metrics from thread outcomes
3. Calculate gap to targets
4. Project trajectory
5. Generate recommendations

---

## Foundations Skills (2)

| Skill | Purpose | Canvas Sections |
|-------|---------|-----------------|
| `foundations-market-intelligence` | Market size, competitive landscape | 01-04, 06 |
| `foundations-problem-solution-fit` | Problem validation, solution fit | 05, 09, 10 |

### foundations-market-intelligence

**Purpose:** Analyze market opportunity

**Output:** Market size (TAM/SAM/SOM), competitor analysis, segment profiles

---

### foundations-problem-solution-fit

**Purpose:** Validate problem-solution fit

**Output:** Problem evidence, solution hypothesis, validation status

---

## Skill Discovery

**By function:**
- Need to reason through something? → `reasoning-gateway` agent
- Need to solve a problem? → `problem-solving-gateway` agent
- Setting goals? → `goal-setter` skill
- Checking progress? → `goal-tracker` skill
- Market analysis? → `foundations-market-intelligence` skill
- Problem validation? → `foundations-problem-solution-fit` skill

**By invocation:**
- Agents: Spawned via Task tool, run in separate context
- Skills: Auto-loaded by description, share main context

---

## Related Documentation

- [Architecture Overview](architecture.md)
- [Causal Flow](../workflows/causal-flow.md)
- [Problem-Solving Workflow](../workflows/problem-solving-workflow.md)
- [Daily Routine](../workflows/daily-routine.md)

---

## LeanOS Pro

Need more capabilities? **LeanOS Pro** includes 63 skills and 12 agents:

- Sales (6 skills) — prospecting, qualification, outreach
- Marketing (5 skills) — content strategy, generation, delivery
- Product (5 skills) — requirements, flows, wireframes, handoff
- Engineering (12 skills) — frontend, testing, code quality
- Research (4 skills) — market research, knowledge synthesis
- Additional foundations (8 skills) — business model, GTM, funding, validation

[Learn more about LeanOS Pro](https://bellabe.gumroad.com/l/leanos-pro)
