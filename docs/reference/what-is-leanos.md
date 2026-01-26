# What is LeanOS Core?

LeanOS Core is an **AI-native operating system** for startup foundations, structured reasoning, and goal management.

**Open Source (MIT)** | 14 skills | 2 agents

---

## Core Capabilities

- **Startup discovery:** Market sizing, customer segmentation, problem validation, competitive analysis
- **Structured reasoning:** 6 cognitive modes for different problem types
- **Goal-driven execution:** Declare objectives, decompose into actionable plans
- **Output shaping:** 11 deliverable schemas for structured outputs

---

## How It Works

### 1. Foundations Discovery

Run startup discovery with the `foundations-research` agent:

| Need | Skill | Canvas Output |
|------|-------|---------------|
| Market size | `market-sizing` | 03.opportunity.md |
| Customer segments | `customer-segmenting` | 04.segments.md |
| Problem validation | `problem-validating` | 05.problem.md |
| Competitive analysis | `competitive-analyzing` | 06.competitive.md |
| Value proposition | `value-positioning` | 07.uvp.md, 08.unfair.md |
| MVP design | `solution-designing` | 09.solution.md |

### 2. Structured Reasoning

Route complex problems to the appropriate thinking mode:

| Context | Mode |
|---------|------|
| Operational execution | **Causal** (6-stage flow) |
| Anomaly/diagnosis | **Abductive** |
| Pattern detection | **Inductive** |
| Novel situation | **Analogical** |
| Stakeholder conflict | **Dialectical** |
| Decision evaluation | **Counterfactual** |

### 3. Output Shaping

Select deliverable structure based on intent:

| Need | Schema |
|------|--------|
| Runbook, SOP | **procedural** |
| Success criteria | **validation** |
| Roadmap, phases | **planning** |
| Choose between options | **decision** |
| Root cause | **diagnostic** |
| Recommendations | **prescriptive** |

### 4. Goal-Driven Operation

Transform objectives into structured, trackable goals:

```
Goal → Plan → Execution → State → Learning
 ↑                                    ↓
 └────── gap-closing actions ─────────┘
```

---

## System Architecture

**Agents (2 orchestrators):**

| Agent | Purpose |
|-------|---------|
| `foundations-research` | Run startup discovery phase |
| `problem-solver` | Orchestrate reasoning + output shaping |

**Skills (14 total):**

| Category | Count | Purpose |
|----------|-------|---------|
| Foundations | 6 | Market sizing, segments, problems, competition, positioning, solution |
| Cognitive | 2 | Thinking modes, output schemas |
| Goals | 2 | goal-setter, goal-tracker |
| System | 3 | Agent/skill creation, indexing |
| Intelligence | 1 | Behavioral science |

**Full catalog:** [agents-skills-index.md](agents-skills-index.md)

---

## Directory Structure

```
project/
├── strategy/
│   ├── goals/           # Objectives + index.md
│   └── canvas/          # Business context (15 sections)
├── threads/             # Decision threads + index.md
├── artifacts/           # Deliverables + index.md
└── .claude/
    ├── agents/          # Orchestrators (2)
    └── skills/          # Skills (14)
```

---

## Getting Started

1. Copy `.claude/` directory to your project
2. Start using skills via natural language
3. Optionally set up goal-driven structure

See [README.md](../../README.md) for quick start guide.

---

## LeanOS Pro

Need sales, marketing, product, engineering, and full business operations?

**LeanOS Pro** — A swiss knife for building and operating a business:
- 181 skills (all domains)
- 44 agents (full orchestration)
- Sales, marketing, product, engineering, customer success, RevOps
- One person operates with 5-10x effectiveness

[Learn more about LeanOS Pro](https://bellabe.gumroad.com/l/leanos-pro)
