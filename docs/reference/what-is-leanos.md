# What is LeanOS Core?

LeanOS Core is an **AI-native operating system** for structured reasoning, goal management, and problem-solving.

**Open Source (MIT)** | 15 skills | 2 agents

---

## Core Capabilities

- **Structured reasoning:** 6 reasoning modes for different problem types
- **Goal-driven execution:** Declare objectives, decompose into actionable plans
- **Problem-solving gateway:** Route tasks to appropriate action skills
- **Market foundations:** Market intelligence and problem-solution fit analysis

---

## How It Works

### 1. Reasoning Gateway

Route complex problems to the appropriate reasoning mode:

| Context | Mode |
|---------|------|
| Operational execution | **Causal** (6-stage flow) |
| Anomaly/diagnosis | **Abductive** |
| Pattern detection | **Inductive** |
| Novel situation | **Analogical** |
| Stakeholder conflict | **Dialectical** |
| Decision evaluation | **Counterfactual** |

### 2. Problem-Solving Gateway

Route tasks to action skills based on what you need:

| Need | Action Skill |
|------|--------------|
| Describe current state | `action-descriptive` |
| Find root cause | `action-diagnostic` |
| Get recommendations | `action-prescriptive` |
| Create execution plan | `action-planning` |
| Choose between options | `action-decision` |

### 3. Goal-Driven Operation

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
| `reasoning-gateway` | Route to reasoning modes |
| `problem-solving-gateway` | Route to action skills |

**Skills (15 total):**

| Category | Count | Purpose |
|----------|-------|---------|
| Reasoning | 6 | Causal, abductive, inductive, analogical, dialectical, counterfactual |
| Actions | 5 | Descriptive, diagnostic, prescriptive, planning, decision |
| Goals | 2 | goal-setter, goal-tracker |
| Foundations | 2 | market-intelligence, problem-solution-fit |

**Full catalog:** [skills-index.md](skills-index.md)

---

## Directory Structure

```
project/
├── strategy/
│   ├── goals/           # Objectives + index.md
│   └── canvas/          # Business context + index.md
├── threads/             # Decision threads + index.md
├── artifacts/           # Deliverables + index.md
└── .claude/
    ├── agents/          # Orchestrators (2)
    └── skills/          # Skills (15)
```

---

## Getting Started

1. Copy `.claude/` directory to your project
2. Start using skills via natural language
3. Optionally set up goal-driven structure

See [README.md](../../README.md) for quick start guide.

---

## LeanOS Pro

Need sales, marketing, product, engineering, and research capabilities?

**LeanOS Pro** includes the complete system:
- 63 skills (all domains)
- 12 agents (full orchestration)
- Sales, marketing, product, engineering workflows

[Learn more about LeanOS Pro](https://bellabe.gumroad.com/l/leanos-pro)
