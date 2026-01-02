# LeanOS Core

AI-native operating system for reasoning, goal management, and problem-solving.

**Open Source (MIT)** | 15 skills | 2 agents

## What It Does

- **Structured reasoning:** 6 reasoning modes (causal, abductive, inductive, analogical, dialectical, counterfactual)
- **Goal-driven execution:** Declare objectives, decompose into actionable plans
- **Problem-solving:** Route tasks to appropriate action skills
- **Market foundations:** Market intelligence and problem-solution fit analysis

---

## Quick Start

### 1. Copy to your project

```bash
# Clone LeanOS Core
git clone https://github.com/BellaBe/lean-os.git

# Copy .claude/ directory to your project
cp -r lean-os/.claude/ your-project/
```

### 2. Start using skills

Skills auto-load based on your task. Try:

- "Help me reason through this decision" → `reasoning-gateway`
- "I want to achieve X" → `goal-setter`
- "What's happening with Y?" → `action-descriptive`

### 3. Set up goals (optional)

For goal-driven operation:

```
your-project/
├── strategy/
│   ├── goals/           # Objectives + index.md
│   └── canvas/          # Business context + index.md
├── threads/             # Decision threads + index.md
├── artifacts/           # Deliverables + index.md
└── .claude/             # LeanOS skills & agents
```

---

## Core Skills (15)

### Reasoning (6)
| Skill | Purpose |
|-------|---------|
| `reasoning-causal` | Execute known processes with 6-stage flow |
| `reasoning-abductive` | Diagnose anomalies, form hypotheses |
| `reasoning-inductive` | Detect patterns, generalize |
| `reasoning-analogical` | Transfer knowledge across domains |
| `reasoning-dialectical` | Resolve conflicts through synthesis |
| `reasoning-counterfactual` | Evaluate decisions via alternatives |

### Actions (5)
| Skill | Question Answered |
|-------|-------------------|
| `action-descriptive` | What is happening? |
| `action-diagnostic` | Why did this happen? |
| `action-prescriptive` | What should we do? |
| `action-planning` | How do we execute this? |
| `action-decision` | Which option do we choose? |

### Goals (2)
| Skill | Purpose |
|-------|---------|
| `goal-setter` | Transform objectives into structured goals |
| `goal-tracker` | Track progress, derive state from execution |

### Foundations (2)
| Skill | Purpose |
|-------|---------|
| `foundations-market-intelligence` | Market size, competitive landscape |
| `foundations-problem-solution-fit` | Problem validation, solution fit |

---

## Core Agents (2)

| Agent | Purpose |
|-------|---------|
| `reasoning-gateway` | Route tasks to appropriate reasoning mode |
| `problem-solving-gateway` | Route tasks to appropriate action skill |

---

## Workflows

| Workflow | Description |
|----------|-------------|
| [Daily Routine](docs/workflows/daily-routine.md) | Goal-driven daily operations |
| [Causal Flow](docs/workflows/causal-flow.md) | 6-stage decision framework |
| [Problem Solving](docs/workflows/problem-solving-workflow.md) | Action skill routing |
| [Canvas Setup](docs/workflows/canvas-setup.md) | Business context setup |

---

## Reference

| Document | Description |
|----------|-------------|
| [Skills Index](docs/reference/skills-index.md) | Complete skills reference |
| [Architecture](docs/reference/architecture.md) | System design |
| [What is LeanOS](docs/reference/what-is-leanos.md) | System overview |

---

## LeanOS Pro

Need sales, marketing, product, engineering, and research capabilities?

**LeanOS Pro** includes the complete system:
- 63 skills (all domains)
- 12 agents (full orchestration)
- Sales, marketing, product, engineering workflows
- Priority support

[Learn more about LeanOS Pro](https://bellabe.gumroad.com/l/leanos-pro)

---

## License

MIT License - see [LICENSE](LICENSE)
