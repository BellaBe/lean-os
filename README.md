# LeanOS Core

[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![GitHub stars](https://img.shields.io/github/stars/BellaBe/lean-os)](https://github.com/BellaBe/lean-os/stargazers)
![Claude Code](https://img.shields.io/badge/Claude_Code-Compatible-blueviolet)

AI operating system for founders. Run startup discovery, structured reasoning, and goal management with Claude Code.

**See every prompt. Modify any skill. Know your agent.**

Open Source (MIT) | 14 skills | 2 agents

---

## What It Does

- **Startup discovery:** Market sizing, customer segmentation, problem validation, competitive analysis
- **Structured reasoning:** 6 reasoning modes (causal, abductive, inductive, analogical, dialectical, counterfactual)
- **Output shaping:** 11 deliverable schemas for structured outputs
- **Goal-driven execution:** Declare objectives, decompose into actionable plans

---

## Quick Start

### 1. Clone and rename

```bash
# Clone LeanOS Core
git clone https://github.com/BellaBe/lean-os.git

# Rename to your project
mv lean-os your-project
cd your-project
```

### 2. Start using skills

Skills auto-load based on your task. Try:

- "Size the market for X" → `market-sizing`
- "Define customer segments" → `customer-segmenting`
- "Validate this problem" → `problem-validating`
- "I want to achieve X" → `goal-setter`
- "Reason through this decision" → `thinking-modes`

### 3. Set up goals (optional)

For goal-driven operation:

```
your-project/
├── strategy/
│   ├── goals/           # Objectives + index.md
│   └── canvas/          # Business context (15 sections)
├── threads/             # Decision threads + index.md
├── artifacts/           # Deliverables + index.md
└── .claude/             # LeanOS skills & agents
```

---

## Core Skills (14)

### Foundations (6)
| Skill | Purpose |
|-------|---------|
| `market-sizing` | TAM/SAM/SOM calculation, market timing |
| `customer-segmenting` | Observable segment definitions, pain scores |
| `problem-validating` | Problem severity scoring (F×I×WTP) |
| `competitive-analyzing` | Competitor mapping, positioning gaps |
| `value-positioning` | UVP statements, moat analysis |
| `solution-designing` | MVP feature set, growth architecture |

### Cognitive (2)
| Skill | Purpose |
|-------|---------|
| `thinking-modes` | 6 reasoning modes for different problem types |
| `shaping-schemas` | 11 deliverable schemas for structured outputs |

### Goals (2)
| Skill | Purpose |
|-------|---------|
| `goal-setter` | Transform objectives into structured goals |
| `goal-tracker` | Track progress, derive state from execution |

### System (3)
| Skill | Purpose |
|-------|---------|
| `agent-creating` | Create Claude Code subagents |
| `skill-creating` | Create Claude Code skills |
| `directory-indexing` | Generate index.md files for navigation |

### Intelligence (1)
| Skill | Purpose |
|-------|---------|
| `behavioral-science` | Apply behavioral science to revenue touchpoints |

---

## Core Agents (2)

| Agent | Purpose |
|-------|---------|
| `foundations-research` | Run startup discovery phase (market, segments, problems, competition) |
| `problem-solver` | Orchestrate reasoning + output shaping for rigorous deliverables |

---

## Core vs Pro

| | Core (Free) | Pro ($249) |
|--|-------------|------------|
| Skills | 14 | 181 |
| Agents | 2 | 44 |
| Foundations | ✓ | ✓ |
| Sales & Marketing | — | ✓ |
| Product & Engineering | — | ✓ |
| Customer Success | — | ✓ |
| RevOps | — | ✓ |

**Pro** - Full business operations: sales, marketing, product, engineering, customer success, RevOps. One person operates with 5-10x effectiveness.

[Get Pro →](https://bellabe.gumroad.com/l/leanos-pro)

---

## Reference

| Document | Description |
|----------|-------------|
| [Agents & Skills Index](docs/reference/agents-skills-index.md) | Complete agents and skills reference |
| [What is LeanOS](docs/reference/what-is-leanos.md) | System overview |

---

## License

MIT License - see [LICENSE](LICENSE)
