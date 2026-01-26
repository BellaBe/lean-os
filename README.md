# LeanOS Core

AI-native operating system for startup foundations, structured reasoning, and goal management.

**Open Source (MIT)** | 14 skills | 2 agents

## What It Does

- **Startup discovery:** Market sizing, customer segmentation, problem validation, competitive analysis
- **Structured reasoning:** 6 reasoning modes (causal, abductive, inductive, analogical, dialectical, counterfactual)
- **Output shaping:** 11 deliverable schemas for structured outputs
- **Goal-driven execution:** Declare objectives, decompose into actionable plans

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

## Reference

| Document | Description |
|----------|-------------|
| [Agents & Skills Index](docs/reference/agents-skills-index.md) | Complete agents and skills reference |
| [What is LeanOS](docs/reference/what-is-leanos.md) | System overview |

---

## LeanOS Pro

Need sales, marketing, product, engineering, and full business operations?

**LeanOS Pro** — A swiss knife for building and operating a business:
- 181 skills (all domains)
- 44 agents (full orchestration)
- Sales, marketing, product, engineering, customer success, RevOps
- One person operates with 5-10x effectiveness

[Learn more about LeanOS Pro](https://bellabe.gumroad.com/l/leanos-pro)

---

## License

MIT License - see [LICENSE](LICENSE)
