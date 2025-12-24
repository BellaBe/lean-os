# LeanOS: AI-Native Operating System for Business Automation

**Version:** 4.0 | **Status:** Active Development

AI-native OS that automates 95%+ of business operations for startups, small teams, and founders.

## What It Does

- **Goal-driven execution:** Declare objectives, AI decomposes and executes
- **Automates decisions:** Claude handles engineering, sales, marketing autonomously
- **Single source of truth:** 15-section Lean Canvas provides strategic context
- **State derived from execution:** Metrics computed from threads, no manual tracking
- **Configurable autonomy:** Auto, ask, or hybrid modes per goal

## Quick Start

**New users:** Read [What is LeanOS?](docs/reference/what-is-leanos.md)
**Existing projects:** Check `strategy/goals/active/` for current objectives

## Documentation

### Core Concepts
| Topic | Description |
|-------|-------------|
| [What is LeanOS?](docs/reference/what-is-leanos.md) | Core principles, problem/solution |
| [Architecture](docs/reference/architecture.md) | System layers, operating model, data flow |
| [All Skills](docs/reference/all-skills.md) | Complete skills and agents reference |

### Workflows
| Workflow | Description |
|----------|-------------|
| [Canvas Setup](docs/workflows/canvas-setup.md) | Foundation-building process (45-60 min) |
| [Causal Flow](docs/workflows/causal-flow.md) | 6-stage decision framework |
| [Sales](docs/workflows/sales-workflow.md) | Strategy to execution to learning |
| [Marketing](docs/workflows/marketing-workflow.md) | Learning-driven content |
| [Engineering](docs/workflows/engineering-workflow.md) | SPEC → BUILD → VERIFY → GEN |
| [Daily Routine](docs/workflows/daily-routine.md) | 5-minute review process |

## Directory Structure

```
lean-os/
├── strategy/
│   ├── goals/active/         # Current objectives (PRIMARY)
│   └── canvas/               # 15-section Lean Canvas
├── threads/{type}/{name}/    # 6-stage decision threads
├── artifacts/                # Deliverables
├── research/customer/        # ICP definitions, prospects
├── .claude/
│   ├── agents/               # 13 orchestrators
│   └── skills/               # 70 skills
└── docs/                     # Full documentation
```

**Details:** [Architecture](docs/reference/architecture.md)

## Business Model Modes

LeanOS adapts to your business model:

| Mode | Focus | Metrics |
|------|-------|---------|
| **VENTURE** | Scale, defensibility | MAU, ARR, market share |
| **BOOTSTRAP** | Cash flow, profitability | MRR, profit, LTV:CAC |

**Configuration:** `strategy/canvas/00-business-model-mode.md`

## Technology Stack

- **AI:** Claude Skills via Claude Code
- **Languages:** Python, JS/TS, Bash, Markdown
- **Infrastructure:** Local file system, Git

## Getting Started

1. Read [What is LeanOS?](docs/reference/what-is-leanos.md)
2. Follow [Canvas Setup](docs/workflows/canvas-setup.md)
3. Create first goal using `goal-setter` skill
4. Review [Daily Routine](docs/workflows/daily-routine.md)

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md)

## License

MIT License - see [LICENSE](LICENSE)
