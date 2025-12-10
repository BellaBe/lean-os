# LeanOS: AI-Native Operating System for Startups, Small Teams, and Founders

**Status:** Active Development | **Version:** 2.2 (Goal-Oriented) | **Last Updated:** 2025-12-10

AI-native OS that automates 95%+ of business operations for startups, small teams, and founders.

## What It Does

- **Goal-driven execution:** Declare objectives, AI decomposes into plans and executes
- **Automates decisions:** Claude AI processes engineering, sales, marketing, and business decisions autonomously
- **Single source of truth:** Lean Canvas (15 living documents) provides strategic context
- **State derived from execution:** No manual tracking, metrics computed from threads
- **Configurable autonomy:** Auto, ask, or hybrid modes per goal

## Quick Navigation

### Reference
- [What is LeanOS?](docs/reference/what-is-leanos.md) - Problem, solution, core principles
- [Architecture](docs/reference/architecture.md) - System layers and data flow
- [All Skills](docs/reference/all-skills.md) - Complete skills reference

### Workflows
- [Canvas Setup](docs/workflows/canvas-setup.md) - Foundation-building process
- [Sales Workflow](docs/workflows/sales-workflow.md) - Strategy → execution → learning
- [Marketing Workflow](docs/workflows/marketing-workflow.md) - Learning-driven content
- [Engineering Workflow](docs/workflows/engineering-workflow.md) - Verified system generation
- [Daily Routine](docs/workflows/daily-routine.md) - Your 5-min review
- [Causal Flow](docs/workflows/causal-flow.md) - 6-stage decision framework

## Core Principles

1. **AI-first execution:** Claude skills handle operations, not just documentation
2. **Context-shaping over generalization:** Each skill targets specific decision types
3. **Zero redundancy:** Information exists in ONE location only
4. **Evidence-based decisions:** All choices trace to Canvas assumptions
5. **Learning-driven content:** Marketing creates when business generates insights
6. **Mode-aware operations:** Adapts to VENTURE or BOOTSTRAP business models
7. **Human-in-the-loop:** AI executes, humans oversee strategy
8. **Flat architecture:** Easy skill discovery and maintenance
9. **Mathematical verification:** System designs are provably correct
10. **Direct and production-ready:** No fluff, just actionable outputs
11. **Continuous improvement:** Regular updates based on performance data
12. **Transparent processes:** Clear documentation of AI decision-making
13. **Scalable systems:** Designed for growth from day one
14. **Ethical AI use:** Prioritizes user privacy and data security
15. **Open collaboration:** Encourages human contributions and feedback
16. **Modular design:** Skills and agents can be updated independently
17. **Robust error handling:** Skills include fallback mechanisms
18. **Comprehensive documentation:** All aspects of the OS are well-documented
19. **Version control:** Changes tracked for accountability
20. **User-centric design:** Focused on the needs of startups and small teams

## Dual-Mode Support: Venture vs Bootstrap

LeanOS supports two fundamentally different business models with mode-specific execution:

### VENTURE Mode
**For funded startups pursuing scale:**
- **Decision Criteria:** Strategic value, market size, defensibility
- **Metrics Focus:** MAU, ARR growth, market share, runway
- **Research:** TAM sizing, competitive landscape, 10x opportunities
- **Impact Formula:** `(Strategic Value × Market Size × Defensibility) / 3`
- **Timeline:** 7-10 year exit horizon

**Best for:** VC-backed companies, billion-dollar markets, winner-take-all dynamics

### BOOTSTRAP Mode
**For profitable businesses pursuing cash flow:**
- **Decision Criteria:** Revenue impact, time to cash, profit margin
- **Metrics Focus:** MRR, monthly profit, cash flow, LTV:CAC
- **Research:** Current spend mapping, arbitrage opportunities, immediate revenue
- **Impact Formula:** `(Revenue Impact × Time to Cash × Margin) / 3`
- **Timeline:** Profitable within 3 months

**Best for:** Self-funded founders, niche markets, lifestyle businesses

### Mode Configuration

Set your mode in `strategy/canvas/00-business-model-mode.md`:

```markdown
**Active Mode:** BOOTSTRAP

**Rationale:**
- Self-funded, need profitability within 3 months
- Revenue-first approach to validate market
- Exit optional, cash flow primary goal
```

**Mode impacts:**
- Market research approach (TAM vs current spend)
- Impact scoring in decision-making
- Metrics tracking and dashboards
- Success criteria for initiatives

See [Business Model Mode documentation](strategy/canvas/00-business-model-mode.md) for complete details.

## Directory Structure

```text
lean-os/
├── strategy/
│   ├── goals/                # Declared objectives (PRIMARY OPERATING MODE)
│   │   ├── active/           # Current goals with plans + state
│   │   ├── completed/        # Achieved goals (archive)
│   │   └── abandoned/        # Dropped goals (archive)
│   └── canvas/               # Lean Canvas (15 files) - STRATEGIC CONTEXT
├── threads/                  # Decision execution (6-stage causal flow)
├── research/customer/        # ICP definitions, prospect lists
├── artifacts/                # Deliverables (sales, marketing, engineering)
├── ops/                      # Supporting files (changes.md, patterns.md)
├── .claude/
│   ├── agents/               # Orchestrators (4 agents)
│   └── skills/               # Flat skills
│       ├── goal-*            # Goal setting and tracking
│       ├── reasoning-*       # Reasoning modes
│       ├── foundations-*     # Business setup
│       ├── sales-*           # Sales pipeline
│       ├── marketing-*       # Campaign execution
│       ├── ops-*             # Operations
│       ├── research-*        # Market research
│       └── engineering/      # Engineering (nested)
```

## Technology Stack

- **AI:** Claude Skills via Claude Code and any supported model
- **Languages:** Python, JS/TS, Bash, Markdown
- **Infrastructure:** Local file system, Git version control

## Getting Started

### Prerequisites
- Claude AI access
- Git for version control
- Understanding of Lean Canvas methodology

### Initial Setup (45-60 minutes)

1. **Install foundation-builder agent and related skills**
   ```bash
   # Copy to .claude/skills/
   ```

2. **Run Phase 0a: Discovery**
   ```text
   use foundation-builder agent, phase: discovery, focus: "[your business idea]"
   ```

3. **Continue through phases** (see [Canvas Setup Guide](docs/foundation/canvas-setup.md))

4. **Activate operations** after validation (see [Timeline Guide](docs/foundation/timeline.md))

## Operating Model

### Goal-Driven (Primary)

```
User objective → goal-setter → Goal with plan → Threads → Artifacts → Learning → Canvas
                                    ↑                                        ↓
                                    └────────── gap-closing actions ─────────┘
```

**Autonomy modes:**
| Mode | Behavior |
|------|----------|
| `auto` | AI creates threads and executes without asking |
| `ask` | AI recommends, waits for approval |
| `hybrid` | Auto for low-impact, ask for high-impact |

### Reactive (Fallback)

For unexpected signals: `Signal → Thread → Link to goal or create new goal`

## Skill Architecture

| Category | Purpose |
|----------|---------|
| `goal-*` | Goal setting and tracking (primary) |
| `reasoning-*` | Reasoning modes (causal, abductive, etc.) |
| `foundations-*` | Business setup, Canvas sections |
| `sales-*` | Sales pipeline activities |
| `marketing-*` | Campaign execution |
| `ops-*` | Operations, content strategy |
| `research-*` | Mode-aware market research |
| `engineering/` | Categorical verification (nested) |

See [All Skills](docs/reference/all-skills.md) for complete reference.

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines on:
- Skill improvements
- Documentation updates
- Architecture enhancements
- Review process

## License

**LeanOS:** MIT License - see [LICENSE](LICENSE)

**Note:** Third-party document-skills removed in v1.2

## Support

**Documentation:** All docs in `docs/` directory

**Philosophy:** Direct, production-ready, question assumptions, AI-operated with human oversight

---

**Last Updated:** 2025-12-10 | **Version:** 2.2 (Goal-Oriented)