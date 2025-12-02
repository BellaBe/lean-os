# LeanOS: AI-Native Operating System for Startups, Small Teams, and Founders

**Status:** Active Development | **Version:** 1.4 (Motion-Aware Marketing) | **Last Updated:** 2025-12-02

AI-native OS that automates 95%+ of business operations for startups, small teams, and founders.

## What It Does

- **Builds + Runs:** Mathematically verified system design, product development, sales, marketing, and business operations
- **Automates decisions:** Claude AI processes engineering, sales, marketing, and business decisions autonomously
- **Single source of truth:** Lean Canvas (15 living documents) drives all operations
- **Human oversight:** <30 min/day for strategic decisions only
- **Learning-driven:** Marketing content created from validated sales learning
- **19 skills, 60+ sub-skills:** Organized by functional type for easy discovery

## Quick Navigation

### Getting Started
- [What is LeanOS?](docs/overview/what-is-leanos.md) - Problem, solution, core principles
- [Architecture Overview](docs/overview/architecture.md) - System layers and data flow
- [Canvas Setup](docs/foundation/canvas-setup.md) - Foundation-building process
- [Timeline Guide](docs/foundation/timeline.md) - Pre-launch to operations

### Operations
- [Sales Workflow](docs/operations/sales-workflow.md) - Strategy → execution → learning
- [Marketing Workflow](docs/operations/marketing-workflow.md) - Learning-driven content
- [Engineering Workflow](docs/operations/engineering-workflow.md) - Verified system generation
- [Daily Routine](docs/operations/daily-routine.md) - Your 5-min review
- [6-Stage Causal Flow](docs/operations/causal-flow.md) - Decision framework

### Skills Reference
- [All Skills](docs/skills/all-skills.md) - Complete skills reference

### Reference
- [Success Metrics](docs/integration/success-metrics.md) - KPIs and targets
- [Troubleshooting](docs/troubleshooting/common-issues.md) - By category
- [FAQ](docs/troubleshooting/faq.md) - Common questions

## Core Principles

1. **AI-first execution:** Claude skills handle operations, not just documentation
2. **Context-shaping over generalization:** Each skill targets specific decision types
3. **Zero redundancy:** Information exists in ONE location only
4. **Evidence-based decisions:** All choices trace to Canvas assumptions
5. **Learning-driven content:** Marketing creates when business generates insights
6. **Mode-aware operations:** Adapts to VENTURE or BOOTSTRAP business models

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
personal-os/
├── strategy/canvas/          # Lean Canvas (15 files) - SOURCE OF TRUTH
├── threads/                  # Decision storage (business, sales, marketing, engineering)
├── research/customer/        # ICP definitions, prospect lists
├── artifacts/                # Deliverables (sales materials, published content, engineering)
├── ops/                      # Daily interface (auto-generated)
└── .claude/skills/           # AI execution layer (19 skills, 60+ sub-skills)
    ├── engineering-*         # 7 skills: System building & verification
    ├── foundations-*         # 4 skills: Business setup & strategy
    ├── ops-*                 # 4 skills: Operational workflows
    ├── research-*            # 2 skills: Market research
    ├── sales-execution/      # Sales pipeline management
    └── marketing-execution/  # Campaign execution
```

## Technology Stack

- **AI:** Claude Sonnet 4.5 via Claude Skills
- **Languages:** Python (FastAPI), Bash, Markdown
- **Infrastructure:** Local file system, Git version control

## Getting Started

### Prerequisites
- Claude AI access (Sonnet 4.5)
- Git for version control
- Understanding of Lean Canvas methodology

### Initial Setup (45-60 minutes)

1. **Install foundation-builder skill**
   ```bash
   # Copy to .claude/skills/foundation-builder/
   ```

2. **Run Phase 0a: Discovery**
   ```text
   skill: foundation-builder
   phase: discovery
   focus: "[your business idea]"
   ```

3. **Continue through phases** (see [Canvas Setup Guide](docs/foundation/canvas-setup.md))

4. **Activate operations** after validation (see [Timeline Guide](docs/foundation/timeline.md))

## Status & Roadmap

- ✅ **Engineering layer** (8 skills, 27 sub-skills: system architecture → backend → frontend → infrastructure)
- ✅ **Sales foundation** (ICP, narratives, materials, execution)
- ✅ **Marketing foundation** (motion-aware GTM, content workflow, channel optimization)
- ✅ **Dual-mode support** (Venture/Bootstrap with mode-aware decision making)
- ✅ **Skill restructuring** (Type-prefixed naming for easy discovery)
- 📋 Ops dashboard auto-generation
- 🔮 Full automation (customer success, fundraising)

## Skill Architecture (v1.4)

**19 skills organized by functional type:**

| Prefix | Count | Purpose |
|--------|-------|---------|
| `engineering-*` | 7 | System building & mathematical verification |
| `foundations-*` | 4 | Business setup, ICP, narratives |
| `ops-*` | 4 | Causal flow, dashboards, metrics |
| `research-*` | 2 | Mode-aware market research |
| `sales-*` | 1 | Sales pipeline execution |
| `marketing-*` | 1 | Campaign execution |

**Engineering layer flow:**
```
Requirements → Architecture → Maps → Code → Deployment
     ↓              ↓           ↓       ↓         ↓
  system-      backend-    standard-  frontend-  infrastructure-
  architecture  prover      applier    prover      prover
```

**Key innovations:**
- **Two-phase verification:** Generate maps first, verify composition, then generate code
- **Split standardization:** Define WHAT standards exist, then HOW to apply them
- **Mathematical proofs:** Category theory guarantees correctness at each stage

See [All Skills](docs/skills/all-skills.md) for complete reference.

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

**Last Updated:** 2025-12-02 | **Version:** 1.4 (Motion-Aware Marketing)