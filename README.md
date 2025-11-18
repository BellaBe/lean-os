# LeanOS: AI-Native Operating System for Founders

**Status:** Active Development | **Version:** 1.0 (Marketing Layer Complete)

AI-native OS that automates 95%+ of startup operations. Built for GlamYouUp, designed for universal application.

## What It Does

- **Automates decisions:** Claude AI processes sales, marketing, and business decisions autonomously
- **Single source of truth:** Lean Canvas (15 living documents) drives all operations
- **Human oversight:** <30 min/day for strategic decisions only
- **Learning-driven:** Marketing content created from validated sales learning

## Quick Navigation

### Getting Started
- [What is LeanOS?](docs/overview/what-is-leanos.md) - Problem, solution, core principles
- [Architecture Overview](docs/overview/architecture.md) - System layers and data flow
- [Canvas Setup](docs/foundation/canvas-setup.md) - Foundation-building process
- [Timeline Guide](docs/foundation/timeline.md) - Pre-launch to operations

### Operations
- [Sales Workflow](docs/operations/sales-workflow.md) - Strategy → execution → learning
- [Marketing Workflow](docs/operations/marketing-workflow.md) - Learning-driven content
- [Daily Routine](docs/operations/daily-routine.md) - Bella's 5-min review
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

## Directory Structure

```text
lean-os/
├── strategy/canvas/          # Lean Canvas (15 files) - SOURCE OF TRUTH
├── threads/                  # Decision storage (business, sales, marketing)
├── research/customer/        # ICP definitions, prospect lists
├── artifacts/                # Deliverables (sales materials, published content)
├── ops/                      # Daily interface (auto-generated)
├── engineering/              # Technical specs (active)
└── .claude/skills/           # AI execution layer
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

- ✅ Sales foundation (ICP, narratives, materials, execution)
- ✅ Marketing foundation (strategy, content workflow, SEO, distribution)
- 🚧 Validation (GlamYouUp DTC segment testing)
- 📋 Ops dashboard auto-generation
- 🔮 Full automation (customer success, fundraising, engineering)

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines on:
- Skill improvements
- Documentation updates
- Architecture enhancements
- Review process

## License

**LeanOS:** MIT License - see [LICENSE](LICENSE)

**Third-party components:** document-skills (© Anthropic, PBC) - see [THIRD-PARTY-LICENSES.md](THIRD-PARTY-LICENSES.md)

## Support

**Maintainer:** Bella Belgarokova ([LinkedIn](https://www.linkedin.com/in/bellabelgarokova/))

**Documentation:** All docs in `docs/` directory

**Philosophy:** Direct, production-ready, question assumptions, AI-operated with human oversight

---

**Last Updated:** 2024-11-18 | **Version:** 1.0 (Marketing Layer Complete)