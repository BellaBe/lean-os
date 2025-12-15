# What is LeanOS?

LeanOS is an **AI-native operating system** for startups, small teams, and founders. It automates 95%+ of business operations while maintaining human oversight for strategic decisions.

**Result:** 1-person team operates with 5-person velocity. Founder spends <30 min/day on operations.

---

## Core Capabilities

- **Goal-driven execution:** Declare objectives, AI decomposes into plans and executes
- **Single source of truth:** Lean Canvas (15 living documents) drives all operations
- **Reasoning gateway:** Routes to appropriate mode (causal, abductive, inductive, analogical, dialectical, counterfactual)
- **Impact-based autonomy:** Auto-execute low-impact (<0.8), flag high-impact for approval
- **Mode-aware operations:** Adapts to VENTURE (scale) or BOOTSTRAP (profit) business models

---

## Core Principles

### 1. Goal-Driven Operation
All work flows from declared objectives:
```
Goal → Plan → Threads → Artifacts → Learning → Canvas
 ↑                                              ↓
 └─────────── gap-closing actions ──────────────┘
```

### 2. Zero Information Duplication
Information exists in ONE location only:
- **Goals:** `strategy/goals/` (objectives with plans + state)
- **Strategy:** `strategy/canvas/` (15 living documents)
- **Decisions:** `threads/{type}/{name}/` (6-stage causal flow)
- **Skills:** `.claude/skills/*/SKILL.md`
- **Artifacts:** `artifacts/{sales|marketing|engineering}/`

### 3. Reasoning Gateway
Non-trivial tasks route through reasoning-gateway:

| Context | Mode |
|---------|------|
| Operational execution | **Causal** (enforced for threads) |
| Anomaly/diagnosis | **Abductive** |
| Pattern detection | **Inductive** |
| Novel situation | **Analogical** |
| Stakeholder conflict | **Dialectical** |
| Decision evaluation | **Counterfactual** |

### 4. Impact-Based Autonomy
- **<0.8:** Auto-execute, log in thread
- **≥0.8:** Flag for human approval
- **Canvas-altering:** Always require approval
- **Customer relationships:** Always human

### 5. Learning-Driven Operations
Marketing creates content when business generates insights. Sales validates marketing assumptions. Engineering builds what sales learns customers need. Everything traces back to Canvas.

### 6. Mode-Aware Operations

| Mode | Focus | Impact Formula |
|------|-------|----------------|
| **VENTURE** | Scale, defensibility | `(Strategic Value × Market Size × Defensibility) / 3` |
| **BOOTSTRAP** | Cash flow, profit | `(Revenue Impact × Time to Cash × Margin) / 3` |

---

## System Architecture

LeanOS operates in layers: Goals → Strategy → Reasoning → Skills → Threads → Artifacts → State.

**Layer breakdown:**

| Layer | Skills | Purpose |
|-------|--------|---------|
| Engineering | 20 | SPEC → BUILD → VERIFY → GEN pipeline |
| Foundations | 10 | Canvas, ICP, sales/marketing narratives |
| Reasoning | 6 modes | Causal, abductive, inductive, analogical, dialectical, counterfactual |
| Goals | 2 | goal-setter, goal-tracker |
| Sales | 6 | Prospecting, qualification, materials, outreach |
| Marketing | 5 | Content strategy, generation, delivery |
| Research | 2 | Venture/bootstrap market research |
| Actions | 11 | Deliverable contracts for outputs |

**Full catalog:** [all-skills.md](all-skills.md)
**Architecture details:** [architecture.md](architecture.md)

---

## Success Metrics

**Operational efficiency:**
- Decision latency: <24h (any decision)
- Auto-execution rate: >95%
- Human review time: <30 min/day

**Information quality:**
- Zero duplication (1 source of truth)
- 100% decision traceability
- >95% Canvas auto-update accuracy

**Business velocity:**
- 2-person team operates like 10-person team
- Cost: ~$200/month AI vs $200k+/year specialists

---

## Technical Requirements

- Claude AI access
- Git for version control
- Terminal/command line comfort
- Markdown editing capability

---

## Design Philosophy

- **Production-ready:** Every skill produces executable outputs
- **Evidence over opinion:** All decisions trace to Canvas or measured outcomes
- **AI-operated, human-supervised:** AI handles execution, humans provide strategy
- **Context-shaping:** Each skill targets specific decision types
- **Zero redundancy:** Information exists in one place

---

## Using LeanOS for Your Project

LeanOS is a **base system** that you copy to create project-specific instances.

**To create a new project:**
1. Copy LeanOS base to `{project-name}/`
2. Create `docs/reference/what-is-{project}.md` using [the template](what-is-PROJECT.template.md)
3. Populate Canvas in `strategy/canvas/`
4. Create first goal using `goal-setter`

---

## Next Steps

1. [Architecture Overview](architecture.md) — system layers and data flow
2. [Canvas Setup](../workflows/canvas-setup.md) — foundation-building process
3. [All Skills](all-skills.md) — complete skills reference

---

**Version:** 3.0
