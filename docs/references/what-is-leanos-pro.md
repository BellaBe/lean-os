# What is LeanOS Pro?

**A swiss knife for building and operating a business.**

LeanOS absorbs the knowledge required to build and run a business — strategy, product, engineering, sales, marketing, customer success, operations — and makes it available through specialized agents and skills.

**Result:** One person operates with 5-10x effectiveness.

---

## Four Architectural Principles

| Principle | What It Means |
|-----------|---------------|
| **Single location** | Everything in one place. No scattered docs, no context switching. |
| **Strategy in Canvas** | 16 living documents that drive all decisions. The context is all there. |
| **State in Artifacts** | Deliverables and outputs stored by domain. Source of truth. |
| **Operations in Threads** | Work executes through causal reasoning. Every action is traceable. |

---

## The Five Functions

```
STRATEGIZE → CREATE → GROW → RETAIN → OPERATE
                 ↑__________|__________|
                       INTELLIGENCE
```

Every business runs on five core functions. LeanOS has agents and skills for each.

### STRATEGIZE

*Figure out what to build and why.*

- **Market understanding:** TAM/SAM/SOM, competitive landscape, customer segments, problem validation
- **Business model:** Value proposition, pricing strategy, unit economics, growth architecture
- **Execution planning:** Goal setting, experiment design, channel discovery, compliance, fundraising

### CREATE

*Build products, design systems, and content.*

- **Code generation:** Natural language → Production Python/FastAPI (4-stage IR pipeline), React + Tailwind, Shopify
- **Design systems:** Intent extraction → Foundations → Tokens → Policies → Component contracts (base, app, marketing, AI) → Figma specs
- **Product design:** Strategy → User stories → Flows → Specs → Engineering handoff, DHM prioritization
- **Content production:** Blog posts, emails, landing pages, pitch decks, case studies, battle cards

### GROW

*Acquire customers.*

- **Outbound:** Account research, decision-maker discovery, personalized sequences, qualification
- **Inbound:** Lead scoring, personalized response, nurture sequences, content attribution
- **Campaigns:** Planning, channel prioritization, budget allocation, content strategy
- **Partnerships:** Discovery, qualification, enablement, co-sell coordination

### RETAIN

*Keep customers and grow revenue.*

- **Customer success:** Health scores, adoption tracking, milestone monitoring, QBR preparation
- **Retention:** Churn prediction, save playbooks, executive escalation, competitive defense
- **Expansion:** Opportunity identification, renewal management, proposal generation, upsell execution

### OPERATE

*Make it all run smoothly.*

- **Signal processing:** Collect, deduplicate, enrich, route to execution engines
- **Scoring models:** PQL, fit, risk, health — with continuous calibration
- **Resource allocation:** Goal-to-engine mapping, priority ranking, capacity planning
- **Performance:** Engine metrics, benchmark comparison, pattern detection, hypothesis validation

### INTELLIGENCE

*Powers all five functions.*

- **Reasoning:** Causal, abductive, inductive, analogical, dialectical, counterfactual
- **Structuring:** Alignment, constraint, decision, diagnostic, evaluative, planning, prescriptive, risk, validation
- **Domain expertise:** Security, cryptography, behavioral science, category theory
- **Knowledge synthesis:** Process expert sources → structured insights → actionable playbooks

---

## How It Works

### Execution Model

```
You (decisions)
    ↓
Agents (orchestration)
    ↓
Skills (execution)
```

| Layer | What It Does | Count |
|-------|--------------|-------|
| **Agents** | Orchestrate multi-step workflows, route to skills, maintain context | 41 |
| **Skills** | Execute atomic tasks with domain expertise | 186 |
| **You** | Approve high-impact decisions, set direction | — |

**Example:**
```
You: "Get me 10 qualified leads in financial services"
    ↓
sls-outbound-manager agent activates
    ↓
sls-researching-prospects skill → finds companies
sls-finding-contacts skill → identifies decision-makers
sls-personalizing-outreach skill → drafts sequences
sls-qualifying-prospects skill → scores and filters
    ↓
You: Review 10 qualified leads
```

### Information Architecture

```
strategy/
├── canvas/     ← Living strategy (16 sections)
└── goals/      ← What you're trying to achieve

threads/        ← Operational execution (causal reasoning)

artifacts/      ← Deliverables and outputs
```

Information exists in ONE location only. Threads reference Canvas. Goals derive from Canvas. Artifacts link to Threads.

### Autonomy Model

```
Impact = Reversibility × Scope × Cost

Impact < 0.8  → Auto-execute
Impact ≥ 0.8  → Request approval
```

| Impact | Behavior | Examples |
|--------|----------|----------|
| < 0.8 | Auto-execute | Research account, draft email, update health score |
| ≥ 0.8 | Request approval | Send outreach, publish content, change pricing |

| Mode | Behavior |
|------|----------|
| `auto` | Execute all actions, notify on completion |
| `ask` | Request approval for any action |
| `hybrid` | Auto-execute low-impact, ask for high-impact |

### Decision Framework

Every decision follows the 6-stage causal flow:

```
1. INPUT        What's the context? What triggered this?
      ↓
2. HYPOTHESIS   What do we believe is true?
      ↓
3. IMPLICATION  If true, what changes? What should we do?
      ↓
4. DECISION     What are we actually doing? Why?
      ↓
5. ACTIONS      Specific steps with ownership
      ↓
6. LEARNING     What happened? What did we learn? → Updates Canvas
```

This flow is enforced for all threads. No action without reasoning. No reasoning without learning.

### Operating Modes

| Mode | Optimizes For |
|------|---------------|
| **BOOTSTRAP** | Profitability, cash flow, fast decisions |
| **VENTURE** | Growth rate, market size, defensibility |

Mode is set in `strategy/canvas/00.mode.md` and affects impact calculations, prioritization, resource allocation, and experiment design.

---

## System Scope

| Component | Count |
|-----------|-------|
| Agents | 41 |
| Skills | 186 |
| Canvas Sections | 16 |
| Reasoning Modes | 6 |
| Structuring Modes | 11 |

**Verticals covered:**
- Engineering (backend IR pipeline, frontend, testing, design systems)
- Product (core, PLG activation, conversion, experiments, growth)
- Sales (outbound, partnerships, enablement, strategy)
- Marketing (inbound, content, campaigns, strategy)
- Customer (success, expansion, retention, advocacy)
- RevOps (signals, scoring, allocation, evaluation)
- Foundations (setup, research, model, launch, canvas audit/validation)
- Intelligence (security, behavioral science, knowledge synthesis)

---

## Cost Comparison

| Item | Traditional | LeanOS |
|------|-------------|--------|
| SaaS stack | $5-20k/month | $0 |
| AI costs | Varies | ~$200/month |
| Specialists | $200k+/year | $0 |
| **Total** | **$300k+/year** | **~$2,400/year** |

---

## Success Metrics

**Operational efficiency:**
- Auto-execution rate: >95%
- Human involvement: High-impact decisions only

**Information quality:**
- Zero duplication (single source of truth)
- 100% decision traceability
- All context in one place

**Business effectiveness:**
- 1-person team operates with 5-10x effectiveness

---

## Best Fit

- Solo founders who want to operate a complete business
- Small teams (1-3) with clear roles
- Bootstrapped or venture-backed startups
- Comfort with CLI/git and markdown as your operating system

---

## Getting Started

1. Copy LeanOS Pro base to `{project-name}/`
2. Populate Canvas in `strategy/canvas/`
3. Create first goal using `sys-defining-goals`
4. Let LeanOS execute

---

## References

- [Capabilities Detail](./leanos-capabilities.md) — Agent and skill breakdowns
- [Agents & Skills Index](./agents-skills-index.md) — Complete catalog
