# What is LeanOS?

## The Problem

Running a startup manually doesn't scale:

- **Decision bottleneck:** Founder reviews every decision, creating delays
- **No systematic approach:** Ad-hoc processes without traceability
- **Context switching:** Jumping between sales, marketing, engineering, operations
- **Knowledge silos:** Information scattered across tools, documents, conversations
- **Scaling wall:** Can't add headcount fast enough, can't afford specialists

## The Solution

LeanOS is an **AI-native operating system** for startups, small teams, and founders. It automates 95%+ of business operations while maintaining human oversight for strategic decisions.

**Core capabilities:**

- **AI-first execution:** Claude agents process business, sales, marketing, and engineering decisions autonomously
- **Single source of truth:** Lean Canvas (15 living documents) drives all operations
- **6-stage causal flow:** Every decision follows INPUT → HYPOTHESIS → IMPLICATION → DECISION → ACTIONS → LEARNING
- **Impact-based autonomy:** Auto-execute low-impact (<0.8), flag high-impact (≥0.8) for approval
- **Human touchpoint:** ops/today.md - Single daily entry point (auto-generated)
- **Mode-aware operations:** Adapts to VENTURE (scale) or BOOTSTRAP (profit) business models

**Result:** 2-person team operates with 10-person velocity. Founder spends <30 min/day on operations.

---

## Who Is LeanOS For?

**Ideal fit:**
- Technical or non-technical founders running lean startups
- Small teams (1-5 people) wearing multiple hats
- B2B SaaS, services, or product companies
- Teams that want AI augmentation, not replacement
- Founders who value evidence-based decisions over gut feel

**Not ideal for:**
- Large enterprises with established processes
- Teams preferring manual control over every decision
- Companies without clear product/service focus
- Those uncomfortable with AI-assisted operations

---

## Core Principles

### 1. AI-First Execution
Claude skills handle operations, not just documentation. Skills make decisions, generate materials, track performance, and update strategy autonomously.

### 2. Zero Information Duplication
Information exists in ONE location only:
- **Strategy:** `strategy/canvas/` (15 living documents)
- **Decisions:** `threads/{type}/{name}/` (6-stage causal flow)
- **Execution logic:** `.claude/skills/*/SKILL.md`
- **Published materials:** `artifacts/{sales|marketing|engineering}/`

No duplication. Always reference.

### 3. 6-Stage Causal Flow (Universal)
Every decision flows through:
```
Stage 1: INPUT       - Factual observation (not opinion)
Stage 2: HYPOTHESIS  - Canvas assumption being tested
Stage 3: IMPLICATION - Business impact with numbers
Stage 4: DECISION    - Official commitment + alternatives
Stage 5: ACTIONS     - Executable tasks (typed by function)
Stage 6: LEARNING    - Measured outcomes → Canvas updates
```

No shortcuts. All 6 stages required.

### 4. Impact-Based Autonomy
- **<0.8:** Auto-execute, log in thread, proceed autonomously
- **≥0.8:** Flag in `ops/today.md`, wait for human approval
- **Canvas-altering:** Always require approval
- **Customer relationships:** Always human (calls, negotiations)

### 5. Learning-Driven Operations
Marketing creates content when business generates insights. Sales validates marketing assumptions. Engineering builds what sales learns customers need. Everything traces back to Canvas.

### 6. Mode-Aware Operations
LeanOS adapts to your business model:

**VENTURE Mode** (scale-focused):
- Impact formula: `(Strategic Value × Market Size × Defensibility) / 3`
- Tracks: MAU, ARR growth, market share, runway

**BOOTSTRAP Mode** (profit-focused):
- Impact formula: `(Revenue Impact × Time to Cash × Margin) / 3`
- Tracks: MRR, monthly profit, cash flow, LTV:CAC

---

## How It's Different

| Traditional Operations | LeanOS |
|------------------------|--------|
| Manual decision-making (hours per decision) | AI processes 95%+ autonomously |
| Information scattered everywhere | Single source of truth (Canvas) |
| Reactive ("something's broken") | Proactive (anomalies detected, flagged) |
| Context switching all day | Single 5-min daily review |
| Tribal knowledge in founders' heads | Decisions documented in threads |
| Scaling requires hiring | 2-person team, 10-person velocity |

---

## What LeanOS Does

### Engineering Layer (7 skills)
- **System architecture:** Transform requirements into mathematical specifications
- **Backend generation:** Two-phase verification (maps → code)
- **Frontend generation:** Type-safe client from OpenAPI
- **Infrastructure:** Deployment configs with topology proofs
- **Proof composition:** Validate entire chain before deployment

### Foundations Layer (4 skills)
- **Canvas builder:** Orchestrate 10 agents for pre-launch population
- **ICP generator:** Define Ideal Customer Profile per segment
- **Sales narrative:** Generate messaging per customer segment
- **Marketing narrative:** Generate content strategy

### Operations Layer (4 skills)
- **Causal flow:** 6-stage decision orchestrator
- **Content strategy:** Detect campaign opportunities from business learning
- **Ops dashboard:** Auto-generate daily operational dashboards
- **Metrics tracker:** Mode-aware business metrics

### Research Layer (2 skills)
- **Venture research:** TAM sizing, growth analysis, competitive landscape
- **Bootstrap research:** Spend mapping, arbitrage opportunities, immediate revenue

### Execution Layer (2 skills)
- **Sales execution:** Materials, prospecting, outreach, qualification
- **Marketing execution:** Content generation, SEO, distribution, tracking

---

## Success Metrics

**Operational efficiency:**
- Decision latency: <24h (any decision)
- Auto-execution rate: >95% (human approves only high-impact)
- Human review time: <30 min/day

**Information quality:**
- Zero duplication (1 source of truth)
- 100% decision traceability (every action traces to Canvas)
- >95% Canvas auto-update accuracy

**Business velocity:**
- 2-person team operates like 10-person team
- Cost: ~$200/month AI operations vs traditional $200k+/year for specialists
- Time to first revenue: depends on business, but accelerated

---

## What You Need

**Technical:**
- Claude AI access (Sonnet 4.5 recommended)
- Git for version control
- Terminal/command line comfort
- Markdown editing capability

**Business:**
- Clear product or service focus (one at a time)
- Willingness to populate Lean Canvas
- Commitment to evidence-based decisions
- Trust in AI for execution, human for strategy

**Mindset:**
- Accept that 95% of operations happen without your direct input
- Focus on high-leverage activities (strategy, customer relationships)
- Value systematic processes over ad-hoc heroics

---

## Design Philosophy

**Production-ready, not theoretical:** Every skill produces executable outputs. No conceptual frameworks without implementation.

**Evidence over opinion:** All decisions trace to Canvas assumptions or measured outcomes. No gut feelings.

**AI-operated, human-supervised:** AI handles execution. Humans provide strategic direction and maintain relationships.

**Context-shaping over generalization:** Each skill targets specific decision types. Specialized beats generalized.

**Zero redundancy:** Information exists in one place. References, not copies.

---

## Next Steps

1. **Understand architecture:** Read [Architecture Overview](architecture.md)
2. **Learn the flow:** Read [How It Works](how-it-works.md)
3. **Start building:** Follow [Canvas Setup](../foundation/canvas-setup.md)
4. **See timeline:** Review [Timeline Guide](../foundation/timeline.md)

---

**Version:** 2.0
**Last updated:** 2025-11-25
