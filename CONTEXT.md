# LeanOS: Universal AI-Native Operating System for Startups

**You're helping Bella design LeanOS** - a universal operating system that enables AI-first startup operations with minimal human intervention. Built for GlamYouUp (AI fashion recommendations), **designed for universal application to any business**.

Previously had 160+ scattered markdown files causing information overload and duplication. Goal: Build production-ready system where Claude AI autonomously executes 95%+ of business operations.

---

## Architecture Philosophy

**Core principles validated through production use:**

1. **Skills-first design** - Claude skills ARE the execution layer, not documentation
2. **Context-shaping is critical** - Specific, targeted instructions beat generic frameworks
3. **No redundant files** - Information exists in ONE location only
4. **Domain knowledge lives with implementation** - Each skill contains execution logic + context
5. **Thread-based decisions** - Complete decision narrative in one folder (6-stage causal flow)
6. **Mode-aware operations** - Adapts to VENTURE or BOOTSTRAP business models

---

## Current Structure (Production-Ready)

```
lean-os/
├── .claude/skills/           # AI execution layer (14 operational skills)
│   ├── Engineering (Building Systems)
│   │   ├── category-theoretic-system-design/  # Requirements → production-ready systems
│   │   └── standardization-layer/             # Cross-cutting concerns (auth, validation)
│   │
│   ├── Business Operations (Running Systems)
│   │   ├── Strategy & Foundation
│   │   │   ├── foundation-builder/            # 10-agent Canvas orchestrator (pre-launch)
│   │   │   ├── icp-generator/                 # ICP per segment
│   │   │   ├── sales-narrative/               # Sales messaging per segment
│   │   │   └── marketing-narrative/           # Content strategy per product
│   │   │
│   │   ├── Market Research (Mode-Aware)
│   │   │   ├── market-research-venture/       # TAM, growth, competitive landscape
│   │   │   └── market-research-bootstrap/     # Current spend, arbitrage, immediate revenue
│   │   │
│   │   ├── Sales Execution
│   │   │   └── sales-execution/               # Materials, prospecting, outreach orchestrator
│   │   │       ├── materials-generation       # (Sub-skill: Pitch decks, emails, scripts)
│   │   │       ├── prospect-research          # (Sub-skill: Find companies via web_search)
│   │   │       ├── contact-finding            # (Sub-skill: Find decision-makers)
│   │   │       ├── outreach-sequencing        # (Sub-skill: Email/phone cadences)
│   │   │       └── qualification-support      # (Sub-skill: Discovery call prep)
│   │   │
│   │   ├── Marketing Strategy
│   │   │   └── content-strategy/              # Scan threads for campaign opportunities (standalone, daily)
│   │   │
│   │   ├── Marketing Execution
│   │   │   └── marketing-execution/           # Campaign orchestrator (Stage 5 only)
│   │   │       ├── content-generation         # (Sub-skill: Create educational drafts)
│   │   │       ├── seo-optimization           # (Sub-skill: Apply keywords naturally)
│   │   │       ├── content-distribution       # (Sub-skill: Publish multi-channel)
│   │   │       └── performance-tracking       # (Sub-skill: Measure impact, insights)
│   │   │
│   │   └── Orchestration & Operations
│   │       ├── causal-flow/                   # 6-stage decision orchestrator (universal)
│   │       ├── ops-dashboard/                 # Auto-generate ops/ dashboards (today.md, velocity.md, patterns.md)
│   │       └── business-metrics-tracker/      # Mode-aware business metrics (revenue, profitability, growth)
│   │
│   └── Utility (Third-Party - DO NOT MODIFY)
│       └── document-skills/                   # Document handling (© Anthropic - use only)
│
├── strategy/canvas/         # Lean Canvas (15 living docs) = SOURCE OF TRUTH
│   ├── 00-business-model-mode.md             # VENTURE vs BOOTSTRAP (impacts all decisions)
│   ├── 01-context.md                         # Product, market, founder context
│   ├── 02-customer.md ... 14-timeline.md     # Complete Canvas framework
│   └── 10-assumptions.md                     # Hypotheses being tested
│
├── threads/                 # Thread-based decisions (complete narrative per thread)
│   ├── business/{name}/     # Strategic decisions (segment splits, pivots, etc.)
│   ├── sales/{name}/        # Sales pipeline + campaigns
│   └── marketing/{name}/    # Marketing campaigns (learning-driven)
│
├── ops/                     # Daily interface (will auto-generate via ops-dashboard skill)
│   ├── today.md             # Human reads in 5 min, approves high-impact decisions
│   ├── velocity.md          # Operational metrics
│   ├── patterns.md          # Detected patterns across threads
│   └── changes.md           # Canvas update history
│
├── artifacts/               # Published materials (deliverables, not working files)
│   ├── sales/               # Pitch decks, narratives, call scripts (per segment)
│   ├── marketing/           # Published campaigns, narratives, performance data
│   └── business/            # Business metrics dashboards (mode-aware)
│
├── research/                # Customer, market, product insights
│   ├── customer/icp/        # ICP definitions per segment (YAML + markdown)
│   ├── customer/personas/   # Buyer personas
│   └── market/              # Market research (mode-specific: TAM vs current spend)
│
├── engineering/             # Active - service specs, standards, domain knowledge
│   ├── services/            # Service blueprints (category-theoretic)
│   ├── standards/           # Cross-cutting standards (auth, validation, etc.)
│   └── domain/              # Domain knowledge documents
│
└── meeting-notes/           # Customer conversation records
```

---

## Operational Principles (Production-Validated)

### What Works

✅ **Skills are the execution layer** - Process definitions embedded in Claude skills, not separate markdown
✅ **Thread-based storage** - Complete decision narrative in one folder (6-stage causal flow)
✅ **Ops generates views** - threads/ is source, ops/ synthesizes for human consumption
✅ **Lean Canvas stays central** - All strategic decisions trace back to Canvas
✅ **Archive completed threads** - Prevents clutter, maintains decision history
✅ **Engineering active workstream** - Service specs, domain knowledge, standards ready for implementation
✅ **Context-shaping over generalization** - Specific instructions beat generic frameworks
✅ **Mode-aware operations** - VENTURE vs BOOTSTRAP changes decision criteria, metrics, research approach
✅ **Skills coordination via standardization-layer** - Not via centralized control
✅ **Learning-driven marketing** - Content created from validated sales learning (not arbitrary calendars)

### What Doesn't Work

❌ **Generic skills** - Lose effectiveness, must be context-specific
❌ **Redundant files** - Information duplication kills maintainability
❌ **Centralized control** - Skills coordinate autonomously
❌ **Documentation-as-execution** - Skills execute, they don't just document
❌ **Marketing before sales validation** - Initial content from Canvas/research, refined from sales learning
❌ **One-size-fits-all metrics** - VENTURE vs BOOTSTRAP require different success criteria

---

## Current System Status

### ✅ Complete & Operational

**Engineering Layer:**
- category-theoretic-system-design (requirements → production systems)
- standardization-layer (cross-cutting concerns)

**Business Operations Layer:**
- foundation-builder (10-agent Canvas orchestrator)
- icp-generator (per segment)
- sales-narrative (per segment)
- marketing-narrative (per product)
- market-research-venture (TAM, growth, competitive)
- market-research-bootstrap (current spend, arbitrage)
- sales-execution (5 sub-skills operational)
- content-strategy (standalone, daily automated)
- marketing-execution (4 sub-skills operational)
- causal-flow (6-stage decision orchestrator)
- business-metrics-tracker (mode-aware dashboards)

**Foundation:**
- Dual-mode support (VENTURE vs BOOTSTRAP)
- 6-stage causal flow (universal decision framework)
- Canvas-first architecture (15 living documents)
- Thread-based decision storage

### 🚧 In Progress

- **ops-dashboard skill** - Auto-generate ops/today.md, velocity.md, patterns.md from thread data
- **GlamYouUp validation** - Testing DTC segment with real customers
- **Thread archival automation** - When to archive vs continue threads

### 📋 Planned

- Full automation (customer success, fundraising)
- Additional mode support (HYBRID - Bootstrap until profitable, then Venture)
- Cross-thread pattern detection (automated insights)

---

## Skills Inventory (14 Operational + 1 Third-Party)

### Engineering Skills (Building Systems)

| Skill | Purpose | Invocation Trigger |
|-------|---------|-------------------|
| **category-theoretic-system-design** | Transform natural language requirements into production-ready systems using category theory | Building technical systems |
| **standardization-layer** | Apply cross-cutting concerns (auth, validation, response formats) to microservices | Standardizing microservices |

### Business Operations Skills (Running Systems)

**Strategy & Foundation:**

| Skill | Purpose | Invocation Trigger |
|-------|---------|-------------------|
| **foundation-builder** | Orchestrate 10 agents for Canvas population and validation | Canvas needs population (pre-launch) |
| **icp-generator** | Define Ideal Customer Profile per segment | New customer segment identified |
| **sales-narrative** | Generate sales messaging per segment | ICP updated or Canvas positioning changes |
| **marketing-narrative** | Generate content strategy per product | Canvas positioning changes |

**Market Research (Mode-Aware):**

| Skill | Purpose | Invocation Trigger |
|-------|---------|-------------------|
| **market-research-venture** | Analyze TAM, growth rates, competitive landscape, scalability potential | VENTURE mode: Canvas section 02 (market sizing) |
| **market-research-bootstrap** | Map current spend, arbitrage opportunities, immediate revenue potential | BOOTSTRAP mode: Canvas section 02 (market sizing) |

**Sales Execution:**

| Skill | Purpose | Invocation Trigger |
|-------|---------|-------------------|
| **sales-execution** | Orchestrate materials, prospecting, outreach, qualification | Sales activities needed |
| ↳ *materials-generation* | Auto-generate pitch decks, emails, scripts | Canvas changes require material updates |
| ↳ *prospect-research* | Find target companies (web_search) | Sales campaign: prospect identification |
| ↳ *contact-finding* | Find decision-makers (web_search) | Prospect identified, need contact info |
| ↳ *outreach-sequencing* | Generate email/phone cadences | Sales campaign: sequence design |
| ↳ *qualification-support* | Discovery call prep | Demo scheduled, need prep materials |

**Marketing Strategy:**

| Skill | Purpose | Invocation Trigger |
|-------|---------|-------------------|
| **content-strategy** | Scan threads for campaign opportunities (standalone, daily automated) | Daily (automated scan of threads/*/6-learning.md) |

**Marketing Execution:**

| Skill | Purpose | Invocation Trigger |
|-------|---------|-------------------|
| **marketing-execution** | Orchestrate campaign execution (Stage 5 only) | High-priority campaign approved (from content-strategy) |
| ↳ *content-generation* | Create educational drafts | Marketing thread Stage 5 action |
| ↳ *seo-optimization* | Apply keywords naturally | Content draft ready for SEO |
| ↳ *content-distribution* | Publish multi-channel | Content approved, ready to publish |
| ↳ *performance-tracking* | Measure impact, feed insights | Content published, tracking performance |

**Orchestration & Operations:**

| Skill | Purpose | Invocation Trigger |
|-------|---------|-------------------|
| **causal-flow** | 6-stage decision flow orchestrator (universal) | Strategic decision needed (any type) |
| **ops-dashboard** | Auto-generate daily ops/ dashboards | Daily (automated generation) |
| **business-metrics-tracker** | Generate mode-aware business metrics dashboards | Weekly/monthly business review |

**Utility (Third-Party):**

| Skill | Purpose | Restrictions |
|-------|---------|--------------|
| **document-skills** | Document format handling (docx, pdf, pptx, xlsx) | © Anthropic, PBC - Use only, DO NOT modify, copy, or redistribute |

---

## Skills Coordination Patterns

### No Centralized Control

Skills coordinate through **data contracts** (Canvas, threads, artifacts), not through a central orchestrator.

**Example: Sales narrative regeneration when Canvas changes**

```
Canvas update (foundation-builder)
    ↓
Thread Stage 6 (Learning) validates hypothesis
    ↓
Canvas section updated (strategy/canvas/07-uvp.md)
    ↓
sales-narrative detects Canvas change (reads 07-uvp.md)
    ↓
Regenerates narratives (artifacts/sales/{segment}/narratives/)
    ↓
sales-execution/materials-generation detects narrative change
    ↓
Regenerates materials (artifacts/sales/{segment}/materials/)
```

**No explicit orchestration. Skills watch for data changes and react.**

### Skill Invocation Rules

1. **Engineering skills** - Invoked explicitly when building systems
2. **Foundation skills** - Invoked explicitly during Canvas population or updates
3. **Sales execution** - Invoked explicitly for sales activities
4. **Marketing strategy (content-strategy)** - Invoked automatically (daily scan)
5. **Marketing execution** - Invoked explicitly after campaign approval
6. **Orchestration (causal-flow)** - Invoked explicitly for strategic decisions
7. **Operations (ops-dashboard, business-metrics-tracker)** - Invoked automatically (daily/weekly)

---

## Open Design Questions

### Current Focus Areas

1. **Ops dashboard auto-generation** - How does ops-dashboard parse thread data without hardcoded logic?
2. **Thread archival criteria** - What triggers thread archive vs thread continuation?
3. **Cross-thread pattern detection** - How to detect patterns across business/sales/marketing threads?
4. **Skill version management** - How to evolve skills without breaking existing threads?
5. **Mode switching** - BOOTSTRAP → VENTURE transition (when to switch, what changes?)

### Skills Coordination

- ✅ Solved: Skills coordinate via data contracts (Canvas, threads, artifacts)
- ✅ Solved: standardization-layer ensures consistency without centralized control
- ⏳ In progress: Automated triggers (daily scans, threshold-based alerts)

### Daily Workflow

**Current (Manual):**
1. Bella reads ops/today.md (manually updated)
2. Approves high-impact decisions
3. Executes customer calls
4. Reviews thread updates

**Target (Automated - via ops-dashboard skill):**
1. ops-dashboard auto-generates ops/today.md from thread data
2. Bella reads in 5 minutes
3. Approves 2-3 high-impact items
4. Done (<30 min total)

---

## Design Constraints (Non-Negotiable)

**System-level constraints:**
- ✓ AI-first execution - Claude skills handle operations, not just documentation
- ✓ Context-shaping precision - Each skill targets specific decision type, no generic prompts
- ✓ Zero redundancy - Information exists in ONE location only
- ✓ Human touchpoint: ops/today.md - Single daily entry point (when auto-generated)
- ✓ No migration pain - System evolves in-place, no big-bang refactors
- ✓ Evidence-based decisions - All choices trace to Canvas assumptions or thread results
- ✓ Skills coordinate via data contracts - Not via centralized control
- ✓ Mode-aware operations - VENTURE vs BOOTSTRAP impacts decision criteria, metrics, research

**Universal applicability:**
- ✓ Product-agnostic - Works for any SaaS, marketplace, platform, or product business
- ✓ Stage-agnostic - Works from pre-launch (foundation-builder) to growth (full operations)
- ✓ Mode-aware - Adapts to VENTURE (scale-focused) or BOOTSTRAP (profit-focused)
- ✓ Segment-flexible - ICPs and sales narratives per **segment**, not hardcoded
- ✓ Single product focus - One product at a time (intentional constraint)

---

## Universal Application Guide

**LeanOS works for any startup because:**

1. **Canvas-first foundation** - Lean Canvas methodology is universal (problem, solution, segments, UVP, channels, revenue, costs, metrics, unfair advantage)
2. **Segment-based execution** - ICPs and sales narratives generated per segment, not hardcoded for fashion/SaaS
3. **Mode-aware operations** - VENTURE vs BOOTSTRAP covers 99% of startup business models
4. **6-stage causal flow** - Universal decision framework (works for any business decision)
5. **Skills-first architecture** - Skills execute operations (not product-specific documentation)

**To apply LeanOS to a new business:**

```
1. Set mode: strategy/canvas/00-business-model-mode.md (VENTURE or BOOTSTRAP)
2. Populate Canvas: Invoke foundation-builder skill (45-60 min)
3. Define segments: strategy/canvas/04-segments.md (1-3 customer segments)
4. Generate ICPs: Invoke icp-generator per segment
5. Generate narratives: Invoke sales-narrative (per segment) + marketing-narrative (per product)
6. Activate operations: Sales execution + Marketing execution + Ops dashboard
```

**No code changes required. System adapts via Canvas + mode configuration.**

---

## Bella's Style (Design for This)

- **Direct, no fluff** - Gets frustrated with repetition, values conciseness
- **Questions assumptions** - "Why not simpler?" is a constant refrain
- **Values production systems over theory** - Must be executable, not just conceptual
- **Thinks in systems and flows** - Data flow diagrams, coordination patterns, feedback loops
- **Tech stack:** Python, FastAPI, microservices, category theory, functional programming

**When designing for Bella:**
- Show data flows, not just descriptions
- Prove with examples, not just assertions
- Challenge redundancy aggressively
- Prioritize production readiness over academic correctness
- Be precise about what works vs what's theoretical

---

## Current Phase: Validation + Ops Automation

**GlamYouUp validation (DTC segment):**
- ✅ Canvas complete (15 documents populated)
- ✅ ICP defined (DTC fashion brands)
- ✅ Sales narratives generated (economic buyer, technical buyer, end user)
- ✅ Marketing narratives generated (content pillars, brand voice, SEO strategy)
- 🚧 DTC outreach campaign (testing ICP + narratives)
- 📋 First customer demo (validate problem-solution fit)

**Ops dashboard automation:**
- ✅ business-metrics-tracker skill complete (mode-aware dashboards)
- 🚧 ops-dashboard skill (auto-generate ops/today.md from threads)
- 📋 Automated daily scans (content-strategy already operational)

**Next actions:**
1. Complete ops-dashboard skill (parse thread data, generate ops/today.md)
2. Validate GlamYouUp DTC campaign (10 prospects contacted → learning captured)
3. Prove marketing activation (2-3 foundational content pieces published)
4. Document patterns (what worked, what needs refinement)

---

## Success Metrics (How We Know It Works)

**Operational efficiency (Universal):**
- Decision latency: <24h (target)
- Auto-execution rate: >95% (target)
- Human review time: <30 min/day (target)

**Mode-Specific Metrics:**

**VENTURE Mode:**
- MAU, ARR, growth rate, market share, runway, CAC, LTV

**BOOTSTRAP Mode:**
- MRR, monthly profit, profit margin, cash flow, CAC, LTV, time to profitability

**Sales performance (Universal):**
- Lead response time: <24h
- Qualification rate: >40%
- Demo booking rate: >40%
- Close rate: >50% of qualified

**Marketing performance (Universal):**
- Content pieces per learning event: 1-3
- Traffic from content: {sessions}
- Demos from content: {conversions}
- Top performer rate: >50%

**Canvas integrity (Universal):**
- Auto-update accuracy: >95%
- Assumption validation rate: tracked per thread
- Zero duplication: 100%

---

## Keep Challenging

**When working with Bella, always challenge:**

1. **Redundancy** - If it exists in a skill, why does it exist elsewhere?
2. **Generalization** - Is this skill losing effectiveness by being too generic?
3. **Coordination** - Do skills know how to work together without centralized control?
4. **Production readiness** - Can this execute today, or is it theoretical?
5. **Universal applicability** - Does this work for any business, or just GlamYouUp?
6. **Mode-awareness** - Does this decision/metric/process respect VENTURE vs BOOTSTRAP mode?

**Red flags to call out:**
- "We'll need to customize this for each business" (should be Canvas-driven)
- "This is a nice-to-have" (remove it, focus on must-haves)
- "Let's add a field for future use" (YAGNI - You Aren't Gonna Need It)
- "This will make it more flexible" (flexibility often kills effectiveness)
- "We should coordinate these skills explicitly" (prefer data contracts over explicit coordination)

---

## Version History

- **v1.0** (2025-09-15): Initial GlamOS design (GlamYouUp-specific)
- **v1.1** (2025-10-20): Extracted LeanOS (universal framework)
- **v1.2** (2025-11-20): Engineering + Operations complete, dual-mode support, 14 operational skills

**Status:** Production-ready for GlamYouUp, designed for universal application

**Maintainer:** Bella Belgarokova ([LinkedIn](https://www.linkedin.com/in/bellabelgarokova/))
