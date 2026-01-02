# Canvas Setup: Foundation Building Process

The Lean Canvas (15 living documents in `strategy/canvas/`) is your **single source of truth**. Everything in LeanOS—sales narratives, marketing content, ICP definitions, business decisions—flows from the Canvas.

## Why Canvas First?

**Canvas is evidence-based, not aspirational.** Every section must be validated through research, customer conversations, or experimentation.

Without Canvas:
- No foundation for ICP generation
- No basis for sales narratives
- No strategy for marketing content
- No assumptions to test
- No single source of truth

## Canvas Creation Process

Use the `foundation-builder` skill to populate and validate all 15 Canvas sections through a structured 5-phase process.

---

## Phase 0: Business Model Mode Selection

**Goal:** Declare your business model approach (VENTURE vs BOOTSTRAP vs HYBRID)

**Why first?** Mode determines research focus, decision criteria, and success metrics throughout Canvas building.

**Process:**
1. Create `strategy/canvas/00.mode.md`
2. Declare mode: VENTURE, BOOTSTRAP, or HYBRID
3. Document rationale

**Decision criteria:**

**Choose VENTURE if:**
- Raising or have raised funding
- Market requires scale to win (winner-take-all)
- Building platform/network effects
- Timeline: 7-10 years to exit
- Okay with burn for growth

**Choose BOOTSTRAP if:**
- Self-funded, need profitability fast
- Can win without scale (service, niche)
- Building clear solution to known problem
- Timeline: Cash flow now, exit optional
- Must be profitable from start

**Choose HYBRID if:**
- Want to prove PMF before raising
- Bootstrap validates, venture scales
- Option to stay bootstrapped if profitable

**Human time:** 15-30 minutes (strategic decision)

**Impact:** Determines which market research skill to use in Phase 0a

---

## Phase 0a: Discovery (Market Intelligence)

**Goal:** Understand the market, identify real customer problems, define segments

**Agents activated:**
- `market-intelligence`: Market analysis, TAM/SAM/SOM, competitive landscape
- `problem-solution-fit`: Problem validation through customer research

**Canvas sections populated:**
- 07.uvp.md (Unique Value Proposition - single sentence)
- 08.unfair.md (Unfair advantages, secret sauce)
- 09.solution.md (MVP feature set, solution approach)
- 11.channels.md (Channels strategy)
- 12.revenue.md (Revenue model, pricing tiers)
- 13.metrics.md (Key metrics, unit economics)

**Example invocation:**
```
skill: foundation-builder
phase: discovery
focus: "{your business idea}"

Output: 6 Canvas sections with evidence-based market intelligence
```

**Human input required (1-2 hours):**
- Provide initial business idea and constraints (15 min)
- Review Canvas sections 01-06 for accuracy (30 min)
- Approve market intelligence findings (15 min)
- Identify customer segments to interview (15 min)

**AI execution time:** 2-3 hours (research, analysis, Canvas population)

**Real-world validation (1-2 weeks):**
- Customer problem interviews (5-10 interviews)
- Competitive product analysis
- Market trend validation
- **This is the actual bottleneck**

**Total elapsed:** 1-2 weeks (limited by real-world validation, not AI)

---

## Phase 0b: Definition (Value Proposition & Business Model)

**Goal:** Define unique value, positioning, revenue model, and MVP scope

**Agents activated:**
- `value-proposition`: UVP articulation, positioning, messaging hierarchy
- `business-model`: Revenue design, pricing strategy, unit economics
- `problem-solution-fit`: MVP definition, solution design

**Canvas sections populated:**
- 07-uvp.md (Unique Value Proposition - single sentence)
- 08-advantage.md (Unfair advantages, secret sauce)
- 09-solution.md (MVP feature set, solution approach)
- 11-pricing.md (Revenue model, pricing tiers)
- 12-costs.md (Cost structure, burn rate)
- 13-metrics.md (Key metrics, unit economics)

**Example invocation:**
```
skill: foundation-builder
phase: definition
context: "Completed discovery, ready to define value prop and business model"

Output: 6 additional Canvas sections defining product and economics
```

**Human input required (1-2 hours):**
- Provide product vision and constraints (15 min)
- Review UVP and positioning (30 min)
- Validate pricing assumptions (20 min)
- Approve Canvas sections 07-13 (20 min)

**AI execution time:** 2-3 hours (value prop articulation, pricing design, economics modeling)

**Real-world validation (3-5 days):**
- Pricing validation (customer surveys, competitor analysis)
- Value prop testing (landing page, customer conversations)
- **Bottleneck: Customer feedback on pricing/value**

**Total elapsed:** 3-5 days (mostly validation, minimal human time)

---

## Phase 1a: Validation (Assumption Testing)

**Goal:** Test critical assumptions before building, design experiments

**Agents activated:**
- `validation`: Experiment design, hypothesis testing, validation plans
- `execution`: Task orchestration for running experiments

**Canvas sections updated:**
- 10.assumptions.md (Hypotheses, validation status, confidence levels)

**Example invocation:**
```
skill: foundation-builder
phase: validation
assumptions: "{critical assumptions to test}"

Output: Validated (or invalidated) assumptions with confidence scores
```

**Human input required (2-3 hours):**
- Identify critical assumptions to test (30 min)
- Review experiment designs (30 min)
- Approve experiment execution (15 min)
- Analyze experiment results with AI (60 min)

**AI execution time:** 1-2 hours (experiment design, test materials, results analysis)

**Real-world validation (2-4 weeks):**
- Run landing page tests (1 week minimum for traffic)
- Conduct customer interviews (5-10 interviews, 1-2 weeks)
- Prototype testing with early customers
- **Major bottleneck: Waiting for statistically significant results**

**Total elapsed:** 2-4 weeks (validation is the constraint)

---

## Phase 1b: Execution (MVP Build & Launch Prep)

**Goal:** Build MVP, prepare for launch, activate operations

**Agents activated:**
- `execution`: Development orchestration, sprint planning
- `go-to-market`: Channel strategy, launch planning

**Canvas sections populated:**
- 11.channels.md (Growth channels, acquisition tactics)
- 15.gtm.md (Go-to-market strategy, launch plan)

**Example invocation:**
```
skill: foundation-builder
phase: execution
status: "Assumptions validated, ready to build MVP and plan launch"

Output: GTM strategy and operational readiness
```

**Human input required (1-2 hours):**
- Define MVP scope and priorities (30 min)
- Review GTM strategy (30 min)
- Approve sales/marketing narratives (30 min)

**AI execution time:** 2-4 hours (GTM design, channel planning, narrative generation)

**Real-world validation (4-8 weeks):**
- MVP development (depends on complexity)
- Beta testing with early customers
- **Bottleneck: Building and testing the actual product**

**Total elapsed:** 4-8 weeks (MVP build is the constraint)

---

## Phase 2: Launch (Operational Mode)

**Goal:** Activate sales and marketing operations, maintain Canvas through learning

**Post-launch:** Canvas becomes living documentation
- Sales threads (Stage 6: Learning) update Canvas assumptions
- Marketing content reflects validated Canvas positioning
- Business decisions update Canvas sections continuously

**Validation criteria for launch readiness:**
- ✅ All 15 Canvas sections populated with evidence
- ✅ Critical assumptions validated (confidence ≥75%)
- ✅ ICP defined for at least 1 segment
- ✅ Sales narratives generated
- ✅ Marketing narratives created

**Human input ongoing:** <30 min/day
- Review ops/today.md (5 min)
- Approve content opportunities (2 min)
- Review draft content (10 min, 2-3x/week)
- Strategic decisions only (as needed)

**AI operations:** Continuous autonomous execution
- Sales execution (prospecting, qualification, materials)
- Marketing execution (content creation, SEO, distribution)
- Thread management (6-stage flow for all decisions)
- Canvas updates from validated learning

**Real-world validation:** Continuous
- Sales cycle time (varies by segment)
- Content performance (7-30 day feedback loops)
- **Bottleneck: Customer decision-making and sales cycles**

---

## Specialist Agents (On-Demand)

Use these agents for specific scenarios outside core operations:

### funding agent
- **Trigger:** Preparing to fundraise
- **Output:** `strategy/financials/fundraising.md` (pitch deck outline, investor targets, financial projections)

### regulatory agent
- **Trigger:** Entering regulated markets (healthcare, finance, insurance)
- **Output:** Compliance requirements, licensing roadmap

### retention-optimizer agent
- **Trigger:** Post-launch with cohort data
- **Output:** Churn analysis, retention experiments, optimization strategies

---

## Timeline Summary

**The bottleneck is NOT AI execution - it's human decisions and real-world validation.**

### Absolute Minimum (Aggressive): 3-4 weeks
- Discovery: 1 week (5 customer interviews)
- Definition: 3 days (pricing validation)
- Validation: 1 week (landing page + 5 interviews)
- Execution: 1 week (simple MVP or no-code prototype)

**Human input:** <10 hours total
**AI execution:** <15 hours total
**Real-world validation:** 3-4 weeks

---

### Typical Timeline (Recommended): 6-8 weeks
- Discovery: 2 weeks (10 customer interviews)
- Definition: 1 week (thorough pricing validation)
- Validation: 2-3 weeks (statistically significant tests)
- Execution: 2-3 weeks (functional MVP)

**Human input:** <10 hours total
**AI execution:** <15 hours total
**Real-world validation:** 6-8 weeks

---

### Conservative (Complex Product): 12+ weeks
- Discovery: 3 weeks (extensive market research)
- Definition: 2 weeks (multiple pricing models tested)
- Validation: 4 weeks (multiple experiment iterations)
- Execution: 4+ weeks (complex MVP build)

**Human input:** <15 hours total
**AI execution:** <20 hours total
**Real-world validation:** 12+ weeks

---

## Key Insight

**Human provides <10 hours total input across all phases. AI does analysis in <15 hours. Real-world validation takes weeks.**

**The bottleneck is NOT the AI—it's customer feedback and product development.**

---

## Canvas Structure Reference

### 01.context.md (KBOS Framework)
- **Known:** Verifiable facts (market size, competitors, regulations)
- **Believed:** High-confidence assumptions (needs validation)
- **Objective:** Measurable statements (can be proven true/false)
- **Subjective:** Opinions (acknowledge but don't build on)

### 02.constraints.md
- Budget limits
- Time constraints
- Resource availability
- Regulatory requirements

### 03.opportunity.md
- TAM/SAM/SOM (Total/Serviceable/Obtainable Market)
- Market timing (why now?)
- Key trends enabling opportunity

### 04.segments.md
- Customer segments with observable filters
- Segment size and attractiveness
- Prioritization

### 05.problem.md
- Top 3 problems (ranked by severity)
- Existing alternatives (how customers solve today)
- Why alternatives fail

### 06.competitive.md
- Direct competitors
- Indirect competitors
- Positioning gaps (white space opportunities)
- Alternative ways customers solve the problem

### 07.uvp.md
- Unique Value Proposition (single sentence)
- What makes it unique
- Why it matters to customers

### 08.unfair.md
- Unfair advantages (hard to copy)
- Secret sauce
- Moats (network effects, data, brand, etc.)

### 09.solution.md
- MVP feature set (minimum viable)
- Solution approach
- Technical architecture (high-level)

### 10.assumptions.md
- Critical hypotheses to test
- Validation status (untested, testing, validated, invalidated)
- Confidence levels (0-100%)
- Evidence for each assumption

### 11.channels.md
- Channel strategy
- Distribution approach
- Partner channels

### 12.revenue.md
- Revenue model (subscription, usage, one-time, etc.)
- Pricing tiers
- Unit economics (LTV, CAC, payback period)

### 13-metrics.md
- Key metrics to track (North Star, AARRR, etc.)
- Targets and benchmarks
- Measurement methodology

### 14.costs.md
- Fixed costs
- Variable costs
- Burn rate
- Runway
    
### 15.gtm.md
- Go-to-market strategy
- Launch plan
- Early customer acquisition approach
- Milestones

---

## Next Steps

- Learn architecture: [Architecture Overview](../reference/architecture.md)
- See all skills: [All Skills](../reference/skills-index.md)
- Learn workflows: [Sales](sales-workflow.md) | [Marketing](marketing-workflow.md)