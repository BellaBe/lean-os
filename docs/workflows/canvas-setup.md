# Canvas Setup

The Lean Canvas (15 living documents in `strategy/canvas/`) is your **single source of truth**. Everything in LeanOS flows from the Canvas.

## Why Canvas?

**Canvas is evidence-based, not aspirational.** Every section should be validated through research, customer conversations, or experimentation.

Without Canvas:
- No foundation for market analysis
- No basis for problem-solution fit
- No assumptions to test
- No single source of truth

## Canvas Structure

**Location:** `strategy/canvas/`

### Core Sections (15 documents)

| # | File | Purpose |
|---|------|---------|
| 00 | `00.mode.md` | Business model mode (VENTURE/BOOTSTRAP) |
| 01 | `01.context.md` | Known facts, beliefs, objectives |
| 02 | `02.constraints.md` | Budget, time, resource limits |
| 03 | `03.opportunity.md` | TAM/SAM/SOM, market timing |
| 04 | `04.segments.md` | Customer segments |
| 05 | `05.problem.md` | Top 3 problems, existing alternatives |
| 06 | `06.competitive.md` | Competitors, positioning gaps |
| 07 | `07.uvp.md` | Unique value proposition |
| 08 | `08.unfair.md` | Unfair advantages, moats |
| 09 | `09.solution.md` | MVP feature set |
| 10 | `10.assumptions.md` | Hypotheses to test |
| 11 | `11.channels.md` | Distribution channels |
| 12 | `12.revenue.md` | Revenue model, pricing |
| 13 | `13.metrics.md` | Key metrics, unit economics |
| 14 | `14.costs.md` | Cost structure, burn rate |
| 15 | `15.gtm.md` | Go-to-market strategy |

---

## Getting Started with Core Skills

LeanOS Core includes two foundation skills to help populate your Canvas:

### foundations-market-intelligence

**Purpose:** Analyze market opportunity

**Use for Canvas sections:** 03 (Opportunity), 04 (Segments), 06 (Competitive)

**Outputs:**
- TAM/SAM/SOM estimates
- Competitive landscape
- Segment profiles
- Market trends

### foundations-problem-solution-fit

**Purpose:** Validate problem-solution fit

**Use for Canvas sections:** 05 (Problem), 09 (Solution), 10 (Assumptions)

**Outputs:**
- Problem evidence
- Solution hypothesis
- Validation status

---

## Business Model Mode

**Step 1:** Create `strategy/canvas/00.mode.md`

**Choose VENTURE if:**
- Raising or have raised funding
- Market requires scale to win
- Building platform/network effects
- Okay with burn for growth

**Choose BOOTSTRAP if:**
- Self-funded, need profitability fast
- Can win without scale
- Must be profitable from start

**Choose HYBRID if:**
- Want to prove PMF before raising
- Bootstrap validates, venture scales

---

## Canvas Population Process

### Phase 1: Context (Manual)

Populate these sections manually:
- `00.mode.md` - Your business model mode
- `01.context.md` - Known facts about your market
- `02.constraints.md` - Your limitations

### Phase 2: Market Analysis (AI-Assisted)

Use `foundations-market-intelligence` skill:
- `03.opportunity.md` - Market size
- `04.segments.md` - Customer segments
- `06.competitive.md` - Competitive landscape

### Phase 3: Problem-Solution (AI-Assisted)

Use `foundations-problem-solution-fit` skill:
- `05.problem.md` - Customer problems
- `09.solution.md` - Your solution
- `10.assumptions.md` - What to validate

### Phase 4: Business Model (Manual)

Populate these based on your strategy:
- `07.uvp.md` - Your unique value
- `08.unfair.md` - Your advantages
- `11.channels.md` - How you reach customers
- `12.revenue.md` - How you make money
- `13.metrics.md` - What you measure
- `14.costs.md` - What you spend
- `15.gtm.md` - How you launch

---

## Canvas Section Details

### 00.mode.md
```markdown
# Business Model Mode

**Mode:** BOOTSTRAP | VENTURE | HYBRID

**Rationale:**
{Why this mode}

**Decision criteria:**
- Primary metrics: {what you optimize for}
- Risk tolerance: {low/medium/high}
- Timeline: {exit expectations}
```

### 01.context.md (KBOS Framework)
- **Known:** Verifiable facts
- **Believed:** High-confidence assumptions
- **Objective:** Measurable statements
- **Subjective:** Opinions (acknowledge but don't build on)

### 10.assumptions.md
```markdown
# Assumptions

| ID | Assumption | Status | Confidence | Evidence |
|----|------------|--------|------------|----------|
| A1 | {statement} | untested/validated/invalidated | 0-100% | {source} |
```

**Status values:**
- `untested` - Not yet tested
- `testing` - Currently being validated
- `validated` - Confirmed with evidence
- `invalidated` - Disproven

---

## Integration with Goals

Goals read Canvas for context:
- `goal-setter` reads Canvas when creating goals
- Goals link to assumptions to validate
- Thread learning updates Canvas

```
Goal created
  └── Reads Canvas for context
        └── Thread executes
              └── Stage 6 Learning
                    └── Updates Canvas assumptions
```

---

## Next Steps

- Learn architecture: [Architecture Overview](../reference/architecture.md)
- See all skills: [All Skills](../reference/skills-index.md)
- Learn goal-driven operation: [Daily Routine](daily-routine.md)

---

## LeanOS Pro

Need guided Canvas building? **LeanOS Pro** includes:
- `foundations-builder` agent - Orchestrated Canvas population
- 10 foundation skills for complete Canvas building
- Value proposition, business model, and GTM skills
- Validation and experiment design skills

[Learn more about LeanOS Pro](https://bellabe.gumroad.com/l/leanos-pro)
