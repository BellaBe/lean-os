# Counterfactual Mode

Evaluate alternatives through "what if" simulation.

## When to Use

- Evaluating a past decision
- Planning future scenarios
- Comparing paths not taken
- Question is "What if we had/do X?"

## Flow

```
Actual World → Intervention → Projection → Comparison
```

---

## Core Principles

### Minimal Intervention

Change only what's necessary:
- Modify one variable at a time
- Keep everything else constant
- Trace downstream effects carefully

Multiple simultaneous changes make attribution impossible.

### Probability Weighting

Alternative outcomes aren't certain:
- Assign probability to each scenario
- Consider multiple alternative outcomes
- Use expected value calculations

### Hindsight Awareness

Guard against these biases:
- **Hindsight bias:** "We should have known" (but did we?)
- **Outcome bias:** Judging decision quality by outcome alone
- **Availability bias:** Overweighting memorable alternatives

Always ask: "What was knowable at decision time?"

---

## Stage 1: Actual World

Document what actually happened.

**Required elements:**
- **Decision:** What was chosen, when, by whom, in what context
- **Alternatives considered:** What options were evaluated at the time
- **Information available:** What was known then (not what we know now)
- **Outcome:** What happened, with metrics
- **Causal chain:** How decision led to outcome

**Challenge:** "Am I using hindsight? What was actually knowable then?"

**Example:**

> **Decision:** Declined $5M Series A at $20M valuation (June 2023)
> 
> **Alternatives considered at the time:**
> - Accept this term sheet
> - Negotiate for better terms
> - Continue bootstrapping (chosen)
> 
> **Information available then:**
> - 12-month runway remaining
> - $50K MRR, growing 15% month-over-month
> - Strong product-market fit signals
> - Uncertain about capital deployment skills
> 
> **Outcome:**
> - Bootstrapped to $600K ARR by Dec 2024
> - 100% ownership retained
> - Now raising at $30M valuation
> 
> **Causal chain:**
> - Declined funding → maintained capital discipline
> - Discipline → focused product, conservative hiring
> - Focus → achieved profitability at $400K ARR
> - Profitability → negotiating from strength

**Gate:** Must document what was knowable at decision time.

---

## Stage 2: Intervention

Define the alternative being evaluated.

**Required elements:**
- **What:** The alternative choice
- **Variable changed:** Single change from actual
- **Validity:** Was this actually available? Was it controllable?
- **Assumptions:** What stays the same, what ripples

**Validity requirements:**
- Intervention was actually available then
- Change was controllable (not external events)
- Effects are traceable

**Challenge:** "Was this actually an option? Could we have controlled it?"

**Example:**

> **Intervention:** Accept $5M Series A at $20M valuation
> 
> **Variable changed:** Funding decision only
> 
> **Validity:**
> - Was available: Yes, term sheet was on the table
> - Was controllable: Yes, our decision to sign
> - Traceable: Yes, can model capital deployment
> 
> **Assumptions:**
> - Market conditions same
> - Team same
> - Product roadmap same
> - Capital deployed "reasonably well" (uncertainty here)

**Gate:** Intervention must have been actually available and controllable.

---

## Stage 3: Projection

Model alternative outcomes with probability weights.

**Required scenarios:**

| Scenario | Probability | Description |
|----------|-------------|-------------|
| Expected | 55-60% | Most likely outcome |
| Optimistic | 20-25% | Things go well |
| Pessimistic | 15-20% | Things go poorly |

Probabilities must sum to 100%.

**For each scenario, specify:**
- Key metrics
- Reasoning for this outcome
- What would cause this scenario

**Challenge:** "Am I being overconfident? What could go wrong that I'm not modeling?"

**Example:**

> **Alternative: Took Series A**
> 
> **Expected (55%):**
> - ARR: $1.5M (capital enables faster hiring, more experiments)
> - Ownership: 75% (after 25% dilution)
> - Valuation: $45M (30x ARR)
> - Equity value: $33.75M
> - Reasoning: Moderate success with capital deployment
> 
> **Optimistic (25%):**
> - ARR: $2.2M (hired great, executed well)
> - Valuation: $66M (30x)
> - Equity value: $49.5M
> - Reasoning: Top-quartile execution
> 
> **Pessimistic (20%):**
> - ARR: $800K (burned capital on wrong bets)
> - Valuation: $24M
> - Equity value: $18M
> - Reasoning: Premature scaling, wrong hires
> 
> **Weighted expected equity value:**
> - (0.55 × $33.75M) + (0.25 × $49.5M) + (0.20 × $18M) = $34.5M
> 
> **Key uncertainty:** Capital deployment skill—no track record, hard to predict.

**Gate:** All three scenarios required with probabilities summing to 100%.

---

## Stage 4: Comparison

Analyze delta between actual and alternative.

**Quantitative comparison:**

| Metric | Actual | Alternative (weighted) | Delta |
|--------|--------|------------------------|-------|
| [Metric 1] | [Value] | [Value] | [+/- %] |
| [Metric 2] | [Value] | [Value] | [+/- %] |

**Verdict framework:**

| Condition | Verdict |
|-----------|---------|
| Alternative >20% better, high confidence | Alternative would have been better |
| Alternative 5-20% better, high confidence | Alternative marginally better |
| Within 5% or low confidence | Decision was reasonable |
| Alternative worse | Original decision was correct |
| High uncertainty | Inconclusive—can't determine |

**Required elements:**
- Quantitative comparison on key metrics
- Verdict with confidence level
- Insight: What does this teach us?
- Application: When does this lesson apply?

**Example:**

> **Comparison:**
> 
> | Metric | Actual | Alternative | Delta |
> |--------|--------|-------------|-------|
> | ARR | $600K | $1.4M (weighted) | -$800K |
> | Ownership | 100% | 75% | +25pp |
> | Equity value | $30M | $34.5M | -$4.5M (-15%) |
> 
> **Verdict:** Decision was reasonable
> 
> **Confidence:** 55%
> 
> **Rationale:**
> - Alternative equity value 15% higher, but within uncertainty bounds
> - Confidence is moderate due to unknown capital deployment skill
> - Given risk preferences and uncertainty, original decision defensible
> 
> **Insight:** Bootstrapping is viable when capital discipline is maintained and path to profitability exists.
> 
> **Applies to:** Early-stage with revenue, founders uncertain about scaling skills.
> 
> **Does not apply to:** Winner-take-all markets, network effects, clear capital deployment opportunity.

**Gate:** Verdict must include confidence level and be justified by the analysis.

---

## Common Counterfactual Questions

| Question Type | Example | Key Challenge |
|---------------|---------|---------------|
| Past decision | "Should we have raised?" | Avoid hindsight bias |
| Missed opportunity | "What if we'd hired X?" | Was X actually available? |
| Alternative strategy | "What if we'd gone enterprise?" | Model the full causal chain |
| Timing | "What if we'd launched earlier?" | What was actually ready? |
| Resource allocation | "What if we'd spent on Y?" | Zero-sum: what didn't we do? |

---

## Output Format

```markdown
## Counterfactual Analysis: [Decision]

### Actual World
**Decision:** [What was chosen]
**Context:** [Information available at the time]
**Outcome:** [What happened]

### Intervention
**Alternative:** [What we're evaluating]
**Validity:** [Was this actually available?]

### Projection

| Scenario | Probability | Outcome |
|----------|-------------|---------|
| Expected | [%] | [Metrics] |
| Optimistic | [%] | [Metrics] |
| Pessimistic | [%] | [Metrics] |

**Weighted outcome:** [Expected value calculation]

### Comparison

| Metric | Actual | Alternative | Delta |
|--------|--------|-------------|-------|
| [Key metric] | [Value] | [Weighted value] | [%] |

**Verdict:** [Assessment] (Confidence: [%])

**Insight:** [What this teaches]
**Applies to:** [When to use this lesson]
```

---

## Output Format

```markdown
## Counterfactual Analysis: [Decision]

### Actual World

**Decision:** [What was chosen]
**When:** [Date]
**Context:** [Information available at the time]

**Alternatives considered then:**
- [Option A]
- [Option B]

**Outcome:**
- [Metric 1]: [Result]
- [Metric 2]: [Result]

**Causal chain:** [How decision led to outcome]

### Intervention

**Alternative evaluated:** [What we're modeling]
**Variable changed:** [Single change from actual]

**Validity:**
- Was available: [Yes/No — evidence]
- Was controllable: [Yes/No — evidence]

### Projection

| Scenario | Probability | Key Metrics |
|----------|-------------|-------------|
| Expected | [55-60%] | [Outcome] |
| Optimistic | [20-25%] | [Outcome] |
| Pessimistic | [15-20%] | [Outcome] |

**Weighted expected outcome:** [Calculation]

**Key assumptions:** [What we're assuming holds constant]

### Comparison

| Metric | Actual | Alternative | Delta |
|--------|--------|-------------|-------|
| [Key metric] | [Value] | [Weighted value] | [+/- %] |

### Verdict

**[Assessment]** (Confidence: [%])

[Explanation of verdict in 2-3 sentences]

### Insight

**Learning:** [What this analysis teaches us]
**Applies to:** [Future situations where this lesson is relevant]
**Does not apply to:** [Situations where conditions differ]
```

---

## Quality Gates

| Stage | Gate |
|-------|------|
| Actual | What was knowable documented |
| Intervention | Was actually available and controllable |
| Projection | Three scenarios with probabilities summing to 100% |
| Comparison | Verdict with confidence level |

## Anti-Patterns

| Avoid | Do Instead |
|-------|------------|
| Hindsight bias | Document what was knowable then |
| Single scenario | Require three probability-weighted scenarios |
| "Obviously better" | Quantify with confidence bounds |
| Uncontrollable intervention | Verify it was our choice to make |
| Overconfident projection | State uncertainty explicitly |
| Outcome = decision quality | Separate decision quality from outcome |
