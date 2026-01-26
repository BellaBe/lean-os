# Counterfactual Mode Reference

Evaluate alternatives through "what if" simulation.

## When to Use

Use counterfactual mode when:
- Evaluating a past decision
- Planning future scenarios
- Comparing paths not taken
- The question is "What if we had/do X?"

## Required Personas

| Persona | Role | Traits |
|---------|------|--------|
| **Executor** | Represents actual world | E:2, A:4, C:5, N:2, O:3 |
| **Explorer** | Models alternative world | E:4, A:3, C:5, N:3, O:5 |

## Execution Flow

```
Stage 1: Actual World (document what happened)
    ↓
Stage 2: Intervention (define the change)
    ↓
Stage 3: Projection (model alternatives)
    ↓
Stage 4: Comparison (analyze delta)
```

## Core Principles

### Minimal Intervention

Change only what's necessary:
- Modify one variable at a time
- Keep everything else constant
- Trace downstream effects carefully

### Probability Weighting

Alternative outcomes aren't certain:
- Assign probability to each scenario
- Consider multiple alternatives
- Use expected value calculations

### Hindsight Awareness

Guard against biases:
- Document what was knowable at decision time
- Don't assume perfect information
- State confidence bounds

## Stage Instructions

### Stage 1: Actual World

**Executor documents:**
1. The decision made and context
2. Alternatives considered at the time
3. Information available then (not now)
4. Observed outcome with metrics
5. Causal chain from decision to outcome

**Output:**
```yaml
actual:
  decision:
    what: "[Choice made]"
    when: "[Timestamp]"
    who: "[Decision maker]"
    context: "[Circumstances]"
    alternatives_considered: ["[Options evaluated then]"]
    information_available: ["[What was known]"]
    
  outcome:
    result: "[What happened]"
    metrics:
      - metric: "[Measure]"
        value: number
        expected: number
    timeline: "[Time to outcome]"
    
  causal_chain:
    - "[Decision led to X]"
    - "[X led to Y]"
    - "[Y produced outcome]"
    
  assessment:
    success_level: high | medium | low | failed
    surprise: 0.0-1.0
```

**Format:**
```xml
<think_executor>
  Actual world:
  
  Decision: Declined $5M Series A at $20M valuation (June 2023)
  
  Alternatives considered at the time:
  - Accept this term sheet
  - Negotiate for better terms
  - Continue bootstrapping (chosen)
  
  Information available:
  - 12-month runway remaining
  - $50K MRR
  - Strong growth trajectory
  
  Outcome: Bootstrapped to $600K ARR, now raising at $30M
  
  Causal chain:
  - Declined funding → maintained capital discipline
  - Discipline → focused product, slower hiring
  - Focus → profitability at $400K ARR
  - Profitability → raising from position of strength
</think_executor>
```

**Gate:** Must document what was knowable at decision time.

---

### Stage 2: Intervention

**Explorer defines the alternative:**

**Validity Requirements:**
- Intervention was actually available then
- Change is controllable (not external events)
- Effects are traceable

**Output:**
```yaml
intervention:
  what: "[Alternative choice]"
  
  change:
    variable: "[What's changed]"
    from: "[Actual value]"
    to: "[Alternative value]"
    
  validity:
    was_available: bool
    was_controllable: bool
    rationale: "[Why valid to consider]"
    
  assumptions:
    held_constant: ["[What stays same]"]
    ripple_effects: ["[Expected changes]"]
```

**Executor challenges validity:**
- "Wait, was that actually an option?"
- "Could we have controlled that?"
- "What information would we have needed?"

**Example:**
```xml
<think_explorer>
  Intervention: Accept $5M Series A at $20M valuation
  
  Change: Funding decision
  From: Bootstrapped
  To: $5M raised, 25% dilution
  
  Was available: Yes, term sheet was on table
  Was controllable: Yes, our decision
</think_explorer>

<think_executor>
  Wait, let me validate this intervention.
  
  Was this actually available? Yes, we had the term sheet.
  Could we have controlled it? Yes, signing was our choice.
  
  Valid intervention. But note: we'd need to model capital deployment,
  which has uncertainty.
</think_executor>
```

**Gate:** Intervention must have been actually available.

---

### Stage 3: Projection

**Explorer models alternative outcomes:**

**Required Scenarios:**

| Scenario | Probability | Description |
|----------|-------------|-------------|
| Expected | 60% | Most likely outcome |
| Optimistic | 25% | Things go well |
| Pessimistic | 15% | Things go poorly |

**Executor reality-checks each projection:**
- "Wait, that assumes we'd deploy capital well"
- "What about the risk of [X]?"
- "Is that growth rate realistic?"

**Output:**
```yaml
alternative:
  scenarios:
    - name: "Expected"
      probability: 0.60
      outcome:
        metric_1: value
        metric_2: value
      reasoning: "[Why expected]"
      
    - name: "Optimistic"
      probability: 0.25
      outcome:
        metric_1: value
        metric_2: value
      reasoning: "[Why possible]"
      
    - name: "Pessimistic"
      probability: 0.15
      outcome:
        metric_1: value
        metric_2: value
      reasoning: "[Why possible]"
      
  weighted_outcome:
    metric_1: "[Expected value]"
    metric_2: "[Expected value]"
    
  causal_reasoning:
    - "[Step 1 in modified chain]"
    - "[Step 2 in modified chain]"
    
  confidence: 0.0-1.0
  key_uncertainties: ["[What we don't know]"]
```

**Example:**
```xml
<think_explorer>
  Projecting alternative (took Series A):
  
  Expected (60%):
  - ARR: $1.5M (capital enables faster hiring)
  - Ownership: 75% (after 25% dilution)
  - Valuation: $45M (30x ARR)
  - Equity value: $33.75M
  
  Optimistic (25%):
  - ARR: $2M
  - Valuation: $60M
  - Equity value: $45M
  
  Pessimistic (15%):
  - ARR: $800K (burned capital on wrong bets)
  - Valuation: $24M
  - Equity value: $18M
</think_explorer>

<think_executor>
  Wait, the expected case assumes good capital deployment.
  What's our track record on that? Unknown.
  
  Also, would we have hired well? Hiring is hard.
  
  I'd widen the pessimistic scenario or increase its probability.
</think_executor>

<think_explorer>
  Good challenges. Adjusting:
  
  Pessimistic probability: 15% → 20%
  Expected probability: 60% → 55%
  
  Weighted equity value: $33.5M → $32M
  Confidence: 0.55 (moderate—many unknowns)
</think_explorer>
```

**Gate:** All three scenarios required with probabilities summing to 1.0.

---

### Stage 4: Comparison

**Both personas compare actual vs alternative:**

**Quantitative comparison:**
```yaml
comparison:
  quantitative:
    - metric: "[Name]"
      actual: value
      alternative: value
      difference: "[+/- amount]"
      direction: better | worse | neutral
```

**Verdict Framework:**

| Condition | Verdict |
|-----------|---------|
| Alternative >20% better, high confidence | "Alternative would have been better" |
| Alternative <20% better, high confidence | "Alternative marginally better" |
| Within margin of error | "Decision was reasonable" |
| Alternative worse | "Original decision was correct" |
| High uncertainty | "Inconclusive" |

**Output:**
```yaml
comparison:
  quantitative:
    - metric: "ARR"
      actual: 600000
      alternative: 1400000
      difference: "+$800K (+133%)"
      direction: worse_actual
      
    - metric: "Ownership"
      actual: 100%
      alternative: 75%
      difference: "-25pp"
      direction: worse_alternative
      
    - metric: "Equity value"
      actual: 30000000
      alternative: 32000000
      difference: "+$2M (+7%)"
      direction: worse_actual
      
  verdict:
    assessment: "[Decision was reasonable | Alternative better | etc.]"
    confidence: 0.0-1.0
    rationale: "[Why this verdict]"
    
  insight:
    learning: "[What this teaches]"
    applies_to: "[Future situations]"
    recommendation: "[What to do differently]"
```

**Example:**
```xml
<synthesis>
  Comparison:
  
  | Metric | Actual | Alternative | Delta |
  |--------|--------|-------------|-------|
  | ARR | $600K | $1.4M | -$800K |
  | Ownership | 100% | 75% | +25pp |
  | Equity value | $30M | $32M | -$2M |
  
  Verdict: Decision was reasonable
  
  Rationale: Alternative equity value only 7% higher ($2M),
  well within uncertainty bounds (confidence 0.55).
  Given risk preferences and unknowns, original decision defensible.
  
  Insight: Bootstrapping viable when capital discipline maintained.
  Applies to: Early-stage with path to profitability.
  
  Recommendation: Accept funding only when clear use of capital identified.
</synthesis>
```

**Gate:** Verdict must include confidence and be justified.

## Complete Example

```xml
<personas>
  <executor traits="E:2,A:4,C:5,N:2,O:3">
    Represents what actually happened
  </executor>
  <explorer traits="E:4,A:3,C:5,N:3,O:5">
    Models the alternative reality
  </explorer>
</personas>

<think_executor>
  Stage 1 - Actual:
  Decision: Declined Series A (June 2023)
  Outcome: $600K ARR, 100% ownership, $30M valuation
</think_executor>

<think_explorer>
  Stage 2 - Intervention:
  What if we took the $5M at $20M valuation?
  Valid: Yes, term sheet was available.
</think_explorer>

<think_executor>
  Wait, validating... Yes, we had the option.
  But capital deployment has uncertainty.
</think_executor>

<think_explorer>
  Stage 3 - Projection:
  Expected (55%): $1.5M ARR, 75% ownership, $33.75M equity
  Optimistic (25%): $2M ARR, $45M equity
  Pessimistic (20%): $800K ARR, $18M equity
  
  Weighted equity value: $32M
</think_explorer>

<think_executor>
  Those projections assume good hiring and deployment.
  What's our evidence for that? Limited.
  
  Confidence: 0.55 is right.
</think_executor>

<synthesis>
  Stage 4 - Comparison:
  
  Actual equity: $30M
  Alternative equity: $32M (weighted)
  Difference: +7%
  
  Verdict: Decision was reasonable
  Confidence: 0.55
  
  Within uncertainty bounds. Risk preferences matter.
  Original decision defensible.
  
  Learning: Bootstrap works with discipline.
  Future: Take funding when clear use identified.
</synthesis>
```

## Quality Gates Summary

| Stage | Gate |
|-------|------|
| Actual | What was knowable documented |
| Intervention | Was actually available |
| Projection | Three scenarios with probabilities |
| Comparison | Verdict with confidence |

## Anti-Patterns

| Avoid | Do Instead |
|-------|------------|
| Hindsight bias | Document what was knowable |
| Single scenario | Require three weighted scenarios |
| "Obviously better" | Quantify with confidence bounds |
| Uncontrollable intervention | Verify it was our choice |
| Overconfident projection | State uncertainty explicitly |
