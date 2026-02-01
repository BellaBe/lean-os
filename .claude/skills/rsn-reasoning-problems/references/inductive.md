# Inductive Mode

Extract patterns and rules from multiple observations.

## When to Use

- Multiple instances suggest a pattern
- Something keeps happening repeatedly
- Need to generalize from examples
- Question is "What pattern exists?"

## Flow

```
Collection (≥5 instances) → Pattern Detection → Generalization → Confidence Bounds
```

---

## Stage 1: Collection

Gather instances with consistent metadata before looking for patterns.

**Minimum sample requirements:**

| Confidence Target | Minimum N |
|-------------------|-----------|
| Exploratory | 3-5 |
| Tentative | 6-10 |
| Moderate | 11-20 |
| High | 21+ |

**Required for each instance:**
- Unique identifier
- Timestamp
- Category/context
- Key attributes
- Outcome

**Data quality checks:**
- **Completeness:** What percentage of fields are filled?
- **Consistency:** Are categories and values standardized?
- **Recency:** How current is the data?

**Challenge:** "Are these instances comparable? Is there selection bias? What's missing?"

**Example:**

> **Collection:** 24 content pieces, Jul-Dec 2024
> 
> | ID | Type | Word Count | Channel | Conversions |
> |----|------|------------|---------|-------------|
> | C01 | Case study | 1,850 | Organic | 47 |
> | C02 | How-to | 2,200 | Organic | 32 |
> | C03 | Case study | 1,600 | LinkedIn | 28 |
> | ... | ... | ... | ... | ... |
> 
> **Quality:** Completeness 88%, Consistency 92%, Recency 95%

**Gate:** Must have ≥5 comparable instances before proceeding.

---

## Stage 2: Pattern Detection

Identify patterns in the data.

### Standard Pattern Types

| Type | What to Look For | Example |
|------|------------------|---------|
| **Frequency** | How often X occurs | "7/12 deals stall at legal review" |
| **Correlation** | X and Y appear together | "Large deals AND long cycles" |
| **Sequence** | X followed by Y | "Demo → proposal within 3 days = higher close" |
| **Cluster** | Natural groupings | "Two distinct customer segments exist" |
| **Trend** | Direction over time | "Average deal size increasing 5%/quarter" |
| **Threshold** | Behavior changes at breakpoint | "Deals >$100K require VP approval" |

### System Architecture Patterns

For AI/software systems, also check:

| Type | What to Look For | Example |
|------|------------------|---------|
| **Layer Coupling** | Failures cascade through layers | "Retrieval errors → reasoning failures" |
| **Feedback Loop** | Output affects future input | "User corrections → behavior drift" |
| **Bottleneck** | Single point constrains system | "All failures trace to validation layer" |
| **Redundancy Gap** | No backup for critical path | "Single model, no fallback" |
| **Drift Signature** | Gradual distribution shift | "Query types changing over 6 months" |

**Challenge:** "Is this correlation or causation? What about the exception that breaks this?"

**Scoring:**
- Strong pattern: ≥80% of instances follow
- Moderate pattern: 60-79% follow
- Weak pattern: <60% follow (needs more data or is unreliable)

**Example:**

> **Patterns detected:**
> 
> **P1 (Frequency):** Case studies convert at 2.3x average rate.
> - 7/8 case studies above average (87.5%)
> - Strength: Strong (0.82)
> 
> **P2 (Correlation):** Technical depth correlates with enterprise demos (r=0.68)
> - Strength: Moderate
> - Note: Correlation, not proven causation
> 
> **P3 (Threshold):** Posts >2,000 words perform 2.1x better on organic
> - Clear step function at 2,000 word mark
> - Strength: Strong (0.75)
> 
> **P4 (Trend):** LinkedIn engagement declining month-over-month
> - Strength: Moderate (0.70)

**Gate:** At least one pattern must have strength ≥0.6 before proceeding.

---

## Stage 3: Generalization

Form rules from validated patterns.

### Rule Types

| Type | Form | Example |
|------|------|---------|
| **Deterministic** | If X, always Y | "Deals >$500K always require legal" |
| **Probabilistic** | If X, Y with P% | "Stalls >21 days → 80% loss rate" |
| **Conditional** | If X and Y, then Z | "Large + new customer → CFO approval" |
| **Threshold** | When X > N, then Y | "Word count >2,000 → 2x organic traffic" |

**Required for each rule:**
- **Statement:** Clear if-then formulation
- **Derived from:** Which patterns support it
- **Mechanism:** Why the rule works (hypothesis)
- **Applicability:** Where rule applies
- **Exceptions:** Known cases where rule doesn't hold

**Challenge:** "What's the boundary condition? Does this hold for [segment]? What are the exceptions?"

**Example:**

> **R1:** Case studies convert at 2x+ rate vs other content types.
> - Derived from: P1
> - Mechanism: Social proof + specificity reduce purchase anxiety
> - Applies to: Bottom-funnel, decision-stage content
> - Exception: Narrow technical audiences (1/8 case studies underperformed)
> 
> **R2:** Target >2,000 words for SEO content.
> - Derived from: P3
> - Mechanism: Longer content ranks better, earns more backlinks
> - Applies to: Organic-focused content
> - Exception: News/announcement posts (brevity expected)
> 
> **R3 (Tentative):** Technical depth attracts enterprise buyers.
> - Derived from: P2
> - Mechanism: Signals expertise → builds trust
> - Status: Correlation only—needs A/B test to confirm causation

**Gate:** Rules must have explicit applicability bounds and exceptions.

---

## Stage 4: Confidence Bounds

Calculate reliability of rules.

**Confidence formula:**

```
Confidence = Base(N) × min(Strength, Consistency, Recency)
```

**Base from sample size:**
- N < 5: max 0.40
- N 5-10: max 0.60
- N 11-20: max 0.80
- N > 20: max 0.95

**Exception rate:**
- <10% exceptions: Rule is robust
- 10-20% exceptions: Rule has caveats
- 20-30% exceptions: Rule is situational
- >30% exceptions: Rule is unreliable—don't generalize

**Challenge:** "Is the sample large enough? Are we overconfident?"

**Example:**

> **R1 confidence calculation:**
> - Base (N=8): 0.60
> - Strength: 0.82
> - Consistency: 0.87
> - Recency: 0.95
> - Final: 0.60 × 0.82 = **0.49**
> 
> **Interpretation:** Moderate confidence. Directionally useful but revisit when N≥15.
> 
> **Validity period:** Re-evaluate in 90 days or when N doubles.

---

## Output Format

```markdown
## Inductive Analysis: [Topic]

### Collection
- **Sample:** [N] instances, [date range]
- **Quality:** Completeness [%], Consistency [%]

### Patterns Detected

**P1: [Name]** (Strength: [X])
[Description with evidence]

**P2: [Name]** (Strength: [X])
[Description with evidence]

### Rules

**R1:** [If-then statement]
- Confidence: [%]
- Applies to: [Context]
- Exceptions: [Known exceptions]

### Uncertainty
- Sample size limitation: [What we'd see with more data]
- Exceptions unexplained: [Anomalies]
- Correlation vs causation: [What needs testing]

### Next Steps
1. [Action to validate or apply]
2. [Experiment to test mechanism]
```

---

## Output Format

### Pattern Analysis

```markdown
## Pattern Analysis: [Topic]

### Collection
**Sample:** [N] instances, [date range]
**Source:** [Where data came from]
**Quality:** Completeness [%], Consistency [%]

### Patterns Detected

**P1: [Pattern Name]** (Strength: [0.0-1.0])
[Description with quantified evidence]

**P2: [Pattern Name]** (Strength: [0.0-1.0])
[Description with quantified evidence]

### Rules Derived

**R1:** [If-then statement]
- Confidence: [%]
- Applies to: [Context where rule holds]
- Exceptions: [Known cases where rule doesn't hold]
- Mechanism: [Why the rule works]

**R2:** [If-then statement]
- Confidence: [%]
- Applies to: [Context]
- Exceptions: [Known exceptions]

### Uncertainty
- **Sample size:** [Limitation and what more data would show]
- **Unexplained exceptions:** [Anomalies not yet understood]
- **Correlation vs causation:** [What needs testing]

### Next Steps
1. [Action to validate or apply]
2. [Experiment to test mechanism]
```

### Assessment Output (for quality evaluation)

When evaluating against criteria:

```markdown
## Assessment: [Target]

**Evaluator:** [Who]
**Date:** [When]

### Criteria

| Criterion | Weight | Pass Threshold |
|-----------|--------|----------------|
| [Name] | [0.0-1.0] | [What constitutes pass] |

### Findings

**[Criterion 1]:** [Pass/Partial/Fail]
- Score: [0.0-1.0]
- Evidence: [Specific observation]
- Gap: [If any, what's missing]

**[Criterion 2]:** [Pass/Partial/Fail]
- Score: [0.0-1.0]
- Evidence: [Specific observation]

### Overall

**Verdict:** [Pass / Conditional / Fail]
**Weighted Score:** [0.0-1.0]
**Confidence:** [0.0-1.0]

### Gaps

| Gap | Severity | Current | Required |
|-----|----------|---------|----------|
| [What's missing] | Blocking/Significant/Minor | [State] | [Target] |

*Note: Assessment describes quality. For recommendations, chain to recommendation output.*
```

---

## Quality Gates

| Stage | Gate |
|-------|------|
| Collection | ≥5 comparable instances |
| Detection | ≥1 pattern with strength ≥0.6 |
| Generalization | Explicit applicability bounds |
| Confidence | Exception rate <30% for actionable rules |

## Anti-Patterns

| Avoid | Do Instead |
|-------|------------|
| Small N conclusions | Wait for sufficient data |
| Correlation = causation | Test mechanism separately |
| Ignoring exceptions | Document and explain each |
| Unbounded rules | Specify where rule applies |
| Overconfident generalization | State confidence with bounds |
| Pattern hunting | Decide what to measure before looking |
