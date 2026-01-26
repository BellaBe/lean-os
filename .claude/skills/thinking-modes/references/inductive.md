# Inductive Mode Reference

Extract patterns and rules from multiple observations.

## When to Use

Use inductive mode when:
- Multiple instances suggest a pattern
- Something keeps happening repeatedly
- Need to generalize from examples
- The question is "What pattern exists?"

## Required Personas

| Persona | Role | Traits |
|---------|------|--------|
| **Explorer** | Finds patterns | E:4, A:3, C:5, N:3, O:5 |
| **Validator** | Stress-tests generalizations | E:2, A:3, C:5, N:5, O:3 |

## Execution Flow

```
Stage 1: Collection (≥5 instances)
    ↓
Stage 2: Pattern Detection
    ↓
Stage 3: Generalization
    ↓
Stage 4: Confidence Bounds
```

## Stage Instructions

### Stage 1: Collection

**Explorer gathers instances:**
1. Collect ≥5 instances with consistent metadata
2. Document source and collection method
3. Assess data quality

**Validator checks:**
- "Wait, are these instances comparable?"
- "Is there selection bias?"
- "What's missing from this sample?"

**Minimum Sample Requirements:**

| Confidence Target | Minimum N |
|-------------------|-----------|
| Exploratory | 3-5 |
| Tentative | 6-10 |
| Moderate | 11-20 |
| High | 21+ |

**Output:**
```yaml
observations:
  instances:
    - id: "[unique-id]"
      timestamp: "[ISO8601]"
      context: "[Category]"
      attributes:
        attr_1: value
        attr_2: value
        outcome: value
        
  metadata:
    total: int
    time_range: "[Start - End]"
    source: "[Where data came from]"
    collection_method: "[How gathered]"
    
  quality:
    completeness: 0.0-1.0
    consistency: 0.0-1.0
    recency: 0.0-1.0
```

**Gate:** Must have ≥5 instances before proceeding.

---

### Stage 2: Pattern Detection

**Explorer identifies patterns:**

| Pattern Type | Detection Method | Example |
|--------------|------------------|---------|
| Frequency | Count / Total | "7/12 deals stall at legal" |
| Correlation | Co-occurrence | "Large deals AND long cycles" |
| Sequence | A then B | "Stall → lose within 30 days" |
| Cluster | Natural groupings | "Two deal archetypes exist" |
| Trend | Direction over time | "Cycles getting longer" |
| Threshold | Behavior change at breakpoint | "Deals >$300K behave differently" |

**Validator challenges each pattern:**
- "Wait, is this correlation or causation?"
- "What about [exception]? Does pattern hold?"
- "Is sample size sufficient for this claim?"

**Output:**
```yaml
patterns:
  detected:
    - id: P1
      type: frequency | correlation | sequence | cluster | trend | threshold
      description: "[Human-readable pattern]"
      evidence: "[Quantified support]"
      strength: 0.0-1.0  # 0.8+ strong, 0.6-0.8 moderate, <0.6 weak
      
  rejected:
    - pattern: "[Considered but rejected]"
      reason: "[Why evidence doesn't support]"
      
  insufficient_data:
    - pattern: "[Possible but unconfirmed]"
      needed: "[What data would confirm]"
```

**Example conversation:**
```xml
<think_explorer>
  I see a pattern: Case studies convert at 2.3x average rate.
  8 of 24 content pieces are case studies, all above average.
  Pattern strength: 0.82
</think_explorer>

<think_validator>
  Wait, what about the API documentation case study?
  Let me check... it underperformed.
  That's 1 exception out of 8. Does pattern still hold?
</think_validator>

<think_explorer>
  Good catch. 7/8 = 87.5% follow pattern.
  Exception: API doc case study was too technical, narrow audience.
  Pattern holds with noted exception.
</think_explorer>

<think_validator>
  Hmm, that suggests a refinement: case studies convert well
  EXCEPT when targeting very narrow technical audiences.
  Let me check other technical content...
</think_validator>
```

**Gate:** At least one pattern must have strength ≥0.6.

---

### Stage 3: Generalization

**Explorer forms rules from validated patterns:**

**Rule Types:**

| Type | Form | Example |
|------|------|---------|
| Deterministic | If X, then always Y | "Deals >$500K always require legal" |
| Probabilistic | If X, then Y with P% | "Stalls >21 days → 80% loss" |
| Conditional | If X and Y, then Z | "Large + new customer → CFO approval" |
| Threshold | When X > N, then Y | "When cycle >90 days, win rate drops" |

**Validator stress-tests:**
- "Wait, what's the boundary condition?"
- "Does this hold for [segment]?"
- "What are the exceptions?"

**Output:**
```yaml
rules:
  - id: R1
    statement: "If [condition], then [prediction] (probability)"
    derived_from: [P1, P2]  # Pattern IDs
    
    structure:
      condition: "[When this is true]"
      prediction: "[This will happen]"
      probability: 0.0-1.0
      mechanism: "[Why the rule works]"
      
    applicability:
      domain: "[Where rule applies]"
      segments: ["[Valid segments]"]
      exceptions: ["[Known exceptions]"]
```

**Example:**
```xml
<think_explorer>
  Forming rule from P1:
  
  R1: "Case studies convert at 2x+ rate vs other content types"
  Applies to: Bottom-funnel, decision-stage content
  Exception: Narrow technical audiences
</think_explorer>

<think_validator>
  Wait, is 2x the right threshold? Let me check variance...
  
  Range: 1.8x to 2.7x across samples.
  2x is conservative. Rule holds.
  
  But what about sample size? N=8 is moderate confidence.
  Flag: Revisit when N≥15.
</think_validator>
```

**Gate:** Rules must have explicit applicability bounds.

---

### Stage 4: Confidence Bounds

**Both personas calculate confidence:**

**Confidence Formula:**
```
Confidence = Base(N) × min(Strength, Consistency, Recency)
```

**Base from sample size:**
- N < 5: max 0.40
- N 5-10: max 0.60
- N 11-20: max 0.80
- N > 20: max 0.95

**Validator identifies exceptions:**
```yaml
confidence_analysis:
  rule_id: R1
  confidence: float
  
  calculation:
    base: float
    strength: float
    consistency: float
    recency: float
    final: float
    
  bounds:
    lower: float
    upper: float
    
  exceptions:
    identified:
      - instance: "[Description]"
        explanation: "[Why exception]"
    exception_rate: float
    
  validity:
    expires: "[When to re-validate]"
    invalidated_by: ["[Conditions]"]
```

**Belief Updates:**
```yaml
belief_implications:
  validates:
    - belief: "[Existing assumption]"
      finding: "[What pattern suggests]"
      
  invalidates:
    - belief: "[Existing assumption]"
      finding: "[What pattern contradicts]"
      
  new_hypotheses:
    - hypothesis: "[New belief from pattern]"
      test: "[How to validate]"
```

**Gate:** Exception rate must be <30% for actionable rules.

## Complete Conversation Example

```xml
<personas>
  <explorer traits="E:4,A:3,C:5,N:3,O:5">
    Pattern-finder, sees connections across data
  </explorer>
  <validator traits="E:2,A:3,C:5,N:5,O:3">
    Edge-case finder, stress-tests generalizations
  </validator>
</personas>

<think_explorer>
  Stage 1 - Collection:
  24 content pieces from Jul-Dec 2024
  Completeness: 88%, Consistency: 92%
  
  Stage 2 - Pattern Detection:
  P1: Case studies convert 2.3x average (strength 0.82)
  P2: Technical depth correlates with enterprise demos (r=0.68)
  P3: Posts >2000 words perform better on SEO (strength 0.75)
  P4: LinkedIn declining, organic rising (strength 0.70)
</think_explorer>

<think_validator>
  Wait, let me check P1 exceptions...
  
  API case study underperformed. 1/8 exception.
  Explanation: Too narrow, technical audience.
  Exception rate: 12.5% - acceptable.
  
  For P3, what's the exact threshold?
</think_validator>

<think_explorer>
  Let me check the breakpoint for P3...
  
  Clear step function at 2000 words.
  Below 2000: average organic traffic
  Above 2000: 2.1x organic traffic
  
  Threshold pattern confirmed.
</think_explorer>

<think_validator>
  Good. But P2 correlation (r=0.68) doesn't prove causation.
  What's the mechanism?
</think_validator>

<think_explorer>
  Proposed mechanism: Technical content signals expertise →
  Enterprise buyers trust more → More likely to request demo
  
  This is hypothesis, not proven. Flag for experimentation.
</think_explorer>

<synthesis>
  Rules formed:
  R1: Case studies convert 2x+ (confidence 0.75, N=8)
  R2: Technical content attracts enterprise (confidence 0.68, needs test)
  R3: SEO content should target >2000 words (confidence 0.70)
  
  Immediate actions:
  - Shift content mix: 40% case studies
  - Increase average word count to 2200+
  
  Monitor:
  - LinkedIn ROI declining—consider reducing investment
  
  Experiment needed:
  - Test R2 mechanism with A/B on technical depth
</synthesis>
```

## Quality Gates Summary

| Stage | Gate |
|-------|------|
| Collection | ≥5 instances |
| Detection | ≥1 pattern with strength ≥0.6 |
| Generalization | Explicit applicability bounds |
| Confidence | Exception rate <30% |

## Anti-Patterns

| Avoid | Do Instead |
|-------|------------|
| Small N conclusions | Wait for sufficient data |
| Correlation = causation | Test mechanism separately |
| Ignoring exceptions | Document and explain each |
| Unbounded rules | Specify where rule applies |
| Overconfident generalization | State confidence with bounds |
