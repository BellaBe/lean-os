# Mode Specifications

Formal definitions of each reasoning mode with type signatures, interfaces, and composition rules.

## Type Signatures

### Causal Reasoning

```
Causal : Input → Hypothesis → Implication → Decision → Action → Learning

Where:
  Input       : Observation × Context → FactualStatement
  Hypothesis  : FactualStatement × CanvasAssumption → TestableHypothesis  
  Implication : TestableHypothesis → (Impact × Probability × Timeline)
  Decision    : Implication × Alternatives → Commitment
  Action      : Commitment → [ExecutableTask]
  Learning    : [ExecutedTask] × Outcomes → CanvasUpdate
```

### Abductive Reasoning

```
Abductive : Observation → Hypotheses[] → Evidence → BestExplanation

Where:
  Observation     : RawData × Surprise → AnomalyDescription
  Hypotheses      : AnomalyDescription → [PossibleCause]
  Evidence        : [PossibleCause] × AvailableData → [ScoredHypothesis]
  BestExplanation : [ScoredHypothesis] → (Cause × Confidence × NextSteps)
```

### Inductive Reasoning

```
Inductive : [Observation] → Pattern → Generalization → ConfidenceBounds

Where:
  Observations     : [Instance] → Dataset
  Pattern          : Dataset → (Regularity × Frequency)
  Generalization   : (Regularity × Frequency) → Rule
  ConfidenceBounds : Rule × SampleSize → (Confidence × Exceptions)
```

### Analogical Reasoning

```
Analogical : Source → StructuralMap → Target → Adaptation

Where:
  Source        : PriorExperience × Relevance → SourceDomain
  StructuralMap : SourceDomain → (Objects × Relations × Constraints)
  Target        : StructuralMap × NewContext → MappedStructure
  Adaptation    : MappedStructure × ContextDifferences → AdaptedSolution
```

### Dialectical Reasoning

```
Dialectical : Thesis → Antithesis → Synthesis

Where:
  Thesis     : Position × Evidence × Stakeholder → ArgumentA
  Antithesis : ArgumentA → CounterPosition × Evidence × Stakeholder → ArgumentB
  Synthesis  : (ArgumentA, ArgumentB) → IntegratedPosition × Tradeoffs
```

### Counterfactual Reasoning

```
Counterfactual : Actual → Intervention → Alternative → Comparison

Where:
  Actual       : Decision × Outcome → ActualWorld
  Intervention : ActualWorld × Δ → ModifiedPremise
  Alternative  : ModifiedPremise → ProjectedOutcome
  Comparison   : (ActualWorld, ProjectedOutcome) → DifferenceAnalysis
```

## Interface Contracts

### Input Contract (all modes)

```yaml
mode_input:
  context:
    type: string              # business | sales | marketing | engineering | strategy
    thread_id: optional<string>
    canvas_refs: [string]     # Links to relevant Canvas sections
  
  observation:
    raw_data: any             # Mode-specific input data
    timestamp: ISO8601
    source: string
    
  constraints:
    time_bound: optional<duration>
    resource_bound: optional<cost>
    must_reference: optional<[string]>  # Required Canvas sections
```

### Output Contract (all modes)

```yaml
mode_output:
  conclusion:
    statement: string         # Primary finding or decision
    confidence: float         # 0.0-1.0
    impact_score: float       # 0.0-1.0 (for gateway routing)
    
  evidence:
    supporting: [EvidenceItem]
    contradicting: [EvidenceItem]
    
  trace:
    mode_used: ReasoningMode
    steps: [ReasoningStep]    # Full reasoning chain
    duration_ms: int
    
  next:
    open_questions: [string]
    suggested_mode: optional<ReasoningMode>
    canvas_updates: [CanvasUpdate]
    threads_generated: [ThreadRef]
```

## Composition Rules

### Valid Mode Chains

| Primary | Secondary | Use Case |
|---------|-----------|----------|
| Abductive → Causal | Diagnose then act | "Why did X happen? What do we do?" |
| Abductive → Inductive | Multiple diagnoses | "We've explained 5 failures. Is there a pattern?" |
| Inductive → Causal | Pattern then act | "This keeps happening. Let's fix it systematically." |
| Inductive → Canvas | Pattern then update | "Pattern validated. Update assumptions." |
| Analogical → Causal | Learn then apply | "What did we do last time? Apply here." |
| Dialectical → Counterfactual | Resolve then simulate | "Stakeholders disagree. What if A? B?" |
| Counterfactual → Causal | Evaluate then act | "Should we have done X? Should we now?" |

### Invalid Chains (avoid)

| Chain | Why Invalid |
|-------|-------------|
| Causal → Abductive | Causal already has explanation; don't backtrack |
| Counterfactual → Abductive | Don't explain hypotheticals; they're already projections |
| Dialectical → Analogical | Synthesis is context-specific; analogies break it |

### Chain Handoff Protocol

```yaml
handoff:
  from_mode: ReasoningMode
  to_mode: ReasoningMode
  
  transform:
    # Map output of from_mode to input of to_mode
    conclusion → observation.raw_data
    evidence → context.canvas_refs
    open_questions → constraints.must_reference
    
  preserve:
    - confidence (carry forward, don't reset)
    - trace (append, don't replace)
    - canvas_refs (union of both)
```

## Mode-Specific Constraints

### Causal

- **Must have:** Canvas hypothesis reference (Stage 2)
- **Must produce:** Impact score (Stage 4)
- **Must update:** Canvas assumptions (Stage 6)
- **SLA:** Complete within 24h per stage

### Abductive

- **Must have:** Anomaly or surprise description
- **Must produce:** ≥3 hypotheses ranked by likelihood
- **Must include:** Evidence for/against each hypothesis
- **SLA:** Hypothesis generation within 1h

### Inductive

- **Must have:** ≥5 observations (≥3 for exploratory)
- **Must produce:** ≥1 pattern with confidence score
- **Must include:** Exception identification and confidence bounds
- **Must validate:** Pattern stability and mechanism plausibility
- **SLA:** Pattern analysis within 2h

### Analogical

- **Must have:** Source case with documented outcome
- **Must produce:** Explicit structural mapping
- **Must include:** Context differences and adaptations
- **SLA:** Source retrieval within 30min

### Dialectical

- **Must have:** ≥2 competing positions with stakeholders
- **Must produce:** Synthesis or clear decision
- **Must include:** Trade-offs acknowledged by all parties
- **SLA:** Synthesis within 48h (allows stakeholder input)

### Counterfactual

- **Must have:** Actual decision and observed outcome
- **Must produce:** ≥2 alternative scenarios
- **Must include:** Probability and impact of alternatives
- **SLA:** Scenario generation within 2h

## Quality Gates

### Per-Mode Gates

| Mode | Gate Criteria | Failure Action |
|------|---------------|----------------|
| Causal | All 6 stages complete, Canvas updated | Block, flag incomplete |
| Abductive | ≥3 hypotheses, ranked with evidence | Request more hypotheses |
| Inductive | ≥1 pattern with ≥0.6 confidence, exceptions identified | Collect more data or lower threshold |
| Analogical | Structural mapping explicit, adaptations listed | Request mapping clarification |
| Dialectical | Both positions represented fairly, synthesis attempted | Request stakeholder input |
| Counterfactual | Actual vs alternative comparison complete | Request comparison |

### Cross-Mode Quality

- **Confidence calibration:** Modes should produce similar confidence for similar certainty
- **Evidence standards:** Evidence quality consistent across modes
- **Trace completeness:** Every step documented, no black boxes
