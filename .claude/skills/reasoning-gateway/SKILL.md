---
name: reasoning-gateway
description: Meta-reasoning orchestrator that selects and routes to appropriate reasoning modes based on context. Use when facing any non-trivial decision, analysis, or problem-solving task. Routes to causal, abductive, analogical, dialectical, or counterfactual reasoning skills based on context classification. Supports enforcement mode for flows requiring specific reasoning patterns.
---

# Reasoning Gateway

Meta-reasoning layer that classifies context and routes to specialized reasoning modes.

## Architecture

```
┌─────────────────────────────────────────────────┐
│           ENFORCEMENT LAYER (inviolable)        │
│  Hard-coded flows: compliance, safety, legal    │
│  Bypasses meta-reasoning, routes directly       │
└─────────────────────┬───────────────────────────┘
                      │ non-enforced contexts
                      ▼
┌─────────────────────────────────────────────────┐
│           REASONING GATEWAY (this skill)        │
│  Classify(context) → Select(mode) → Route       │
│  Can chain modes within single flow             │
└─────────────────────┬───────────────────────────┘
                      │ dispatches to
    ┌─────────┬───────┴───────┬─────────┬─────────┐
    ▼         ▼               ▼         ▼         ▼
┌────────┐┌────────┐    ┌──────────┐┌────────┐┌────────┐
│ Causal ││Abductive│    │Analogical││Dialect-││Counter-│
│        ││         │    │          ││ical    ││factual │
└────────┘└────────┘    └──────────┘└────────┘└────────┘
```

## Reasoning Modes

| Mode | Primary Use | Type Signature |
|------|-------------|----------------|
| **Causal** | Known process, clear cause-effect | `Input → Hypothesis → Implication → Decision → Action → Learning` |
| **Abductive** | Incomplete data, need explanation | `Observation → Hypotheses[] → Evidence → BestExplanation` |
| **Inductive** | Multiple observations, pattern extraction | `[Observation] → Pattern → Generalization → ConfidenceBounds` |
| **Analogical** | Novel situation, pattern matching | `Source → StructuralMap → Target → Adaptation` |
| **Dialectical** | Competing views, need synthesis | `Thesis → Antithesis → Synthesis` |
| **Counterfactual** | Decision evaluation, alternative paths | `Actual → Intervention → Alternative → Comparison` |

## Context Classification

### Step 1: Identify Primary Signal

Ask these questions in order (first match wins):

1. **Is this enforced?** → Check enforcement registry, route directly
2. **Do we know the causal graph?** → If yes, use **Causal**
3. **Are we explaining a single observation?** → If yes, use **Abductive**
4. **Do we have multiple similar observations?** → If yes, use **Inductive**
5. **Is this similar to something we've done?** → If yes, use **Analogical**
6. **Are there competing valid positions?** → If yes, use **Dialectical**
7. **Are we evaluating a past/hypothetical decision?** → If yes, use **Counterfactual**

### Step 2: Detect Composite Needs

Some contexts require chained reasoning:

```
Abductive → Causal
  "Why did this happen?" → "What do we do about it?"
  
Inductive → Causal
  "This pattern keeps happening" → "Implement process to address it"

Abductive → Inductive
  "Multiple anomalies explained" → "Is there a systemic pattern?"
  
Analogical → Causal
  "This is like our marketplace launch" → "Apply that playbook"
  
Dialectical → Counterfactual
  "Sales wants X, Eng wants Y" → "What if we chose X? Y?"
  
Counterfactual → Causal
  "What if we'd priced higher?" → "Should we reprice now?"

Inductive → Canvas Update
  "Pattern validated with high confidence" → "Update assumptions"
```

## Enforcement Registry

Some flows MUST use specific reasoning modes. Gateway cannot override.

```yaml
enforced_flows:
  # Causal-only (process execution)
  sales_pipeline:
    mode: causal
    reason: "Deal progression is inherently causal"
    
  marketing_campaign:
    mode: causal
    reason: "Campaign execution follows causal flow"
    
  engineering_build:
    mode: causal
    reason: "Specification → Implementation is causal"
    
  # Compliance (no reasoning, direct execution)
  legal_review:
    mode: direct
    reason: "Human review required, no AI reasoning"
    
  financial_audit:
    mode: direct
    reason: "Compliance requires human verification"
```

### Enforcement Check

```
IF context.flow_type IN enforced_flows:
  route_to(enforced_flows[context.flow_type].mode)
  SKIP meta-reasoning
ELSE:
  proceed with classification
```

## Mode Selection Algorithm

```python
def select_mode(context: Context) -> ReasoningMode:
    # Layer 1: Enforcement (inviolable)
    if context.flow_type in ENFORCEMENT_REGISTRY:
        return ENFORCEMENT_REGISTRY[context.flow_type].mode
    
    # Layer 2: Signal detection
    signals = extract_signals(context)
    
    # Layer 3: Primary mode selection
    if signals.has_known_causal_graph:
        primary = CAUSAL
    elif signals.is_single_explanation_needed:
        primary = ABDUCTIVE
    elif signals.has_multiple_similar_observations:
        primary = INDUCTIVE
    elif signals.has_structural_similarity:
        primary = ANALOGICAL
    elif signals.has_competing_positions:
        primary = DIALECTICAL
    elif signals.is_evaluating_alternatives:
        primary = COUNTERFACTUAL
    else:
        primary = CAUSAL  # Default fallback
    
    # Layer 4: Composite detection
    secondary = detect_follow_on_mode(context, primary)
    
    return CompositeMode(primary, secondary) if secondary else primary
```

## Signal Extraction

### Causal Signals
- "What happens if we..."
- "How do we achieve..."
- Process execution context
- Known workflow patterns
- Clear input → output relationship

### Abductive Signals
- "Why did X happen?"
- "What explains Y?"
- Anomaly or surprise present
- Data without clear cause
- Diagnostic context

### Inductive Signals
- "This keeps happening"
- "I've noticed a pattern"
- "Every time we do X..."
- Multiple similar observations
- "What's the trend?"
- "Is this systemic?"
- Review/retrospective context
- Accumulated thread learnings

### Analogical Signals
- "This is like..."
- "We did something similar..."
- New market/product/situation
- Pattern recognition opportunity
- Transfer learning context

### Dialectical Signals
- "On one hand... on the other..."
- Stakeholder disagreement
- Trade-off analysis needed
- Strategic tension present
- Multiple valid perspectives

### Counterfactual Signals
- "What if we had..."
- "What would happen if..."
- Decision post-mortem
- Scenario planning
- Alternative evaluation

## Routing Protocol

### Single Mode Routing

```
1. Classify context
2. Select primary mode
3. Invoke mode skill with full context
4. Receive mode output
5. Pass to next step (may trigger re-routing)
```

### Composite Mode Routing

```
1. Classify context
2. Detect composite need (primary + secondary)
3. Invoke primary mode skill
4. Transform output for secondary mode
5. Invoke secondary mode skill
6. Synthesize combined output
```

### Mode Handoff Contract

Each mode must output in a format consumable by downstream modes:

```yaml
mode_output:
  conclusion: "Primary finding or decision"
  confidence: 0.0-1.0
  evidence: ["Supporting data points"]
  open_questions: ["Unresolved issues"]
  suggested_next_mode: optional<ReasoningMode>
```

## Observability

### Logging Schema

```yaml
reasoning_trace:
  timestamp: ISO8601
  context_hash: sha256
  enforcement_check: {matched: bool, flow_type: optional}
  signals_detected: [SignalType]
  mode_selected: ReasoningMode
  composite: bool
  secondary_mode: optional<ReasoningMode>
  execution_time_ms: int
  outcome: {success: bool, confidence: float}
```

### Metrics to Track

- Mode selection distribution (which modes get used?)
- Composite vs single mode ratio
- Enforcement bypass attempts (should be 0)
- Mode selection accuracy (retrospective validation)
- Average confidence by mode

## Available Mode Skills

Load as needed:

- `reasoning-causal` → `{baseDir}/stages/reasoning-causal/SKILL.md`
- `reasoning-abductive` → `{baseDir}/stages/reasoning-abductive/SKILL.md`
- `reasoning-inductive` → `{baseDir}/stages/reasoning-inductive/SKILL.md`
- `reasoning-analogical` → `{baseDir}/stages/reasoning-analogical/SKILL.md`
- `reasoning-dialectical` → `{baseDir}/stages/reasoning-dialectical/SKILL.md`
- `reasoning-counterfactual` → `{baseDir}/stages/reasoning-counterfactual/SKILL.md`

## Integration with Causal Flow

Existing `causal-flow` skill remains primary for operational threads. This gateway enhances it:

```
User request arrives
    ↓
reasoning-gateway classifies
    ↓
IF operational thread (sales/marketing/business/engineering):
    route to causal-flow (enforced)
ELSE IF strategic/analytical:
    select appropriate reasoning mode
    ↓
    may invoke causal-flow as secondary mode
```

## Execution Pattern

```
User: "Our enterprise conversion dropped 40% last quarter"

1. Gateway receives context
2. Enforcement check: NOT enforced (analytical, not operational)
3. Signal detection:
   - "dropped" → anomaly present ✓
   - "why" implied → explanation needed ✓
   - No known causal graph for this specific drop
4. Primary mode: ABDUCTIVE
5. Composite detection: Will need CAUSAL follow-on
6. Route to reasoning-abductive
7. Abductive output: "Top 3 hypotheses with evidence"
8. Route to reasoning-causal for response planning
9. Synthesize: "Root cause + action plan"
```

## Success Criteria

- **Correct routing:** Mode matches context type >90%
- **Enforcement integrity:** 0 bypasses of enforced flows
- **Latency:** Mode selection <100ms
- **Composability:** Smooth handoffs between modes
- **Observability:** Full trace for every decision

## Reference Documentation

- Mode specifications: `{baseDir}/reference/mode-specifications.md`
- Enforcement registry: `{baseDir}/reference/enforcement-registry.md`
- Signal patterns: `{baseDir}/reference/signal-patterns.md`
  