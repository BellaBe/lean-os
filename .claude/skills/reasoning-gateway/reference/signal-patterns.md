# Signal Patterns

Patterns that indicate which reasoning mode to use. Gateway uses these for context classification.

## Signal Detection Framework

```
Context arrives
    ↓
Extract linguistic signals
Extract structural signals
Extract domain signals
    ↓
Score each mode (0.0-1.0)
    ↓
Select highest score (with composite detection)
```

## Causal Signals

### Linguistic Patterns

| Pattern | Example | Confidence |
|---------|---------|------------|
| "What happens if..." | "What happens if we raise prices?" | 0.9 |
| "How do we..." | "How do we increase conversion?" | 0.85 |
| "If we... then..." | "If we launch early, then we'll..." | 0.9 |
| "What's the impact of..." | "What's the impact of this feature?" | 0.8 |
| "Execute/implement/deploy" | "Deploy the new pricing" | 0.95 |
| "Plan for..." | "Plan for Q2 launch" | 0.85 |

### Structural Patterns

| Pattern | Detection | Confidence |
|---------|-----------|------------|
| Thread exists | `threads/{type}/{name}/` present | 0.9 |
| Canvas reference | Links to `strategy/canvas/` | 0.8 |
| Known workflow | Matches sales/marketing/business pattern | 0.95 |
| Action list | Bulleted tasks, assignments, deadlines | 0.85 |

### Domain Patterns

| Domain | Context | Confidence |
|--------|---------|------------|
| Sales pipeline | Deal stage progression | 0.95 |
| Marketing campaign | Content → publish → measure | 0.9 |
| Engineering build | Spec → design → implement | 0.9 |
| Operations | Routine execution | 0.85 |

## Abductive Signals

### Linguistic Patterns

| Pattern | Example | Confidence |
|---------|---------|------------|
| "Why did..." | "Why did conversion drop?" | 0.95 |
| "What explains..." | "What explains this behavior?" | 0.9 |
| "What's causing..." | "What's causing the delay?" | 0.9 |
| "How come..." | "How come users aren't converting?" | 0.85 |
| "Something's wrong with..." | "Something's wrong with the funnel" | 0.8 |
| "I don't understand..." | "I don't understand this data" | 0.75 |

### Structural Patterns

| Pattern | Detection | Confidence |
|---------|-----------|------------|
| Anomaly present | Metric deviation >20% from baseline | 0.9 |
| Unexpected outcome | Prediction vs actual mismatch | 0.85 |
| No clear cause | Data without explanation | 0.8 |
| Diagnostic context | Error logs, support tickets | 0.85 |

### Domain Patterns

| Domain | Context | Confidence |
|--------|---------|------------|
| Customer behavior | "Users are doing X unexpectedly" | 0.9 |
| Market signals | "Competitor did Y, why?" | 0.85 |
| Performance issues | "System is slow, why?" | 0.9 |
| Revenue changes | "MRR dropped, what happened?" | 0.95 |

## Inductive Signals

### Linguistic Patterns

| Pattern | Example | Confidence |
|---------|---------|------------|
| "This keeps happening..." | "This keeps happening with enterprise deals" | 0.95 |
| "I've noticed a pattern..." | "I've noticed a pattern in churn" | 0.95 |
| "Every time we..." | "Every time we launch, X happens" | 0.9 |
| "What's the trend..." | "What's the trend in conversion?" | 0.85 |
| "Is this systemic..." | "Is this systemic or one-off?" | 0.9 |
| "Looking across..." | "Looking across all deals..." | 0.85 |
| "What do these have in common..." | "What do lost deals have in common?" | 0.9 |
| "N out of M..." | "7 out of 10 deals stalled at legal" | 0.95 |

### Structural Patterns

| Pattern | Detection | Confidence |
|---------|-----------|------------|
| Multiple threads with similar outcomes | ≥3 threads with same learning | 0.9 |
| Repeated observations | Same phenomenon observed N times | 0.85 |
| Review/retrospective context | Quarterly review, post-mortem | 0.8 |
| Aggregation request | "Summarize", "analyze across" | 0.85 |
| Time series data | Multiple data points over time | 0.8 |

### Domain Patterns

| Domain | Context | Confidence |
|--------|---------|------------|
| Sales patterns | "What predicts deal success?" | 0.9 |
| Marketing patterns | "Which content themes work?" | 0.85 |
| Product patterns | "What features get requested together?" | 0.85 |
| Operational patterns | "What failures keep recurring?" | 0.9 |
| Canvas validation | "Which assumptions keep getting validated?" | 0.9 |

### Distinction from Abductive

| Signal | Abductive | Inductive |
|--------|-----------|-----------|
| Quantity | Single observation | Multiple observations |
| Question | "Why did THIS happen?" | "What KEEPS happening?" |
| Output | Explanation of one event | Pattern/rule from many |
| Example | "Why did deal X fail?" | "Why do deals keep failing at legal?" |

## Analogical Signals

### Linguistic Patterns

| Pattern | Example | Confidence |
|---------|---------|------------|
| "This is like..." | "This is like our Shopify launch" | 0.95 |
| "Similar to..." | "Similar to what we did with X" | 0.9 |
| "We did something like this..." | "We did something like this before" | 0.85 |
| "Reminds me of..." | "Reminds me of the Y project" | 0.8 |
| "Apply the same..." | "Apply the same approach as Z" | 0.9 |
| "What worked for..." | "What worked for marketplace?" | 0.85 |

### Structural Patterns

| Pattern | Detection | Confidence |
|---------|-----------|------------|
| New market entry | No existing threads for this market | 0.8 |
| New product launch | First thread for product type | 0.8 |
| Pattern recognition | Structural similarity to past case | 0.85 |
| Cross-domain transfer | Applying X domain logic to Y | 0.9 |

### Domain Patterns

| Domain | Context | Confidence |
|--------|---------|------------|
| Market expansion | "Enter new market like we did before" | 0.9 |
| Product iteration | "Build this like the other feature" | 0.85 |
| Partnership | "Structure deal like the X partnership" | 0.85 |
| Hiring | "Hire like we did for role Y" | 0.8 |

## Dialectical Signals

### Linguistic Patterns

| Pattern | Example | Confidence |
|---------|---------|------------|
| "On one hand... on the other..." | "On one hand X, on the other Y" | 0.95 |
| "Some say... others say..." | "Sales says X, Eng says Y" | 0.9 |
| "Trade-off between..." | "Trade-off between speed and quality" | 0.9 |
| "Debate/disagreement" | "There's disagreement about..." | 0.85 |
| "Pros and cons" | "What are the pros and cons?" | 0.8 |
| "Both have merit" | "Both approaches have merit" | 0.85 |

### Structural Patterns

| Pattern | Detection | Confidence |
|---------|-----------|------------|
| Multiple stakeholders | ≥2 named parties with positions | 0.9 |
| Competing proposals | ≥2 explicit alternatives | 0.85 |
| Resource conflict | Same resource, different uses | 0.8 |
| Priority dispute | Different rankings of importance | 0.85 |

### Domain Patterns

| Domain | Context | Confidence |
|--------|---------|------------|
| Strategy | "Growth vs profitability" | 0.9 |
| Resource allocation | "Team A vs Team B needs" | 0.85 |
| Product direction | "Feature X vs Feature Y" | 0.85 |
| Hiring | "Candidate A vs Candidate B" | 0.8 |

## Counterfactual Signals

### Linguistic Patterns

| Pattern | Example | Confidence |
|---------|---------|------------|
| "What if we had..." | "What if we had priced higher?" | 0.95 |
| "What would happen if..." | "What would happen if we pivoted?" | 0.9 |
| "If we had done X instead..." | "If we had launched earlier..." | 0.9 |
| "Should we have..." | "Should we have taken funding?" | 0.85 |
| "Imagine if..." | "Imagine if we'd hired Y" | 0.8 |
| "Alternative scenario" | "What's the alternative scenario?" | 0.85 |

### Structural Patterns

| Pattern | Detection | Confidence |
|---------|-----------|------------|
| Past decision review | Reference to completed thread | 0.85 |
| Post-mortem context | Analyzing after outcome known | 0.9 |
| Scenario planning | Future with multiple branches | 0.8 |
| Decision comparison | Evaluating options not taken | 0.9 |

### Domain Patterns

| Domain | Context | Confidence |
|--------|---------|------------|
| Pricing | "What if we'd charged more?" | 0.9 |
| Timing | "What if we'd launched earlier/later?" | 0.85 |
| Strategy | "What if we'd taken a different path?" | 0.9 |
| Hiring | "What if we'd hired differently?" | 0.8 |

## Composite Detection

### Chain Indicators

| Primary Signal | Secondary Signal | Composite |
|----------------|------------------|-----------|
| Abductive (why?) | + action implied | Abductive → Causal |
| Analogical (like X) | + execute | Analogical → Causal |
| Dialectical (debate) | + evaluate outcomes | Dialectical → Counterfactual |
| Counterfactual (what if) | + decide now | Counterfactual → Causal |

### Composite Scoring

```python
def detect_composite(context, primary_mode):
    secondary_signals = extract_signals(context, exclude=primary_mode)
    
    if primary_mode == ABDUCTIVE:
        if has_action_signals(context):
            return (primary_mode, CAUSAL)
            
    if primary_mode == ANALOGICAL:
        if has_execution_signals(context):
            return (primary_mode, CAUSAL)
            
    if primary_mode == DIALECTICAL:
        if has_outcome_evaluation(context):
            return (primary_mode, COUNTERFACTUAL)
            
    if primary_mode == COUNTERFACTUAL:
        if has_present_decision(context):
            return (primary_mode, CAUSAL)
            
    return (primary_mode, None)
```

## Confidence Thresholds

| Decision | Threshold | Action |
|----------|-----------|--------|
| Clear mode | ≥0.85 | Route immediately |
| Probable mode | 0.7-0.84 | Route with logging |
| Uncertain | 0.5-0.69 | Consider composite or ask |
| Ambiguous | <0.5 | Default to causal or ask |

## Fallback Rules

1. **No clear signal:** Default to Causal (most general)
2. **Equal scores:** Prefer Causal > Abductive > Analogical > Dialectical > Counterfactual
3. **Conflicting signals:** Ask for clarification
4. **Enforcement overrides:** Always respect enforcement, ignore signals
