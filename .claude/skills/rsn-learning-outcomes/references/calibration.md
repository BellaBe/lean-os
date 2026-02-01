# Calibration

Adjust prediction confidence based on track record.

## When to Use

- Pattern of over- or under-confidence detected
- Predictions consistently wrong in one direction
- High-stakes decisions depend on accurate confidence
- Systematic bias suspected
- Periodic review of forecasting accuracy

## Mental Model

**Weather forecaster:** When I say 80% chance of rain, it should rain 80% of the time.

If "80% confident" predictions are right 60% of the time → overconfident
If "80% confident" predictions are right 95% of the time → underconfident

## Perfect Calibration

| Stated Confidence | Should Be Correct |
|-------------------|-------------------|
| 50% | 50% of the time |
| 70% | 70% of the time |
| 90% | 90% of the time |

## Process

### 1. Assemble Track Record

Collect past predictions with outcomes.

**Minimum:** 30+ predictions for meaningful analysis

**For each prediction record:**
- Prediction statement
- Confidence level stated
- Date made
- Outcome (correct/incorrect)
- Date resolved

### 2. Stratify by Confidence Level

Group predictions by confidence bucket.

**Typical buckets:**
- 50-59%
- 60-69%
- 70-79%
- 80-89%
- 90-100%

### 3. Calculate Calibration Error

For each bucket:
- Count predictions
- Count correct
- Calculate actual accuracy
- Calculate error (stated confidence - actual accuracy)

**Overall calibration error:** Mean of absolute errors across buckets

### 4. Identify Patterns

Look for systematic biases.

**Questions:**
- Which confidence levels are miscalibrated?
- Is the direction consistent (always over or under)?
- Does it vary by domain?
- Does it vary by time horizon?

### 5. Define Adjustment Rules

Create rules to correct systematic bias.

**Rule types:**
- **Linear shift:** "Subtract 10% from all estimates"
- **Bucket-specific:** "90%+ → treat as 75%"
- **Domain-specific:** "Timeline estimates: -20%"
- **Situation-specific:** "New technology: -25%"

### 6. Monitor Ongoing Calibration

Track whether adjustments are working.

**Metrics:**
- Rolling calibration error (last 30 predictions)
- Domain-specific calibration

**Triggers:**
- Calibration error > 25% → review rules
- New domain → default to lower confidence

## Output Format

```markdown
## Calibration Review: [Domain]

**Period:** [Timeframe analyzed]
**Predictions analyzed:** [N]

### Track Record Summary

**Overall:**
- Total predictions: [N]
- Overall accuracy: [X%]
- Average stated confidence: [Y%]
- Calibration error: [Z%]
- Direction: [Overconfident / Underconfident / Well-calibrated]

### By Confidence Level

| Bucket | Count | Accuracy | Stated | Error | Direction |
|--------|-------|----------|--------|-------|-----------|
| 90-100% | [N] | [X%] | ~95% | [Y%] | [Over/Under] |
| 80-89% | [N] | [X%] | ~85% | [Y%] | [Over/Under] |
| 70-79% | [N] | [X%] | ~75% | [Y%] | [Over/Under] |

### By Domain (if applicable)

| Domain | Predictions | Error | Direction |
|--------|-------------|-------|-----------|
| [Domain 1] | [N] | [X%] | [Over/Under] |
| [Domain 2] | [N] | [X%] | [Over/Under] |

### Patterns Identified

- [Pattern 1]: [Evidence]
- [Pattern 2]: [Evidence]

### Root Causes

**For overconfidence:**
- [Cause]: [Evidence]

**For underconfidence:**
- [Cause]: [Evidence]

### Adjustment Rules

**Rule 1:** [Statement]
- Applies to: [Scope]
- Rationale: [Why this adjustment]
- Implementation: [How to apply]

**Rule 2:** [Statement]
- Applies to: [Scope]
- Rationale: [Why this adjustment]

### Monitoring Plan

**Review schedule:** [Frequency]

**Trigger for re-review:**
- [Condition 1]
- [Condition 2]

**Next review:** [Date]
```

## Common Calibration Patterns

### Planning Fallacy
Timeline and effort estimates are too optimistic.

**Pattern:** 80% confident estimates are only 50% accurate

**Adjustment:** Apply 1.3-1.5x multiplier to timelines

### Optimism Bias
Positive outcomes overestimated.

**Pattern:** High confidence in success, lower actual success rate

**Adjustment:** Reduce confidence by 10-20% for success predictions

### Confidence in Familiar Domains
Well-calibrated in expertise areas, miscalibrated outside.

**Pattern:** Domain-specific calibration varies widely

**Adjustment:** Domain-specific rules

### Anchoring on First Estimate
Initial estimate anchors subsequent thinking.

**Pattern:** First estimate strongly predicts final, regardless of new info

**Adjustment:** Deliberately revise initial estimates upward

## Calibration Exercises

### Confidence Interval Practice
Give 90% confidence intervals for factual questions. Check: Do 9/10 contain the true value?

### Binary Prediction Tracking
Make 50 predictions at various confidence levels. Check: Calibration curve matches diagonal?

### Pre-Mortem
Before high-confidence prediction, imagine being wrong. What would have caused that?

## Anti-Patterns

| Avoid | Problem | Do Instead |
|-------|---------|------------|
| No tracking | Can't know if calibrated | Log predictions and outcomes |
| Small samples | Unreliable conclusions | Wait for 30+ predictions |
| Ignoring domain differences | Miss systematic patterns | Stratify by domain |
| Over-adjusting | Oscillating accuracy | Gradual adjustments |
| Not updating rules | Rules become stale | Regular review |
| One-size-fits-all | Domain-specific patterns | Domain-specific rules |

## Calibration Checklist

- [ ] Track record assembled (30+ predictions)
- [ ] Predictions stratified by confidence level
- [ ] Accuracy calculated per stratum
- [ ] Calibration error computed
- [ ] Direction identified (over/under/well-calibrated)
- [ ] Patterns identified by domain
- [ ] Root causes investigated
- [ ] Adjustment rules defined
- [ ] Implementation plan created
- [ ] Monitoring schedule set
- [ ] Next review scheduled
