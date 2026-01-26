# Validation Schema Reference

Define how success will be verified.

## Output Structure

```yaml
validation:
  target: string
  
  success_criteria:
    - criterion: string
      metric: string
      threshold: string
      measurement_method: string
      
  validation_methods:
    - method: string
      covers: [string]
      duration: string
      
  failure_conditions:
    - condition: string
      threshold: string
      response: string
      
  rollback_triggers:
    - trigger: string
      action: string
```

## Construction Rules

1. **Criteria must be measurable** — Not "good performance" but "p95 < 200ms"
2. **Methods must map to criteria** — Every criterion has a test
3. **Failure is explicit** — What number means failure
4. **Rollback defined** — When and how to undo

## Example

```yaml
validation:
  target: "New checkout flow deployment"
  
  success_criteria:
    - criterion: "Conversion rate maintained"
      metric: "Checkout completion rate"
      threshold: "≥95% of baseline (currently 3.2%)"
      measurement_method: "A/B test, 50/50 split"
      
    - criterion: "No latency regression"
      metric: "p95 page load"
      threshold: "<500ms"
      measurement_method: "RUM data"
      
  validation_methods:
    - method: "A/B test"
      covers: ["Conversion rate"]
      duration: "7 days or 10K transactions"
      
    - method: "Synthetic monitoring"
      covers: ["Latency"]
      duration: "Continuous"
      
  failure_conditions:
    - condition: "Conversion drops >5%"
      threshold: "Completion rate <3.04%"
      response: "Pause rollout, investigate"
      
  rollback_triggers:
    - trigger: "Conversion drop >10% for 24h"
      action: "Automatic rollback to previous version"
```

## Quality Gates

| Gate | Requirement |
|------|-------------|
| Criteria measurable | Numbers, not adjectives |
| Methods mapped | Each criterion has test |
| Thresholds explicit | Clear pass/fail line |
| Rollback defined | Know how to undo |
