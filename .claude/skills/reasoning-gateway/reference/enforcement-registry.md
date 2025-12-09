# Enforcement Registry

Flows that MUST use specific reasoning modes. Gateway cannot override.

## Enforced Flows

### Causal-Enforced (Process Execution)

| Flow Type | Mode | Rationale |
|-----------|------|-----------|
| `sales_pipeline` | causal | Deal progression is inherently causal: lead → qualify → demo → pilot → close |
| `sales_campaign` | causal | Outreach sequences follow causal chains |
| `marketing_campaign` | causal | Campaign execution: create → publish → promote → measure |
| `engineering_build` | causal | Specification → Design → Implementation → Verification |
| `business_thread` | causal | Business decisions follow 6-stage causal flow |
| `ops_routine` | causal | Operational routines are deterministic sequences |

### Direct-Enforced (Human Required)

| Flow Type | Mode | Rationale |
|-----------|------|-----------|
| `legal_review` | direct | Legal decisions require human judgment |
| `financial_audit` | direct | Compliance requires human verification |
| `contract_signing` | direct | Legal commitment requires human authority |
| `hiring_decision` | direct | Employment decisions require human approval |
| `termination` | direct | Employment termination requires human authority |
| `fundraising_pitch` | direct | Investor relations require human presence |

## Enforcement Rules

### Absolute Rules (Never Override)

1. **Safety-critical flows:** Any flow involving physical safety, health, or wellbeing
2. **Legal obligations:** Contract, compliance, regulatory
3. **Financial commitments:** Spending >$10K, revenue recognition
4. **Employment actions:** Hiring, firing, compensation changes
5. **Customer relationships:** Calls, negotiations, escalations

### Conditional Enforcement

Some flows enforce modes conditionally:

```yaml
conditional_enforcement:
  strategic_planning:
    default_mode: dialectical
    enforce_when: "involves budget >$100K OR timeline >6 months"
    fallback: causal
    
  market_analysis:
    default_mode: abductive
    enforce_when: "anomaly detected OR surprise present"
    fallback: causal
    
  competitive_response:
    default_mode: counterfactual
    enforce_when: "competitor action requires response evaluation"
    fallback: causal
```

## Adding New Enforcements

To add a new enforced flow:

1. Identify flow type and required mode
2. Document rationale (why enforcement needed)
3. Define bypass conditions (if any)
4. Add to registry with impact assessment
5. Flag for human review if impact ≥0.8

```yaml
# Template for new enforcement
new_enforcement:
  flow_type: "example_flow"
  mode: causal | abductive | analogical | dialectical | counterfactual | direct
  rationale: "Clear explanation of why enforcement is needed"
  bypass_conditions: null | ["condition1", "condition2"]
  added_date: ISO8601
  added_by: human | system
  impact: 0.0-1.0
```

## Bypass Protocol

Enforcement bypasses should be extremely rare. If bypass is needed:

1. **Document request:** Why is bypass needed?
2. **Human approval:** Bypasses require explicit human approval
3. **Log bypass:** Full audit trail
4. **Review outcome:** Was bypass appropriate?
5. **Update registry:** If pattern emerges, update enforcement rules

```yaml
bypass_log:
  timestamp: ISO8601
  flow_type: string
  requested_mode: ReasoningMode
  enforced_mode: ReasoningMode
  bypass_reason: string
  approved_by: human_id
  outcome: success | failure | partial
  recommendation: keep_enforcement | remove_enforcement | modify_conditions
```
