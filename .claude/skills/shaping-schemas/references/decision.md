# Decision Schema Reference

Select one option with explicit trade-off justification.

## When to Use

Use decision schema when output is:
- Choosing between options
- Go/no-go determination
- Prioritization or ranking
- Recommendation with alternatives

## Output Structure

```yaml
decision:
  statement: string
  context: string
  deadline: optional<date>
  
  options:
    - name: string
      description: string
      pros: [string]
      cons: [string]
      scores:
        - criterion: string
          score: 0.0-1.0
          rationale: string
          
  criteria:
    - criterion: string
      weight: float  # Sum to 1.0
      definition: string
      
  recommendation: string  # Exactly ONE
  rationale: string
  
  trade_offs:
    - trade_off: string
      severity: high | medium | low
      accepted_because: string
      
  risks:
    - risk: string
      likelihood: high | medium | low
      mitigation: string
      
  revisit_triggers:
    - condition: string
      action: string
```

## Construction Process

### Step 1: Frame the Decision

State clearly:
- What is being decided
- Why now (what triggered this)
- Constraints and boundaries

```yaml
statement: "Select CRM platform for sales team"
context: "Current CRM contract expires in 90 days. 
         Team has grown from 5 to 25 reps."
deadline: "2024-03-01"
```

**Rule:** Decision statement must be specific. Not "improve sales tools" but "select CRM platform."

### Step 2: Enumerate Options

Include all viable options plus "do nothing":

```yaml
options:
  - name: "Salesforce"
    description: "Enterprise CRM, market leader"
    
  - name: "HubSpot"
    description: "Mid-market CRM with marketing integration"
    
  - name: "Renew current (Pipedrive)"
    description: "Extend existing contract"
    
  - name: "Do nothing"
    description: "Let contract lapse, use spreadsheets"
```

**Rule:** Always include "do nothing" or "status quo" as an option.

### Step 3: Define Criteria

What factors matter? Assign weights:

```yaml
criteria:
  - criterion: "Total cost (3 year)"
    weight: 0.25
    definition: "License + implementation + training"
    
  - criterion: "Sales team fit"
    weight: 0.30
    definition: "Match to current workflow, learning curve"
    
  - criterion: "Scalability"
    weight: 0.20
    definition: "Supports growth to 100 reps"
    
  - criterion: "Integration"
    weight: 0.15
    definition: "Works with existing stack"
    
  - criterion: "Time to value"
    weight: 0.10
    definition: "Days until team productive"
```

**Rule:** Weights must sum to 1.0. Justify each weight.

### Step 4: Score Each Option

For each option, score against each criterion:

```yaml
options:
  - name: "Salesforce"
    scores:
      - criterion: "Total cost"
        score: 0.4
        rationale: "$180K/3yr, highest cost"
        
      - criterion: "Sales team fit"
        score: 0.7
        rationale: "Powerful but complex, learning curve"
        
      - criterion: "Scalability"
        score: 0.95
        rationale: "Proven at any scale"
        
      - criterion: "Integration"
        score: 0.9
        rationale: "Extensive API and ecosystem"
        
      - criterion: "Time to value"
        score: 0.5
        rationale: "3-month implementation typical"
    
    # Weighted score = 0.4×0.25 + 0.7×0.30 + 0.95×0.20 + 0.9×0.15 + 0.5×0.10
    # = 0.10 + 0.21 + 0.19 + 0.135 + 0.05 = 0.685
```

### Step 5: Make Recommendation

**Rule:** Exactly ONE option. Not "either A or B" or "it depends."

```yaml
recommendation: "HubSpot"
rationale: "Highest weighted score (0.78). Best balance of cost, 
           team fit, and speed. Adequate scalability for 3-year horizon.
           Salesforce overkill for current stage."
```

### Step 6: Acknowledge Trade-offs

What are we giving up?

```yaml
trade_offs:
  - trade_off: "Less scalability than Salesforce"
    severity: medium
    accepted_because: "Adequate for 3-year plan. Can migrate later if needed."
    
  - trade_off: "Fewer enterprise features"
    severity: low
    accepted_because: "Don't need enterprise features at current stage."
```

### Step 7: Identify Risks

What could go wrong with this decision?

```yaml
risks:
  - risk: "HubSpot pricing increases at renewal"
    likelihood: medium
    mitigation: "Negotiate multi-year contract"
    
  - risk: "Team outgrows platform faster than expected"
    likelihood: low
    mitigation: "Build export capability, plan migration path"
```

### Step 8: Define Revisit Triggers

When should we reconsider?

```yaml
revisit_triggers:
  - condition: "Team exceeds 50 reps"
    action: "Re-evaluate scalability needs"
    
  - condition: "HubSpot announces price increase >20%"
    action: "Accelerate migration planning"
    
  - condition: "Major workflow friction after 6 months"
    action: "Assess Salesforce migration"
```

## Complete Example

```yaml
decision:
  statement: "Select CRM platform for sales team"
  context: "Contract expires 90 days. Team grew 5→25 reps."
  deadline: "2024-03-01"
  
  options:
    - name: "Salesforce"
      description: "Enterprise CRM leader"
      pros:
        - "Unlimited scalability"
        - "Best integrations"
        - "Industry standard"
      cons:
        - "Highest cost ($180K/3yr)"
        - "Complex, steep learning curve"
        - "3-month implementation"
      weighted_score: 0.685
      
    - name: "HubSpot"
      description: "Mid-market with marketing"
      pros:
        - "Best team fit, intuitive"
        - "Moderate cost ($90K/3yr)"
        - "Fast implementation (4 weeks)"
      cons:
        - "Less scalable at enterprise"
        - "Fewer advanced features"
      weighted_score: 0.780
      
    - name: "Renew Pipedrive"
      description: "Current platform"
      pros:
        - "No change management"
        - "Lowest cost ($45K/3yr)"
      cons:
        - "Team has outgrown it"
        - "Missing needed features"
      weighted_score: 0.520
      
    - name: "Do nothing"
      description: "Use spreadsheets"
      pros:
        - "Zero license cost"
      cons:
        - "Operational chaos"
        - "Data loss risk"
      weighted_score: 0.150
      
  criteria:
    - criterion: "Total cost"
      weight: 0.25
    - criterion: "Sales team fit"
      weight: 0.30
    - criterion: "Scalability"
      weight: 0.20
    - criterion: "Integration"
      weight: 0.15
    - criterion: "Time to value"
      weight: 0.10
      
  recommendation: "HubSpot"
  rationale: "Highest score (0.78). Best cost/fit balance. 
             Adequate scale for 3-year plan."
             
  trade_offs:
    - trade_off: "Less scalable than Salesforce"
      severity: medium
      accepted_because: "Sufficient for 100 reps. Migrate if needed."
      
  risks:
    - risk: "Pricing increase at renewal"
      likelihood: medium
      mitigation: "Multi-year contract"
      
  revisit_triggers:
    - condition: "Team >50 reps"
      action: "Re-evaluate scale needs"
```

## Quality Gates

| Gate | Requirement |
|------|-------------|
| Statement specific | Not vague goal |
| Options complete | Includes "do nothing" |
| Criteria weighted | Sum to 1.0 |
| Single recommendation | Not "A or B" |
| Trade-offs explicit | Acknowledged with severity |
| Revisit defined | Know when to reconsider |

## Anti-Patterns

| Avoid | Do Instead |
|-------|------------|
| "It depends" | Pick one option |
| Missing "do nothing" | Always include status quo |
| Hidden criteria | Explicit weights |
| Ignoring trade-offs | Acknowledge what's given up |
| Permanent decision | Define revisit triggers |
