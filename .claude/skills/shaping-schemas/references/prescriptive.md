# Prescriptive Schema Reference

Provide actionable guidance and recommended direction.

## When to Use

Use prescriptive schema when output is:
- Recommendations
- "What should I do" answers
- Next steps
- Advice or guidance

## Output Structure

```yaml
prescriptive:
  objective: string
  context: string
  
  recommendation:
    primary: string
    rationale: string
    confidence: float
    
  alternatives:
    - alternative: string
      when_preferred: string
      trade_off: string
      
  trade_offs:
    - trade_off: string
      severity: high | medium | low
      mitigation: optional<string>
      
  risks:
    - risk: string
      likelihood: high | medium | low
      if_occurs: string
      mitigation: string
      
  immediate_actions:
    - action: string
      owner: optional<string>
      deadline: optional<string>
      success_criteria: optional<string>
      
  monitoring:
    - signal: string
      threshold: string
      response: string
```

## Construction Process

### Step 1: State Objective

What are we trying to achieve?

```yaml
objective: "Reduce customer churn from 5% to 2% monthly"
context: "Enterprise segment showing highest churn. 
         Exit interviews cite onboarding as top issue."
```

**Rule:** Objective should be specific and measurable.

### Step 2: Make Primary Recommendation

Single, clear recommendation:

```yaml
recommendation:
  primary: "Implement dedicated onboarding specialist for enterprise accounts"
  rationale: "Exit interviews show 60% cite onboarding issues. 
             Dedicated specialist addresses root cause directly.
             Competitors with specialists show 2x better retention."
  confidence: 0.75
```

**Rules:**
- ONE primary recommendation (not "do A and B")
- State confidence (0.0-1.0)
- Justify with evidence

### Step 3: Offer Alternatives

When might a different path make sense?

```yaml
alternatives:
  - alternative: "Self-serve onboarding with video tutorials"
    when_preferred: "Budget constrained (<$50K available)"
    trade_off: "Slower impact, 50% effectiveness of specialist"
    
  - alternative: "Outsource onboarding to partner"
    when_preferred: "Need immediate capacity, can't hire fast"
    trade_off: "Less control over quality, higher per-customer cost"
```

**Rule:** Alternatives are conditional, not wishy-washy hedging.

### Step 4: Acknowledge Trade-offs

What are we giving up with the primary recommendation?

```yaml
trade_offs:
  - trade_off: "Higher cost ($120K/year salary + overhead)"
    severity: medium
    mitigation: "ROI positive if churn drops 1.5%+ (likely)"
    
  - trade_off: "Single point of failure initially"
    severity: medium
    mitigation: "Document processes, plan for backup"
    
  - trade_off: "3-month ramp before full effectiveness"
    severity: low
    mitigation: "Use contractor bridge during ramp"
```

### Step 5: Identify Risks

What could go wrong?

```yaml
risks:
  - risk: "Can't hire qualified specialist quickly"
    likelihood: medium
    if_occurs: "Recommendation delayed 2-3 months"
    mitigation: "Start recruiting now, use contractor interim"
    
  - risk: "Churn root cause misdiagnosed"
    likelihood: low
    if_occurs: "Specialist doesn't impact churn"
    mitigation: "A/B test with subset before full commit"
```

### Step 6: Define Immediate Actions

What should happen right now?

```yaml
immediate_actions:
  - action: "Post job req for Onboarding Specialist"
    owner: "HR"
    deadline: "This week"
    success_criteria: "Req live on job boards"
    
  - action: "Identify 5 recent churned customers for interviews"
    owner: "CS team"
    deadline: "Next 3 days"
    success_criteria: "Interviews scheduled"
    
  - action: "Define onboarding playbook v1"
    owner: "Product"
    deadline: "2 weeks"
    success_criteria: "Draft reviewed by CS"
```

**Rule:** Actions are specific, owned, and time-bound.

### Step 7: Set Up Monitoring

How do we know if this is working?

```yaml
monitoring:
  - signal: "30-day enterprise churn rate"
    threshold: "If still >4% after 3 months"
    response: "Escalate, consider alternative approach"
    
  - signal: "Onboarding NPS"
    threshold: "If <40 after first month"
    response: "Diagnose, adjust playbook"
    
  - signal: "Time to value for new customers"
    threshold: "If >14 days average"
    response: "Review onboarding bottlenecks"
```

## Complete Example

```yaml
prescriptive:
  objective: "Reduce enterprise churn from 5% to 2% monthly"
  context: "Enterprise highest churn segment. Exit interviews cite
           onboarding as #1 issue (60% mention)."
           
  recommendation:
    primary: "Hire dedicated enterprise onboarding specialist"
    rationale: "Directly addresses top churn driver. Competitors
               with specialists retain 2x better. Clear ROI model."
    confidence: 0.75
    
  alternatives:
    - alternative: "Self-serve video onboarding"
      when_preferred: "Budget <$50K, need immediate action"
      trade_off: "~50% effectiveness, slower impact"
      
    - alternative: "Partner outsourcing"
      when_preferred: "Can't hire fast, need capacity now"
      trade_off: "Less control, higher unit cost"
      
  trade_offs:
    - trade_off: "$120K annual cost"
      severity: medium
      mitigation: "ROI positive at 1.5% churn reduction"
      
    - trade_off: "3-month ramp to effectiveness"
      severity: low
      mitigation: "Contractor bridge during ramp"
      
  risks:
    - risk: "Hiring takes too long"
      likelihood: medium
      if_occurs: "2-3 month delay"
      mitigation: "Start now, contractor interim"
      
    - risk: "Root cause misdiagnosed"
      likelihood: low
      if_occurs: "Specialist doesn't impact churn"
      mitigation: "A/B test with subset first"
      
  immediate_actions:
    - action: "Post specialist job req"
      owner: "HR"
      deadline: "This week"
      success_criteria: "Live on job boards"
      
    - action: "Interview 5 churned customers"
      owner: "CS team"
      deadline: "3 days"
      success_criteria: "Interviews scheduled"
      
    - action: "Draft onboarding playbook v1"
      owner: "Product"
      deadline: "2 weeks"
      success_criteria: "Reviewed by CS"
      
    - action: "Identify contractor backup"
      owner: "HR"
      deadline: "1 week"
      success_criteria: "3 candidates identified"
      
  monitoring:
    - signal: "30-day churn rate"
      threshold: ">4% after 3 months"
      response: "Escalate, consider pivot"
      
    - signal: "Onboarding NPS"
      threshold: "<40 after 1 month"
      response: "Diagnose, adjust playbook"
```

## Quality Gates

| Gate | Requirement |
|------|-------------|
| Objective specific | Measurable, not vague |
| Single primary | Not "A and B" or "it depends" |
| Confidence stated | 0.0-1.0 with justification |
| Alternatives conditional | "When preferred" specified |
| Trade-offs honest | What we're giving up |
| Actions owned | Who, when, done-criteria |

## Anti-Patterns

| Avoid | Do Instead |
|-------|------------|
| "You could do A or B" | Pick one, alternatives are conditional |
| "Consider doing X" | "Do X" with clear action |
| Unquantified trade-offs | "Costs $120K" not "costs more" |
| Actions without owners | Someone is responsible |
| Missing confidence | State uncertainty explicitly |
| No monitoring | How do we know it's working |

## Prescriptive vs Other Schemas

| If asked for... | Use... |
|-----------------|--------|
| "What should we do?" | prescriptive |
| "Pick between A, B, C" | decision |
| "Why did this happen?" | diagnostic |
| "How do we do this?" | procedural |
| "Is this ready?" | validation |
| "What are the risks?" | risk |

Prescriptive focuses on **recommending direction** when the question is open-ended. If options are already defined, use decision schema instead.
