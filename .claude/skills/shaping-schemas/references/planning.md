# Planning Schema Reference

Translate goals into phased execution plans.

## When to Use

Use planning schema when output is:
- Roadmap or timeline
- Project plan with phases
- Rollout strategy
- Implementation sequence

## Output Structure

```yaml
plan:
  name: string
  goal: string
  owner: string
  created: date
  
  constraints:
    - constraint: string
      type: time | budget | resource | dependency
      
  scope:
    in: [string]
    out: [string]
    assumptions: [string]
    
  phases:
    - name: string
      objective: string
      duration: string
      start_condition: string
      
      milestones:
        - milestone: string
          criteria: string
          date: optional<date>
          
      deliverables:
        - deliverable: string
          owner: string
          
      resources:
        - resource: string
          allocation: string
          
  dependencies:
    - dependency: string
      type: internal | external
      owner: string
      risk_if_delayed: string
      
  risks:
    - risk: string
      phase: string
      likelihood: high | medium | low
      impact: high | medium | low
      mitigation: string
      
  success_criteria:
    - criterion: string
      measurement: string
```

## Construction Process

### Step 1: State Goal and Constraints

What are we trying to achieve? What limits us?

```yaml
goal: "Launch self-serve onboarding for SMB customers"
owner: "Product team"

constraints:
  - constraint: "Must launch before Q2"
    type: time
    
  - constraint: "No new headcount"
    type: resource
    
  - constraint: "Cannot change billing system"
    type: dependency
```

### Step 2: Define Scope

What's in and out?

```yaml
scope:
  in:
    - "Self-serve signup flow"
    - "Automated provisioning"
    - "Basic onboarding tutorial"
    
  out:
    - "Enterprise onboarding (separate project)"
    - "Billing system changes"
    - "Mobile app"
    
  assumptions:
    - "Engineering capacity available as planned"
    - "Design specs finalized by Phase 1 end"
```

**Rule:** Explicit "out of scope" prevents creep.

### Step 3: Break into Phases

Each phase has clear objective and exit criteria:

```yaml
phases:
  - name: "Phase 1: Foundation"
    objective: "Technical infrastructure ready"
    duration: "4 weeks"
    start_condition: "Project kickoff"
    
    milestones:
      - milestone: "Auth system updated"
        criteria: "Self-serve accounts can be created"
        
      - milestone: "Provisioning API complete"
        criteria: "API creates workspace in <30 seconds"
        
    deliverables:
      - deliverable: "Auth service v2"
        owner: "Backend team"
        
      - deliverable: "Provisioning service"
        owner: "Platform team"
        
  - name: "Phase 2: User Experience"
    objective: "User-facing flows complete"
    duration: "3 weeks"
    start_condition: "Phase 1 milestones met"
    
    milestones:
      - milestone: "Signup flow live"
        criteria: "User can complete signup in <5 minutes"
        
      - milestone: "Onboarding tutorial complete"
        criteria: "80% completion rate in testing"
```

**Rule:** Each phase has objective, duration, and start condition.

### Step 4: Identify Dependencies

What could block progress?

```yaml
dependencies:
  - dependency: "Design specs for signup flow"
    type: internal
    owner: "Design team"
    risk_if_delayed: "Phase 2 blocked, 1-week slip per week delay"
    
  - dependency: "Payment processor API access"
    type: external
    owner: "Partnerships"
    risk_if_delayed: "Cannot enable paid tiers at launch"
```

### Step 5: Assess Risks

What could go wrong in each phase?

```yaml
risks:
  - risk: "Auth migration breaks existing users"
    phase: "Phase 1"
    likelihood: medium
    impact: high
    mitigation: "Feature flag rollout, 10% → 50% → 100%"
    
  - risk: "Onboarding completion rate below target"
    phase: "Phase 2"
    likelihood: medium
    impact: medium
    mitigation: "A/B test variations, iterate before full launch"
```

### Step 6: Define Success Criteria

How do we know we succeeded?

```yaml
success_criteria:
  - criterion: "Self-serve conversion rate"
    measurement: "≥5% of visitors complete signup"
    
  - criterion: "Time to first value"
    measurement: "<10 minutes from signup to core action"
    
  - criterion: "Support ticket volume"
    measurement: "<0.5 tickets per new signup"
```

## Complete Example

```yaml
plan:
  name: "SMB Self-Serve Launch"
  goal: "Enable self-serve onboarding for SMB segment"
  owner: "Product team"
  created: "2024-01-15"
  
  constraints:
    - constraint: "Launch by March 31"
      type: time
    - constraint: "$50K budget"
      type: budget
    - constraint: "2 engineers available"
      type: resource
      
  scope:
    in:
      - "Self-serve signup"
      - "Automated provisioning"
      - "Onboarding tutorial"
    out:
      - "Enterprise onboarding"
      - "Billing changes"
      - "Mobile support"
    assumptions:
      - "Design ready by Phase 1 end"
      - "No major incidents during development"
      
  phases:
    - name: "Phase 1: Foundation"
      objective: "Backend infrastructure"
      duration: "4 weeks (Jan 15 - Feb 12)"
      start_condition: "Kickoff complete"
      
      milestones:
        - milestone: "Self-serve auth enabled"
          criteria: "New accounts creatable via API"
        - milestone: "Provisioning automated"
          criteria: "Workspace created in <30s"
          
      deliverables:
        - deliverable: "Auth service v2"
          owner: "Alice (Backend)"
        - deliverable: "Provisioning service"
          owner: "Bob (Platform)"
          
    - name: "Phase 2: User Experience"
      objective: "Frontend flows"
      duration: "3 weeks (Feb 12 - Mar 5)"
      start_condition: "Phase 1 milestones met"
      
      milestones:
        - milestone: "Signup flow live"
          criteria: "Complete in <5 min"
        - milestone: "Tutorial complete"
          criteria: "80% completion rate"
          
      deliverables:
        - deliverable: "Signup UI"
          owner: "Carol (Frontend)"
        - deliverable: "Tutorial content"
          owner: "Dan (Content)"
          
    - name: "Phase 3: Launch"
      objective: "Production rollout"
      duration: "3 weeks (Mar 5 - Mar 26)"
      start_condition: "Phase 2 milestones met"
      
      milestones:
        - milestone: "Beta launch (10%)"
          criteria: "No critical bugs in 48h"
        - milestone: "Full launch"
          criteria: "Success criteria met"
          
  dependencies:
    - dependency: "Design specs"
      type: internal
      owner: "Design team"
      risk_if_delayed: "Phase 2 blocked"
      
    - dependency: "Payment API"
      type: external
      owner: "Partnerships"
      risk_if_delayed: "Launch without paid tiers"
      
  risks:
    - risk: "Auth migration issues"
      phase: "Phase 1"
      likelihood: medium
      impact: high
      mitigation: "Feature flags, staged rollout"
      
    - risk: "Low completion rate"
      phase: "Phase 2"
      likelihood: medium
      impact: medium
      mitigation: "A/B test, iterate"
      
  success_criteria:
    - criterion: "Conversion rate"
      measurement: "≥5% visitor → signup"
    - criterion: "Time to value"
      measurement: "<10 min to core action"
    - criterion: "Support volume"
      measurement: "<0.5 tickets per signup"
```

## Quality Gates

| Gate | Requirement |
|------|-------------|
| Goal specific | Measurable outcome |
| Phases sequenced | Clear start conditions |
| Milestones measurable | Criteria, not vague |
| Dependencies owned | Someone responsible |
| Risks per phase | Where things go wrong |
| Success defined | Know when done |

## Anti-Patterns

| Avoid | Do Instead |
|-------|------------|
| Single mega-phase | Break into 2-4 week chunks |
| Vague milestones | Measurable criteria |
| Unowned dependencies | Assign responsibility |
| Optimistic estimates | Include buffer, identify risks |
| Missing "out of scope" | Explicit exclusions |
