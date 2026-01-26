# Risk Mode

Identify and prioritize threats.

## Trigger Phrases

"what could go wrong", "risks", "threats", "vulnerabilities", "failure modes"

## When to Use

- Planning a launch or initiative
- Assessing a decision's downside
- Preparing contingency plans
- Due diligence

## Execution Instructions

### Step 1: Define Scope and Horizon

State clearly:
- What we're assessing risk for
- Time horizon being considered

**Format:**
```yaml
scope: "Q2 product launch"
horizon: "90 days"
date: "2024-01-15"
```

### Step 2: Generate Risk Register

Enumerate risks across multiple categories:

**Required categories:**
- Technical: System failures, bugs, performance
- Operational: Process, team, execution
- Market: Competition, demand, timing
- Financial: Budget, revenue, costs
- Legal/Compliance: Regulations, contracts
- External: Economy, events, dependencies

**For each risk, capture:**
```yaml
risk_register:
  - id: R1
    risk: "[What could go wrong]"
    category: technical | operational | market | financial | legal | external
    likelihood: low | medium | high
    impact: low | medium | high
    score: float  # likelihood_score × impact_score
    owner: optional<string>
    detection: "[How we'd know if it's happening]"
```

**Scoring:**
| Level | Score |
|-------|-------|
| Low | 0.2 |
| Medium | 0.5 |
| High | 0.9 |

**Score = likelihood × impact** (range 0.04 to 0.81)

### Step 3: Prioritize Top Risks

Identify the critical few (typically 3-5):
- Highest score
- Or blocking (regardless of score)
- Or novel/unfamiliar

**Format:**
```yaml
top_risks:
  - risk_id: R1
    rank: 1
    rationale: "Highest impact, moderate likelihood"
    
  - risk_id: R3
    rank: 2
    rationale: "Novel risk, limited experience managing"
```

### Step 4: Identify Mitigation Themes

Group mitigations into themes (not detailed plans):

**Format:**
```yaml
mitigation_themes:
  - theme: "Redundancy"
    addresses: [R1, R4]
    approach: "Add backup systems and failover"
    
  - theme: "Early warning"
    addresses: [R2, R3, R5]
    approach: "Monitoring and alerting before threshold"
    
  - theme: "Contractual protection"
    addresses: [R6]
    approach: "SLA terms and exit clauses"
```

### Step 5: Note Open Questions

What risks might we be missing?

**Format:**
```yaml
open_questions:
  - "Do we have blind spots in [area]?"
  - "What risks emerged in similar past projects?"
  - "What would a competitor do to disrupt us?"
```

## Output Schema

```yaml
risk:
  scope: string
  horizon: string
  date: date
  
  risk_register:
    - id: string
      risk: string
      category: string
      likelihood: low | medium | high
      impact: low | medium | high
      score: float
      owner: optional<string>
      detection: string
      
  top_risks:
    - risk_id: string
      rank: int
      rationale: string
      
  mitigation_themes:
    - theme: string
      addresses: [string]
      approach: string
      
  open_questions: [string]
```

## Quality Gates

| Gate | Requirement |
|------|-------------|
| Multiple categories | ≥3 categories covered |
| Likelihood AND impact | Both scored |
| Top risks explicit | 3-5 prioritized |
| Detection defined | How we'd know |

## Anti-Patterns

| Avoid | Do Instead |
|-------|------------|
| Single category | Cover multiple categories |
| Only high-impact | Include low-probability/high-impact |
| Detailed mitigation plans | Theme-level approaches |
| "Risk: things go wrong" | Specific, testable risks |

## Boundary

Risk schema **identifies and prioritizes threats**. It does not:
- Create detailed mitigation plans (use planning)
- Make go/no-go decisions (use decision)
- Assign probability to outcomes (use counterfactual)

If user asks "what are risks AND what should we do", chain: risk → prescriptive
