# Alignment Schema Reference

Surface disagreements and clarify ownership.

## When to Use

- Stakeholders have conflicting interests
- Assumptions differ across parties
- Ownership is unclear
- Hidden disagreements suspected
- Need to get everyone on same page

## Purpose

**Surface conflicts, assign ownership, enable resolution.** Not to resolve conflicts (that's decision or consensus), but to make them visible.

## Structure

### Situation Summary

```yaml
situation:
  context: "Cross-team initiative to launch enterprise feature"
  trigger: "Disagreement emerged in planning meeting"
  scope: "Feature scope, timeline, and ownership"
  urgency: medium
```

### Stakeholder Mapping

```yaml
stakeholders:
  - stakeholder: "Product"
    representative: "Sarah"
    interests:
      - "Ship feature that wins enterprise deals"
      - "Beat competitor to market"
    constraints:
      - "Must have SSO and audit logs"
    influence: high
    
  - stakeholder: "Engineering"
    representative: "Mike"
    interests:
      - "Maintain code quality"
      - "Sustainable pace"
    constraints:
      - "Team at capacity"
    influence: high
    
  - stakeholder: "Sales"
    representative: "Jordan"
    interests:
      - "Close Q1 pipeline"
      - "Feature parity with competitor"
    constraints:
      - "Deals waiting on this"
    influence: medium
```

### Assumption Inventory

```yaml
assumptions:
  explicit:
    - assumption: "Feature needed for enterprise deals"
      held_by: ["Product", "Sales"]
      evidence: "Customer feedback"
      contested: false
      
    - assumption: "3-month timeline is achievable"
      held_by: ["Product"]
      evidence: "Initial estimate"
      contested: true
      contested_by: ["Engineering"]
      
  implicit:
    - assumption: "Engineering can hire to fill capacity"
      held_by: ["Product"]
      evidence: none
      contested: true
      
    - assumption: "Scope is fixed"
      held_by: ["Sales"]
      evidence: "Customer conversations"
      contested: true
```

### Conflict Identification

```yaml
conflicts:
  - conflict: "Timeline vs scope"
    type: resource
    parties: ["Product", "Engineering"]
    description: "Product wants full scope in 3 months; Engineering says 5 months needed"
    
    positions:
      product: "Must ship Q1 for competitive reasons"
      engineering: "Quality will suffer at this pace"
      
    root_cause: "Capacity constraints not factored into planning"
    
  - conflict: "Scope definition"
    type: preference
    parties: ["Sales", "Engineering"]
    description: "Sales wants feature parity; Engineering wants MVP"
    
    positions:
      sales: "Customers expect full feature set"
      engineering: "MVP gets us learning faster"
      
    root_cause: "Different mental models of customer needs"
```

### Conflict Types

| Type | Description | Resolution Approach |
|------|-------------|---------------------|
| **Factual** | Disagreement on facts | Get data, triangulate |
| **Resource** | Competition for limited resources | Prioritization decision |
| **Preference** | Different values/priorities | Negotiation or authority |
| **Process** | How to do something | Agree on method |
| **Ownership** | Who is responsible | Explicit assignment |

### Decisions Needed

```yaml
decisions_needed:
  - decision: "Final scope for v1"
    why: "Resolves scope conflict"
    owner: "Product (Sarah)"
    input_from: ["Engineering", "Sales"]
    deadline: "Friday"
    
  - decision: "Realistic timeline given scope"
    why: "Resolves timeline conflict"
    owner: "Engineering (Mike)"
    input_from: ["Product"]
    deadline: "Monday"
    
  - decision: "Whether to hire contractors"
    why: "Could resolve capacity constraint"
    owner: "Engineering Lead"
    escalate_to: "VP Engineering"
    deadline: "Next week"
```

### Ownership Gaps

```yaml
ownership_gaps:
  - gap: "Who owns customer communication about delay?"
    candidates: ["Product", "Sales"]
    impact: "Customer expectations not managed"
    
  - gap: "Who decides on technical trade-offs?"
    candidates: ["Engineering", "Product"]
    impact: "Decisions made ad-hoc"
```

## Process

### 1. Map Stakeholders
Identify everyone with a stake. List their interests and constraints.

### 2. Surface Assumptions
Explicitly list what each party assumes. Flag implicit assumptions.

### 3. Identify Conflicts
Where do interests or assumptions clash? Classify by type.

### 4. Document Decisions Needed
What must be decided to resolve conflicts? Who decides?

### 5. Flag Ownership Gaps
Where is accountability unclear?

## Quality Gates

| Gate | Requirement |
|------|-------------|
| Stakeholders complete | No missing parties |
| Interests explicit | Each stakeholder's interests documented |
| Assumptions attributed | Clear who holds each assumption |
| Conflicts classified | Type identified for each |
| Decisions assigned | Owner for each needed decision |
| Gaps flagged | Ownership gaps visible |

## Anti-Patterns

| Avoid | Do Instead |
|-------|------------|
| Resolving conflicts immediately | Surface first, resolve separately |
| Hiding disagreement | Make conflicts visible |
| Assuming alignment | Check assumptions explicitly |
| Vague ownership | Specific person for each decision |
| Only explicit conflicts | Surface implicit assumptions too |

## Output Schema

```yaml
alignment:
  situation: string
  
  stakeholders:
    - stakeholder: string
      interests: [string]
      constraints: [string]
      
  assumptions:
    explicit:
      - assumption: string
        held_by: [string]
        contested: bool
    implicit:
      - assumption: string
        held_by: [string]
        
  conflicts:
    - conflict: string
      type: factual | resource | preference | process | ownership
      parties: [string]
      positions: {string: string}
      root_cause: string
      
  decisions_needed:
    - decision: string
      owner: string
      deadline: string
      
  ownership_gaps:
    - gap: string
      candidates: [string]
      impact: string
```

## Example Output

```yaml
alignment:
  situation: "Enterprise feature launch planning misalignment"
  
  stakeholders:
    - stakeholder: "Product"
      interests: ["Ship Q1", "Beat competitor"]
    - stakeholder: "Engineering"  
      interests: ["Code quality", "Sustainable pace"]
    - stakeholder: "Sales"
      interests: ["Close pipeline", "Feature parity"]
      
  conflicts:
    - conflict: "Timeline vs scope"
      type: resource
      parties: ["Product", "Engineering"]
      root_cause: "Capacity not factored in"
      
  decisions_needed:
    - decision: "Final scope for v1"
      owner: "Product (Sarah)"
      deadline: "Friday"
      
  ownership_gaps:
    - gap: "Customer communication about timeline"
      candidates: ["Product", "Sales"]
```
