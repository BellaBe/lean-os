# Constraint Mode

Make limits explicit.

## Trigger Phrases

"requirements", "must not", "limitations", "boundaries", "guardrails", "constraints"

## When to Use

- Scoping a project
- Defining requirements
- Establishing boundaries
- Clarifying what's negotiable vs fixed

## Execution Instructions

### Step 1: Classify Constraints

Separate hard from soft:

**Hard constraints:** Cannot be violated. Breaking them means failure.
**Soft constraints:** Preferred but negotiable under conditions.

**For each constraint, document:**
```yaml
hard_constraints:
  - constraint: "[The limit]"
    source: "[Where this comes from]"
    violation_consequence: "[What happens if violated]"
    verification: "[How to check compliance]"
```

```yaml
soft_constraints:
  - constraint: "[The preference]"
    source: "[Where this comes from]"
    trade_conditions: "[When we'd trade this off]"
```

### Step 2: Identify Unknowns

Constraints we suspect but can't confirm:

**Format:**
```yaml
unknowns:
  - constraint: "[Suspected limit]"
    question: "[What we need to clarify]"
    owner: "[Who can answer]"
    deadline: "[When we need to know]"
```

### Step 3: Define Guardrails

Translate constraints into actionable rules:

**Format:**
```yaml
guardrails:
  - rule: "[Specific actionable rule]"
    enforces: "[Which constraint]"
    check: "[How to verify]"
```

**Example:**
```yaml
guardrails:
  - rule: "All data at rest must use AES-256 encryption"
    enforces: "HIPAA PHI protection requirement"
    check: "Database encryption audit"
    
  - rule: "No deployment on Fridays after 2pm"
    enforces: "Support coverage requirement"
    check: "CI/CD pipeline calendar check"
```

### Step 4: Surface Conflicts

Constraints that conflict with each other:

**Format:**
```yaml
conflicts:
  - conflict: "[Description of incompatibility]"
    constraints_involved: [C1, C2]
    requires_decision: true | false
    proposed_resolution: optional<string>
```

**Example:**
```yaml
conflicts:
  - conflict: "Budget limit vs feature scope"
    constraints_involved: 
      - "Budget: $100K maximum"
      - "Scope: All 5 features required"
    requires_decision: true
    proposed_resolution: "Reduce scope to 3 features or increase budget"
```

## Output Schema

```yaml
constraints:
  context: string
  date: date
  
  hard_constraints:
    - constraint: string
      source: string
      violation_consequence: string
      verification: string
      
  soft_constraints:
    - constraint: string
      source: string
      trade_conditions: string
      
  unknowns:
    - constraint: string
      question: string
      owner: string
      deadline: optional<string>
      
  guardrails:
    - rule: string
      enforces: string
      check: string
      
  conflicts:
    - conflict: string
      constraints_involved: [string]
      requires_decision: bool
      proposed_resolution: optional<string>
```

## Quality Gates

| Gate | Requirement |
|------|-------------|
| Hard vs soft | Every constraint classified |
| Source cited | Know where each comes from |
| Violations defined | Consequences explicit |
| Conflicts surfaced | Incompatibilities identified |

## Anti-Patterns

| Avoid | Do Instead |
|-------|------------|
| Mixing hard and soft | Separate clearly |
| No source | Always cite where constraint comes from |
| Hidden conflicts | Surface and flag for decision |
| Vague guardrails | Specific, checkable rules |

## Boundary

Constraint schema **makes limits explicit**. It does not:
- Resolve conflicts (use decision)
- Plan within constraints (use planning)
- Evaluate compliance (use evaluative)

If user asks "what are constraints AND which to prioritize", chain: constraint → decision
