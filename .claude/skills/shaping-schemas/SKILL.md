---
name: shaping-schemas
description: Formats outputs into rigorous deliverable structures. Selects schema based on deliverable intent—procedural (SOPs), validation (success criteria), planning (roadmaps), decision (recommendations), evaluative (assessments), diagnostic (root cause), risk (threats), constraint (guardrails), alignment (stakeholder conflicts), prescriptive (guidance), or descriptive (summaries). Composes with thinking-modes (thinking = how to reason, shaping = what to output). Triggers on "decide", "plan", "diagnose", "evaluate", "recommend", "SOP", "checklist".
---

# Shaping Schemas

Select output schema. Produce deliverable matching structure.

## Relationship to Thinking

**thinking-modes** = cognitive process (HOW to reason)
**shaping-schemas** = output format (WHAT to deliver)

They compose orthogonally:

```
thinking-modes.mode × shaping-schemas.schema → output
```

| Task | Thinking Mode | Shaping Schema | Output |
|------|---------------|----------------|--------|
| "Why did this fail?" | abductive | diagnostic | Root cause report |
| "Decide between X and Y" | dialectical | decision | Decision document |
| "Plan the rollout" | causal | planning | Phased plan |
| "What should we do?" | any | prescriptive | Recommendations |

**Rule:** Apply thinking first (if needed), then shape the output.

## Schema Selection (First Match)

| Priority | Schema | Trigger |
|----------|--------|---------|
| 1 | procedural | Runbook, SOP, checklist, playbook |
| 2 | validation | Verify, test plan, "how do we know" |
| 3 | planning | Roadmap, phases, timeline, rollout |
| 4 | decision | Choose, pick, prioritize, go/no-go |
| 5 | evaluative | Review, assess, score, audit |
| 6 | diagnostic | Why did X happen, root cause, debug |
| 7 | risk | Risks, threats, what could go wrong |
| 8 | constraint | Requirements, must/must not, limits |
| 9 | alignment | Stakeholder conflict, unclear ownership |
| 10 | prescriptive | Recommendations, what should I do |
| 11 | descriptive | Summarize, explain, compare (default) |

## Composite Chains

When prompt contains multiple intents, chain schemas:

| Pattern | Chain |
|---------|-------|
| Analyze and recommend | descriptive → prescriptive |
| Why and what to do | diagnostic → prescriptive |
| Compare and pick | evaluative → decision |
| Pick and plan | decision → planning |
| Plan and verify | planning → validation |
| Launch safely | constraint → risk → planning → validation |

## Schema Specifications

### procedural

**Purpose:** Repeatable, deterministic process.

```yaml
procedure:
  name: string
  purpose: string
  triggers: [string]
  
  prerequisites:
    - item: string
      required: bool
      
  steps:
    - number: int
      action: string
      expected_outcome: string
      
  decision_points:
    - at_step: int
      condition: string
      if_true: string
      if_false: string
      
  escalation:
    - condition: string
      escalate_to: string
      
  rollback:
    - trigger: string
      actions: [string]
```

**Gates:** Steps numbered, outcomes defined, rollback included.

---

### validation

**Purpose:** Define how success will be verified.

```yaml
validation:
  target: string
  
  success_criteria:
    - criterion: string
      metric: string
      threshold: string
      
  validation_methods:
    - method: string
      covers_criteria: [string]
      
  failure_conditions:
    - condition: string
      response: string
      
  rollback_triggers:
    - trigger: string
      action: string
```

**Gates:** Criteria measurable, failure conditions explicit.

---

### planning

**Purpose:** Translate goal into phased execution.

```yaml
plan:
  goal: string
  constraints: [string]
  
  scope:
    in: [string]
    out: [string]
    
  phases:
    - name: string
      duration: string
      milestones:
        - milestone: string
          criteria: string
          
  dependencies:
    - dependency: string
      owner: string
      
  risks:
    - risk: string
      likelihood: low | medium | high
      mitigation: string
```

**Gates:** Phases sequenced, milestones measurable, dependencies owned.

---

### decision

**Purpose:** Select one option with trade-off justification.

```yaml
decision:
  statement: string
  
  options:
    - name: string
      pros: [string]
      cons: [string]
      
  criteria:
    - criterion: string
      weight: float
      
  recommendation: string    # Exactly ONE
  rationale: string
  
  trade_offs:
    - trade_off: string
      accepted_because: string
      
  revisit_triggers:
    - condition: string
```

**Gates:** Single recommendation (not "it depends"), risks documented.

---

### evaluative

**Purpose:** Assess against criteria.

```yaml
evaluation:
  target: string
  
  assessment:
    - criterion: string
      result: pass | partial | fail
      evidence: string
      
  overall:
    verdict: pass | conditional | fail
    confidence: float
    
  gaps:
    - gap: string
      severity: blocking | significant | minor
```

**Gates:** Evidence cited, no recommendations (evaluative ≠ prescriptive).

---

### diagnostic

**Purpose:** Explain why a problem occurred.

```yaml
diagnostic:
  symptoms:
    - symptom: string
      observed: string
      expected: string
      
  hypotheses:
    - cause: string
      mechanism: string
      evidence_for: [string]
      evidence_against: [string]
      confidence: float
      
  conclusion:
    primary_cause: string
    confidence: float
    contributing_factors: [string]
    
  data_gaps:
    - gap: string
      would_clarify: string
```

**Gates:** Multiple hypotheses, evidence both for AND against, no fixes (diagnostic ≠ prescriptive).

**Requires:** thinking-modes.abductive

---

### risk

**Purpose:** Identify and prioritize threats.

```yaml
risk:
  scope: string
  
  risk_register:
    - risk: string
      category: string
      likelihood: low | medium | high
      impact: low | medium | high
      
  top_risks:
    - risk_id: string
      rationale: string
      
  mitigation_themes:
    - theme: string
      approach: string
```

**Gates:** Multiple categories, likelihood AND impact scored.

---

### constraint

**Purpose:** Make limits explicit.

```yaml
constraints:
  hard_constraints:
    - constraint: string
      source: string
      violation_consequence: string
      
  soft_constraints:
    - constraint: string
      trade_conditions: string
      
  unknowns:
    - constraint: string
      question: string
      
  guardrails:
    - rule: string
      enforces: string
      
  conflicts:
    - conflict: string
      requires_decision: bool
```

**Gates:** Hard vs soft classified, conflicts surfaced not resolved.

---

### alignment

**Purpose:** Surface disagreements and ownership.

```yaml
alignment:
  situation: string
  
  stakeholders:
    - stakeholder: string
      interests: [string]
      
  assumptions:
    - assumption: string
      held_by: string
      explicit: bool
      
  conflicts:
    - conflict: string
      type: factual | preference
      parties: [string]
      
  decisions_needed:
    - decision: string
      owner: string
      
  ownership_gaps:
    - gap: string
```

**Gates:** Assumptions attributed, ownership assigned or flagged.

---

### prescriptive

**Purpose:** Actionable guidance.

```yaml
prescriptive:
  objective: string
  
  recommendation:
    primary: string
    rationale: string
    
  alternatives:
    - alternative: string
      when_preferred: string
      
  trade_offs:
    - trade_off: string
      
  immediate_actions:
    - action: string
      owner: optional<string>
```

**Gates:** Clear primary recommendation, trade-offs explicit.

---

### descriptive

**Purpose:** Neutral summary (default schema).

```yaml
descriptive:
  scope: string
  summary: string
  
  details:
    - section: string
      content: [string]
      
  evidence:
    - claim: string
      source: string
      
  open_questions: [string]
```

**Gates:** No recommendations, facts separated from interpretation.

## Thinking Mode Pairings

| Schema | Common Thinking Mode |
|--------|---------------------|
| diagnostic | abductive (required) |
| decision | dialectical |
| planning | causal |
| alignment | dialectical |
| evaluative | inductive |
| validation | inductive |
| risk | abductive + inductive |

## Output Rules

1. Complete each schema fully before chaining
2. Section by schema when chaining
3. Match structure exactly
4. State thinking mode if applied

## References

- [references/procedural.md](references/procedural.md) — SOP patterns
- [references/validation.md](references/validation.md) — Success criteria design
- [references/planning.md](references/planning.md) — Phase decomposition
- [references/decision.md](references/decision.md) — Option evaluation
- [references/diagnostic.md](references/diagnostic.md) — Root cause structure
- [references/risk.md](references/risk.md) — Threat identification
