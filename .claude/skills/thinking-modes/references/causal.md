# Causal Mode Reference

Execute systematic cause-effect reasoning through 6 stages.

## When to Use

Use causal mode when:
- Executing a known process or workflow
- Making operational decisions with clear steps
- Following goal-linked execution threads
- The question is "How do we execute this?"

## Required Personas

| Persona | Role | Traits |
|---------|------|--------|
| **Executor** | Drives stages forward | E:2, A:4, C:5, N:2, O:3 |
| **Validator** | Checks each stage | E:2, A:3, C:5, N:5, O:3 |

## Execution Flow

```
Stage 1: Input
    ↓
Stage 2: Hypothesis
    ↓
Stage 3: Implication
    ↓
Stage 4: Decision
    ↓
Stage 5: Actions
    ↓
Stage 6: Learning
```

## Stage Instructions

### Stage 1: Input

**Executor does:**
1. State the factual observation that triggers reasoning
2. List evidence with sources and confidence scores
3. Provide context: when, where, who observed
4. State prior belief before this observation

**Validator checks:**
- "Wait, is this fact or interpretation?"
- "Let me verify the evidence source..."
- "What was actually observed vs inferred?"

**Output:**
```yaml
input:
  observation: "[Factual statement]"
  evidence:
    - claim: "[Data point]"
      source: "[Source]"
      confidence: 0.0-1.0
  context:
    when: "[Timestamp]"
    where: "[Location/system]"
    observed_by: "[Observer]"
  prior_belief: "[What we believed before]"
```

**Gate:** Validator must confirm all claims are evidence-backed facts before proceeding.

---

### Stage 2: Hypothesis

**Executor does:**
1. Form testable hypothesis connecting observation to cause
2. State which assumption is being tested
3. Define falsification criteria
4. Propose test method

**Validator checks:**
- "Wait, is this falsifiable?"
- "What would prove this wrong?"
- "Can we actually test this?"

**Output:**
```yaml
hypothesis:
  assumption_tested: "[Which belief this challenges]"
  statement: "If [condition], then [prediction], because [mechanism]"
  falsification:
    - "[What would disprove this]"
  test:
    method: "[How to test]"
    duration: "[Time required]"
    success_metric: "[Threshold]"
```

**Gate:** Validator must confirm hypothesis is falsifiable before proceeding.

---

### Stage 3: Implication

**Executor does:**
1. Model at least 3 scenarios with probabilities
2. Quantify impact with specific numbers
3. Identify resource requirements
4. List risks with mitigations
5. State opportunity costs

**Validator checks:**
- "Wait, are these numbers justified?"
- "What about the scenario where [X]?"
- "Let me check the risk you might have missed..."

**Output:**
```yaml
implication:
  scenarios:
    - name: "Hypothesis true"
      probability: 0.0-1.0
      impact: "[Quantified]"
      timeline: "[Duration]"
    - name: "Hypothesis false"
      probability: 0.0-1.0
      impact: "[Quantified]"
      timeline: "[Duration]"
    - name: "Do nothing"
      probability: 1.0
      impact: "[Quantified]"
      timeline: "[Duration]"
  resources:
    effort: "[Time/people]"
    cost: "[Financial]"
    dependencies: "[What must be true]"
  risks:
    - risk: "[What could go wrong]"
      probability: high | medium | low
      impact: high | medium | low
      mitigation: "[How to reduce]"
  opportunity_cost:
    - "[What we cannot do if we pursue this]"
```

**Gate:** Validator must confirm all impacts have specific numbers before proceeding.

---

### Stage 4: Decision

**Executor does:**
1. State explicit commitment: PROCEED, DEFER, or DECLINE
2. List alternatives considered and why rejected
3. Document criteria used with weights
4. State conditions under which decision changes

**Validator checks:**
- "Wait, did we consider [alternative]?"
- "What if [condition] changes?"
- "Is this actually reversible?"

**Output:**
```yaml
decision:
  commitment: PROCEED | DEFER | DECLINE
  alternatives:
    - option: "[Alternative]"
      rejected_because: "[Reason]"
  criteria:
    - criterion: "[Factor]"
      weight: 0.0-1.0
      score: 0.0-1.0
  conditions:
    - "[When decision would change]"
  rationale: "[Why this decision]"
```

**Gate:** Decision must be explicit (not "probably" or "maybe").

---

### Stage 5: Actions

**Executor does:**
1. Define specific tasks with owners
2. Set deadlines for each task
3. Define success criteria for each task
4. Establish execution order with dependencies
5. Set validation checkpoints

**Validator checks:**
- "Wait, who owns this task?"
- "How do we know this is done?"
- "What's blocking this?"

**Output:**
```yaml
actions:
  tasks:
    - id: "ACTION-1"
      description: "[What to do]"
      owner: "[Who]"
      deadline: "[When]"
      dependencies: []
      success_criteria: "[How we know it's done]"
  execution_order:
    - "ACTION-1 (no dependencies)"
    - "ACTION-2 (after ACTION-1)"
  checkpoints:
    - after: "ACTION-1"
      validate: "[What to check]"
```

**Gate:** Every task must have owner, deadline, and success criteria.

---

### Stage 6: Learning

**Executor does:**
1. Compare expected vs actual outcome
2. State hypothesis validation status
3. Update beliefs based on evidence
4. Identify follow-on questions and actions

**Validator checks:**
- "Wait, are we learning the right lesson?"
- "What else could explain this outcome?"
- "Are we updating beliefs appropriately?"

**Output:**
```yaml
learning:
  outcome:
    expected: "[Prediction]"
    actual: "[What happened]"
    delta: "[Difference]"
  hypothesis_result:
    status: VALIDATED | INVALIDATED | INCONCLUSIVE
    evidence: "[What proved/disproved]"
  belief_updates:
    - assumption: "[Belief affected]"
      previous: "[Old status]"
      updated: "[New status]"
      evidence: "[What caused update]"
  follow_on:
    questions: ["[New questions]"]
    actions: ["[Next work]"]
```

**Gate:** Must compare expected vs actual even when successful.

## Conversation Example

```xml
<personas>
  <executor traits="E:2,A:4,C:5,N:2,O:3">
    Methodical, systematic, drives execution forward
  </executor>
  <validator traits="E:2,A:3,C:5,N:5,O:3">
    Thorough, risk-aware, checks everything
  </validator>
</personas>

<think_executor>
  Stage 1 - Input:
  Observation: Conversion dropped from 12% to 7% in Q4.
  Evidence: Analytics dashboard (confidence 0.95).
  Prior belief: Conversion was stable.
</think_executor>

<think_validator>
  Wait, is 7% the current rate or an average? Let me check...
  Confirmed: 7% is Q4 average, drop started week 3.
  The evidence is solid. Proceed to hypothesis.
</think_validator>

<think_executor>
  Stage 2 - Hypothesis:
  If page load time increased, then conversion dropped,
  because users abandon slow pages.
  Falsification: Load time unchanged would disprove this.
</think_executor>

<think_validator>
  Hmm, what if mobile and desktop dropped equally?
  That would suggest it's not performance-related.
  Add that to falsification criteria.
</think_validator>

<think_executor>
  Good point. Adding: "If mobile and desktop dropped equally,
  performance is less likely the cause."
  Proceeding to Stage 3...
</think_executor>
```

## Quality Gates Summary

| Stage | Gate |
|-------|------|
| Input | All claims evidence-backed |
| Hypothesis | Falsifiable with test |
| Implication | Quantified with numbers |
| Decision | Explicit PROCEED/DEFER/DECLINE |
| Actions | Owner + deadline + criteria for each |
| Learning | Expected vs actual compared |

## Anti-Patterns

| Avoid | Do Instead |
|-------|------------|
| Jumping to Stage 5 | Complete all stages in order |
| Vague hypothesis | Require falsification criteria |
| "Significant impact" | Require specific numbers |
| "We should probably..." | Force explicit commitment |
| Tasks without owners | Require ownership assignment |
| Skipping Stage 6 | Always extract learning |
