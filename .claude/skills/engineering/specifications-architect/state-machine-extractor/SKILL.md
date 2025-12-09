---
name: state-machine-extractor
description: Extract lifecycle state machines as finite categories. Use for entities with lifecycle:true to define states, transitions, guards, and actions. Outputs state-machines.yaml defining finite categories where objects are states and morphisms are transitions.
---

# State Machine Extractor

Extract state machines from entities with lifecycle behavior. States become objects, transitions become morphisms, forming a finite category.

## Input

Requires:
- `artifacts/engineering/v{X}/specifications/domain-concepts.yaml` (entities with lifecycle: true)
- `artifacts/engineering/v{X}/specifications/requirements.adt` (status coproducts)
- `artifacts/engineering/v{X}/specifications/services.spec.yaml` (resilience patterns with state)

## Output

Generate `artifacts/engineering/v{X}/specifications/state-machines.yaml`:

```yaml
version: "1.0"
sources:
  - domain-concepts.yaml
  - requirements.adt
  - services.spec.yaml

state_machines:
  - name: MachineName
    entity: EntityName
    description: "What this state machine represents"
    
    # Categorical structure
    category:
      objects: [State1, State2, State3]
      initial: State1
      terminal: [State3]  # Can have multiple
    
    states:
      - name: StateName
        description: "What this state means"
        type: initial | intermediate | terminal
        invariants:
          - "What must be true in this state"
        data:
          - field: field_name
            type: TypeReference
            required: true
    
    transitions:
      - name: transition_name
        from: SourceState
        to: TargetState
        
        # Guard (pre-condition for transition)
        guard:
          condition: "When transition is allowed"
          formal: "P(entity)"
        
        # Action (side effect on transition)
        action:
          description: "What happens during transition"
          morphism: operation_name  # Reference to services.spec
        
        # Trigger
        trigger:
          type: command | event | timeout | condition
          source: "What causes this transition"
    
    # Composition with identity
    identity:
      per_state: true  # id_S: S → S for each state
    
    # Paths through the machine
    paths:
      - name: happy_path
        sequence: [State1, State2, State3]
        probability: 0.9
      - name: error_path
        sequence: [State1, State2, ErrorState]
        probability: 0.1
```

## Extraction from Entities

### Identify Lifecycle Entities

```yaml
# From domain-concepts.yaml
entities:
  - name: Analysis
    lifecycle: true
    attributes:
      - name: status
        type: AnalysisStatus

# Extract state machine
state_machines:
  - name: AnalysisLifecycle
    entity: Analysis
```

### Extract States from Status

```yaml
# From requirements.adt
coproducts:
  - name: AnalysisStatus
    variants:
      - name: Pending
      - name: Processing
      - name: Completed
      - name: Failed

# To state-machines.yaml
state_machines:
  - name: AnalysisLifecycle
    category:
      objects: [Pending, Processing, Completed, Failed]
      initial: Pending
      terminal: [Completed, Failed]
    
    states:
      - name: Pending
        type: initial
        description: "Analysis requested, waiting to start"
        invariants:
          - "No processing has begun"
        
      - name: Processing
        type: intermediate
        description: "AI analysis in progress"
        invariants:
          - "Photo has been submitted"
          - "AI service is working"
        data:
          - field: started_at
            type: Timestamp
            required: true
        
      - name: Completed
        type: terminal
        description: "Analysis finished successfully"
        invariants:
          - "Results are available"
        data:
          - field: result
            type: AnalysisResult
            required: true
          - field: completed_at
            type: Timestamp
            required: true
        
      - name: Failed
        type: terminal
        description: "Analysis could not complete"
        data:
          - field: error
            type: AnalysisError
            required: true
          - field: failed_at
            type: Timestamp
            required: true
```

### Define Transitions

```yaml
transitions:
  # Start processing
  - name: start_processing
    from: Pending
    to: Processing
    guard:
      condition: "Photo is available"
      formal: "HasPhoto(analysis)"
    action:
      description: "Begin AI analysis"
      morphism: process_analysis
    trigger:
      type: event
      source: "Worker picks up job"

  # Complete successfully
  - name: complete
    from: Processing
    to: Completed
    guard:
      condition: "Analysis succeeded"
      formal: "IsSuccess(result)"
    action:
      description: "Store results"
      morphism: save_analysis_result
    trigger:
      type: event
      source: "AI returns result"

  # Fail
  - name: fail
    from: Processing
    to: Failed
    guard:
      condition: "Analysis failed"
      formal: "IsFailure(result)"
    action:
      description: "Record failure"
      morphism: record_failure
    trigger:
      type: event
      source: "AI returns error or timeout"
```

## Circuit Breaker State Machine

Extract from resilience patterns:

```yaml
state_machines:
  - name: CircuitBreakerState
    entity: CircuitBreaker
    description: "Circuit breaker for external dependency"
    
    category:
      objects: [Closed, Open, HalfOpen]
      initial: Closed
      terminal: []  # No terminal state - always running
    
    states:
      - name: Closed
        type: initial
        description: "Normal operation, counting failures"
        data:
          - field: failure_count
            type: NonNegativeInt
          - field: success_count
            type: NonNegativeInt
        
      - name: Open
        type: intermediate
        description: "Failing fast, not calling dependency"
        data:
          - field: opened_at
            type: Timestamp
        
      - name: HalfOpen
        type: intermediate
        description: "Testing if dependency recovered"
        data:
          - field: test_count
            type: NonNegativeInt
    
    transitions:
      - name: trip
        from: Closed
        to: Open
        guard:
          condition: "Failure threshold exceeded"
          formal: "failure_count >= failure_threshold"
        action:
          description: "Record open time"
          morphism: record_circuit_open
        trigger:
          type: condition
          source: "Failure count check"

      - name: timeout
        from: Open
        to: HalfOpen
        guard:
          condition: "Timeout elapsed"
          formal: "now - opened_at >= half_open_timeout"
        trigger:
          type: timeout
          source: "Timer expiration"

      - name: test_success
        from: HalfOpen
        to: Closed
        guard:
          condition: "Enough successful tests"
          formal: "success_count >= success_threshold"
        action:
          description: "Reset counters"
          morphism: reset_circuit_breaker
        trigger:
          type: event
          source: "Successful call"

      - name: test_failure
        from: HalfOpen
        to: Open
        guard:
          condition: "Any test failed"
          formal: "true"
        action:
          description: "Record failure"
          morphism: record_circuit_open
        trigger:
          type: event
          source: "Failed call"

      - name: record_failure
        from: Closed
        to: Closed
        guard:
          condition: "Below threshold"
          formal: "failure_count < failure_threshold"
        action:
          description: "Increment failure count"
          morphism: increment_failure
        trigger:
          type: event
          source: "Failed call"

      - name: record_success
        from: Closed
        to: Closed
        guard:
          condition: "Always"
          formal: "true"
        action:
          description: "Reset failure count"
          morphism: reset_failure_count
        trigger:
          type: event
          source: "Successful call"
```

## Categorical Properties

### Finite Category

State machine forms a finite category:

```yaml
category:
  name: AnalysisLifecycle
  
  # Finite set of objects
  objects: [Pending, Processing, Completed, Failed]
  
  # Morphisms are transitions + identities
  morphisms:
    - id_Pending: Pending → Pending
    - id_Processing: Processing → Processing
    - id_Completed: Completed → Completed
    - id_Failed: Failed → Failed
    - start_processing: Pending → Processing
    - complete: Processing → Completed
    - fail: Processing → Failed
  
  # Composition
  composition:
    - complete ∘ start_processing: Pending → Completed
    - fail ∘ start_processing: Pending → Failed
  
  # Laws
  laws:
    identity: "id ∘ f = f = f ∘ id"
    associativity: "h ∘ (g ∘ f) = (h ∘ g) ∘ f"
```

### Path Composition

```yaml
paths:
  - name: success_path
    morphisms: [start_processing, complete]
    composed: "success: Pending → Completed"
    
  - name: failure_path
    morphisms: [start_processing, fail]
    composed: "failure: Pending → Failed"
```

## Validation Checklist

Before outputting, verify:

- [ ] Every lifecycle entity has a state machine
- [ ] Initial state exists and is unique
- [ ] Terminal states are reachable from initial
- [ ] All states are reachable from initial
- [ ] No orphan states (unreachable)
- [ ] Transitions reference valid states
- [ ] Guards are consistent (no contradictions)
- [ ] Actions reference valid morphisms

## State Machine Laws

**Determinism** (optional):
```
For each state S and trigger T, at most one transition applies
```

**Reachability**:
```
∀s ∈ States. ∃path: Initial → s
```

**Termination** (for workflows):
```
∀s ∈ States. ∃path: s → Terminal
```

**No deadlocks**:
```
∀s ∈ NonTerminal. ∃t: s → _
```

## Next Skill

Output feeds into:
- **categorical-structure-detector** → state machines are finite categories
- **proof-obligation-generator** → transition guards become proofs
