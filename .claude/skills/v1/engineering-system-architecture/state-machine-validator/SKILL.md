---
name: state-machine-validator
description: Extract state machines from ADT annotations, validate reachability (all states reachable), determinism (no ambiguous transitions), and completeness (all paths defined). Generates state machine specifications with proofs.
allowed-tools: Read, Write, Bash
version: 1.0.0
---

# State Machine Validator

## Purpose

Extract state machines from ADT with state annotations, validate correctness (reachability, determinism, completeness), and generate formal state machine specifications.

## Input

```
artifacts/engineering/specifications/v{VERSION}/requirements.adt (with state annotations)
```

## Output

```
artifacts/engineering/specifications/v{VERSION}/state-machines.yaml
artifacts/engineering/proofs/architecture/state-machine-proofs/
```

## State Machine Properties

### Property 1: Reachability
**Rule:** All states must be reachable from initial state

**Validation:**
```python
def validate_reachability(state_machine):
    initial = state_machine.initial_state
    reachable = compute_reachable_states(initial)
    all_states = state_machine.states
    
    unreachable = all_states - reachable
    assert len(unreachable) == 0, f"Unreachable states: {unreachable}"
```

### Property 2: Determinism
**Rule:** For any state + event, at most one transition

**Validation:**
```python
def validate_determinism(state_machine):
    for state in state_machine.states:
        for event in state_machine.events:
            transitions = find_transitions(state, event)
            assert len(transitions) <= 1, f"Ambiguous: {state} + {event}"
```

### Property 3: Completeness
**Rule:** All possible event + state combinations handled

**Validation:**
```python
def validate_completeness(state_machine):
    for state in state_machine.states:
        for event in state_machine.events:
            transitions = find_transitions(state, event)
            assert len(transitions) > 0, f"Undefined: {state} + {event}"
```

## Execution Steps

### Step 1: Extract State Annotations

```bash
python {baseDir}/scripts/extract_state_machines.py \
  --adt artifacts/engineering/specifications/v{VERSION}/requirements.adt \
  --output /tmp/extracted-state-machines.json
```

### Step 2: Validate Properties

```bash
python {baseDir}/scripts/validate_state_machines.py \
  --machines /tmp/extracted-state-machines.json \
  --checks reachability,determinism,completeness \
  --output artifacts/engineering/proofs/architecture/state-machine-proofs/validation.json
```

### Step 3: Generate State Machine Specs

```bash
python {baseDir}/scripts/generate_state_machine_specs.py \
  --machines /tmp/extracted-state-machines.json \
  --validation artifacts/engineering/proofs/architecture/state-machine-proofs/validation.json \
  --output artifacts/engineering/specifications/v{VERSION}/state-machines.yaml
```

## Example: Payment Flow

### Input (ADT with State Annotations)
```yaml
type: PaymentFlow
states:
  - pending (initial)
  - authorized
  - captured
  - settled (terminal)
  - failed (terminal)

transitions:
  - from: pending
    to: authorized
    event: authorize_payment
    guard: payment_method_valid
  
  - from: authorized
    to: captured
    event: capture_funds
    guard: funds_reserved
  
  - from: captured
    to: settled
    event: settlement_complete
  
  - from: pending
    to: failed
    event: authorization_failed
  
  - from: authorized
    to: failed
    event: capture_failed
```

### Validation Results
```json
{
  "state_machine": "PaymentFlow",
  "validation": {
    "reachability": {
      "initial": "pending",
      "reachable": ["pending", "authorized", "captured", "settled", "failed"],
      "unreachable": [],
      "status": "PASS"
    },
    "determinism": {
      "ambiguous_transitions": [],
      "status": "PASS"
    },
    "completeness": {
      "undefined_transitions": [],
      "status": "PASS"
    }
  },
  "proof": "All states reachable, transitions deterministic, all paths defined"
}
```

### Output Specification
```yaml
# artifacts/engineering/specifications/v{VERSION}/state-machines.yaml

state_machines:
  payment_flow:
    initial_state: pending
    terminal_states: [settled, failed]
    
    states:
      - name: pending
        description: "Payment initiated, awaiting authorization"
      - name: authorized
        description: "Payment authorized, funds reserved"
      - name: captured
        description: "Funds captured, awaiting settlement"
      - name: settled
        description: "Payment complete"
      - name: failed
        description: "Payment failed"
    
    transitions:
      - from: pending
        to: authorized
        event: authorize_payment
        guard: payment_method_valid
        actions: [reserve_funds, log_authorization]
      
      - from: authorized
        to: captured
        event: capture_funds
        guard: funds_reserved
        actions: [capture_amount, notify_merchant]
      
      - from: captured
        to: settled
        event: settlement_complete
        actions: [finalize_transaction, send_receipt]
      
      - from: pending
        to: failed
        event: authorization_failed
        actions: [log_failure, notify_customer]
      
      - from: authorized
        to: failed
        event: capture_failed
        actions: [release_funds, log_failure]
    
    validation:
      reachability: true
      determinism: true
      completeness: true
      proof: proofs/architecture/state-machine-proofs/payment-flow.proof
```

## Success Criteria

1. ✅ All states reachable from initial
2. ✅ No ambiguous transitions (deterministic)
3. ✅ All event + state combinations handled (complete)
4. ✅ Terminal states identified
5. ✅ Guards and actions specified

## Next Steps

- State machines ready for implementation in **backend-prover**
- Use in runtime validation and testing