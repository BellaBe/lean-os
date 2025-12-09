---
name: transaction-standard-definer
description: |
  Define transaction standards as categorical structures. Produces transaction monad,
  distributed saga patterns, compensation morphisms, and isolation levels.
  Transactions as monads with rollback semantics.
  Input: categories/*.std.yaml, services.spec.yaml
  Output: standards/transactions/*.std.yaml
---

# Transaction Standard Definer

Define transaction patterns as categorical structures.

## Purpose

Transform stateful operations into transactional standards:
1. Transaction monad (local transactions)
2. Saga pattern (distributed transactions)
3. Compensation morphisms (rollback)
4. Isolation levels

## Input

- `standards/categories/storage.std.yaml` - Storage category
- `services.spec.yaml` - Operations requiring transactions

## Output

```
standards/transactions/
├── transaction.std.yaml  # Transaction monad
└── saga.std.yaml         # Distributed saga
```

## Transaction Standard

### Schema

```yaml
# standards/transactions/transaction.std.yaml

standard:
  name: Transaction
  description: "Transaction as monad with commit/rollback"

# Transaction monad
monad:
  name: Transaction
  type_constructor: "Transaction[A] = Connection → IO[Either[TxError, A]]"
  
  pure: |
    λa. λconn. IO(Right(a))
    
  bind: |
    λma f. λconn.
      ma(conn).flatMap {
        case Right(a) → f(a)(conn)
        case Left(e) → IO(Left(e))
      }
      
  # Monad laws
  laws:
    - left_identity: "pure(a) >>= f ≡ f(a)"
    - right_identity: "m >>= pure ≡ m"
    - associativity: "(m >>= f) >>= g ≡ m >>= (x → f(x) >>= g)"

# Transaction operations
operations:
  - name: begin
    type: "Unit → Transaction[Unit]"
    sql: "BEGIN"
    semantics: "Start new transaction"
    
  - name: commit
    type: "Transaction[A] → IO[Either[TxError, A]]"
    sql: "COMMIT"
    semantics: "Persist changes"
    
  - name: rollback
    type: "Transaction[A] → IO[Either[TxError, Unit]]"
    sql: "ROLLBACK"
    semantics: "Discard changes"
    
  - name: savepoint
    type: "String → Transaction[Savepoint]"
    sql: "SAVEPOINT {name}"
    semantics: "Create nested transaction point"
    
  - name: rollback_to
    type: "Savepoint → Transaction[Unit]"
    sql: "ROLLBACK TO {savepoint}"
    semantics: "Partial rollback"

# Transaction boundaries
boundaries:
  # Unit of work pattern
  unit_of_work:
    description: "Group related operations in single transaction"
    pattern: |
      def create_merchant_with_profile(input):
        with transaction():
          merchant = create_merchant(input.merchant)
          profile = create_profile(input.profile, merchant.id)
          return (merchant, profile)
          
  # Read operations
  reads:
    transaction_required: false
    isolation: read_committed
    
  # Write operations
  writes:
    transaction_required: true
    isolation: repeatable_read

# Isolation levels
isolation:
  levels:
    - name: read_uncommitted
      value: 0
      anomalies: [dirty_read, non_repeatable_read, phantom_read]
      use_for: never
      
    - name: read_committed
      value: 1
      anomalies: [non_repeatable_read, phantom_read]
      use_for: [default_reads]
      
    - name: repeatable_read
      value: 2
      anomalies: [phantom_read]
      use_for: [default_writes]
      
    - name: serializable
      value: 3
      anomalies: []
      use_for: [financial_operations]
      
  default: read_committed

# Transactional morphisms
transactional_morphisms:
  # Operations requiring transactions
  - name: create_merchant
    requires_transaction: true
    isolation: repeatable_read
    
  - name: process_subscription
    requires_transaction: true
    isolation: serializable  # Financial operation
    
  - name: transfer_credits
    requires_transaction: true
    isolation: serializable
    
  # Grouped operations
  - name: complete_analysis
    requires_transaction: true
    operations:
      - update_analysis_status
      - create_recommendations
      - update_profile_stats
    rollback_on_failure: true

# Error handling
errors:
  types:
    - name: TxError
      variants:
        - DeadlockDetected
        - SerializationFailure
        - ConnectionLost
        - ConstraintViolation
        - Timeout
        
  retry_policy:
    - error: DeadlockDetected
      action: retry
      max_attempts: 3
      backoff: exponential
      
    - error: SerializationFailure
      action: retry
      max_attempts: 3
      backoff: exponential
      
    - error: ConstraintViolation
      action: fail  # Don't retry
      
    - error: Timeout
      action: rollback_and_fail

# Categorical interpretation
categorical:
  # Transaction as Kleisli category
  kleisli:
    name: "Kleisli[Transaction]"
    objects: types
    morphisms: "A → Transaction[B]"
    composition: "Kleisli composition via bind"
    identity: pure
    
  # Transaction functor
  functor:
    lift: "IO[A] → Transaction[A]"
    semantics: "Lift IO action into transaction context"
    
  laws:
    - "Transaction preserves composition"
    - "Rollback is left inverse of commit (when no side effects)"
```

## Saga Standard

### Schema

```yaml
# standards/transactions/saga.std.yaml

standard:
  name: Saga
  description: "Distributed transactions as morphism sequences with compensations"

# Saga structure
saga:
  definition: |
    A saga is a sequence of local transactions T₁, T₂, ..., Tₙ
    where each Tᵢ has a compensating transaction Cᵢ
    
  execution: |
    Execute T₁, T₂, ..., Tₙ in order
    If Tᵢ fails, execute Cᵢ₋₁, Cᵢ₋₂, ..., C₁ (reverse order)

# Saga coordination patterns
patterns:
  - name: choreography
    description: "Event-driven, decentralized"
    flow: |
      Service A completes → emits Event A
      Service B listens for Event A → completes → emits Event B
      On failure: emit compensation events
    use_for: [simple_sagas, loosely_coupled]
    
  - name: orchestration
    description: "Centralized coordinator"
    flow: |
      Orchestrator calls Service A
      On success: Orchestrator calls Service B
      On failure: Orchestrator calls compensation
    use_for: [complex_sagas, tight_coordination]

# Saga definitions
sagas:
  - name: create_merchant_saga
    description: "Create merchant with all dependencies"
    steps:
      - name: create_merchant
        service: merchant_service
        action: create_merchant
        compensation: delete_merchant
        
      - name: setup_shopify
        service: shopify_service
        action: install_app
        compensation: uninstall_app
        
      - name: initialize_settings
        service: settings_service
        action: create_default_settings
        compensation: delete_settings
        
    on_failure: rollback_all
    
  - name: process_analysis_saga
    description: "Process photo analysis with external API"
    steps:
      - name: reserve_credits
        service: billing_service
        action: reserve_credits
        compensation: release_credits
        
      - name: upload_photo
        service: storage_service
        action: upload_photo
        compensation: delete_photo
        
      - name: analyze_photo
        service: analysis_service
        action: analyze_with_groq
        compensation: mark_analysis_failed
        
      - name: charge_credits
        service: billing_service
        action: confirm_charge
        compensation: refund_credits
        
    on_failure: rollback_all

# Compensation morphisms
compensation:
  definition: |
    For each step morphism f: A → B,
    there exists compensation c: B → A' 
    where A' represents "compensated state"
    
  properties:
    - name: semantic_undo
      description: "Compensation undoes business effect, not data"
      example: |
        charge_card: Account → ChargedAccount
        refund_card: ChargedAccount → RefundedAccount
        Note: RefundedAccount ≠ Account (has refund record)
        
    - name: idempotent
      description: "Compensation can be safely retried"
      
    - name: commutative_with_failure
      description: "Order of compensation may vary"

  morphisms:
    - action: create_merchant
      compensation: delete_merchant
      compensation_type: hard_delete
      
    - action: reserve_credits
      compensation: release_credits
      compensation_type: state_change
      
    - action: charge_card
      compensation: refund_card
      compensation_type: new_transaction
      
    - action: send_email
      compensation: send_cancellation_email
      compensation_type: compensating_action

# Saga state machine
state_machine:
  states:
    - STARTED
    - STEP_{N}_PENDING
    - STEP_{N}_COMPLETED
    - STEP_{N}_FAILED
    - COMPENSATING
    - COMPENSATION_{N}_COMPLETED
    - COMPLETED
    - FAILED
    - COMPENSATED
    
  transitions:
    - from: STARTED
      to: STEP_1_PENDING
      trigger: saga_started
      
    - from: STEP_{N}_PENDING
      to: STEP_{N}_COMPLETED
      trigger: step_succeeded
      
    - from: STEP_{N}_PENDING
      to: STEP_{N}_FAILED
      trigger: step_failed
      
    - from: STEP_{N}_FAILED
      to: COMPENSATING
      trigger: start_compensation
      
    - from: COMPENSATING
      to: COMPENSATION_{N}_COMPLETED
      trigger: compensation_succeeded
      
    - from: COMPENSATION_{N}_COMPLETED
      to: COMPENSATED
      trigger: all_compensated
      condition: N == 0

# Saga execution
execution:
  timeout:
    saga_timeout_ms: 300000  # 5 minutes total
    step_timeout_ms: 30000   # 30 seconds per step
    
  retry:
    max_step_retries: 3
    compensation_retries: 5  # More retries for compensation
    backoff: exponential
    
  persistence:
    store: saga_log  # Table tracking saga state
    fields:
      - saga_id
      - saga_type
      - current_state
      - step_results
      - started_at
      - completed_at

# Categorical interpretation
categorical:
  # Saga as sequence in category
  sequence:
    definition: |
      Saga = T₁ ; T₂ ; ... ; Tₙ
      where ; is Kleisli composition
      
  # Compensation as pseudo-inverse
  pseudo_inverse:
    definition: |
      For f: A → B, compensation c is pseudo-inverse if:
      f ; c ; f ≈ f (up to business equivalence)
      
  # Saga monad
  monad:
    name: Saga
    type_constructor: |
      Saga[A] = SagaContext → IO[Either[SagaError, (A, Compensations)]]
      
    bind: |
      Accumulate compensations, execute steps in order
      On failure, run accumulated compensations in reverse
      
  laws:
    - "Saga preserves atomicity (all or nothing)"
    - "Compensation reverses business effect"
    - "Completed saga is consistent state"
```

## Validation

### Completeness Checks

```yaml
completeness:
  - all_writes_have_transaction_boundary
  - all_distributed_ops_have_saga
  - all_saga_steps_have_compensation
  - isolation_levels_specified
```

### Consistency Checks

```yaml
consistency:
  - compensations_match_actions
  - saga_steps_idempotent
  - timeout_values_reasonable
  - retry_policies_defined
```

## Next Skills

Output feeds into:
- `configuration-standard-definer`
- `standards-validator`
