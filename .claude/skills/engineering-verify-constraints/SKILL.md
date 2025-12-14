---
name: verify-constraints
description: |
  Verify business constraints and invariants from spec. Generates proofs
  for proof_obligation constraints and plans runtime checks for others.
  Use when: verifying invariants, checking business rules, planning validation.
---

# Verify Constraints

Verify business constraints from spec/constraints.yaml.

## Input

- `artifacts/v{N}/spec/constraints.yaml`
- `artifacts/v{N}/build/category.yaml`
- `artifacts/v{N}/verify/proofs/` (from verify-laws)

## Output

`artifacts/v{N}/verify/constraints-report.yaml`

## Process

1. **Load constraints** from spec/constraints.yaml
2. **Categorize** by proof_obligation
3. **For proof_obligation: true** — Verify Lean proof exists
4. **For proof_obligation: false** — Plan runtime validation
5. **Report status**

## Constraint Categories

### Proven Constraints

Constraints with `proof_obligation: true` that have Lean proofs.

```yaml
- id: "positive_money"
  kind: invariant
  status: proven
  method: lean_proof
  evidence: "LeanOS/Constraints.lean:15"
```

### Runtime Checked Constraints

Constraints with `proof_obligation: false` that become runtime validation.

```yaml
- id: "max_order_items"
  kind: invariant
  status: runtime_check
  method: generated_validation
  evidence: "Validation in Order constructor"
```

### Sorry Constraints

Proof obligations that have `sorry` in Lean.

```yaml
- id: "get_after_create"
  kind: law
  status: sorry
  method: lean_proof
  evidence: "LeanOS/Constraints.lean:45 - requires DB semantics"
```

## Verification Methods

### Lean Proof

For constraints that can be proven statically:

```lean
-- Invariant: created user has pending status
theorem created_user_is_pending (input : CreateUserInput) :
    (create_user input).status = UserStatus.Pending := by
  simp [create_user]
  rfl
```

### Construction Enforcement

For refined types, the invariant is enforced by construction:

```yaml
- id: "valid_email_format"
  kind: invariant
  scope: "Email"
  status: proven
  method: construction
  evidence: "Email type only constructible with valid format"
```

### Runtime Validation

For dynamic constraints:

```yaml
- id: "order_item_limit"
  kind: invariant
  scope: "Order"
  status: runtime_check
  method: generated_validation
  evidence: |
    Generated validation in Order.__init__:
    if len(items) > 100:
        raise ConstraintViolation("order_item_limit")
```

### Database Enforcement

For uniqueness and referential integrity:

```yaml
- id: "unique_email"
  kind: invariant
  status: database_enforced
  method: unique_constraint
  evidence: "UNIQUE constraint on users.email column"
```

## Output Format

```yaml
version: "1.0"

constraints:
  # ========================================
  # Invariants
  # ========================================
  
  - id: "positive_money"
    kind: invariant
    scope: "Money"
    expression: "value >= 0"
    proof_obligation: true
    status: proven
    method: construction
    evidence: "Money type only accepts non-negative Decimal"
    file: null
    line: null
    
  - id: "valid_email_format"
    kind: invariant
    scope: "Email"
    expression: "matches(value, EMAIL_REGEX)"
    proof_obligation: true
    status: proven
    method: construction
    evidence: "Email type validates format on construction"
    file: null
    line: null
    
  - id: "user_has_id"
    kind: invariant
    scope: "User"
    expression: "id != null"
    proof_obligation: true
    status: proven
    method: construction
    evidence: "User requires UserId which is non-nullable"
    file: null
    line: null
    
  - id: "order_item_limit"
    kind: invariant
    scope: "Order"
    expression: "items.length <= 100"
    proof_obligation: false
    status: runtime_check
    method: generated_validation
    evidence: "Runtime check in Order constructor"
    generated_code: |
      if len(items) > 100:
          raise ConstraintViolation("order_item_limit", 
              f"Order has {len(items)} items, max is 100")
    
  - id: "unique_email"
    kind: invariant
    scope: "System"
    expression: "∀ u1, u2. u1.id ≠ u2.id → u1.email ≠ u2.email"
    proof_obligation: false
    status: database_enforced
    method: unique_constraint
    evidence: "UNIQUE constraint on users.email"
    generated_code: |
      -- Migration
      ALTER TABLE users ADD CONSTRAINT unique_email UNIQUE (email);
      
  # ========================================
  # Preconditions
  # ========================================
  
  - id: "active_user_for_order"
    kind: precondition
    scope: "create_order"
    expression: "user.status == UserStatus.Active"
    proof_obligation: true
    status: proven
    method: lean_proof
    evidence: "Proven that create_order checks status"
    file: "LeanOS/Constraints.lean"
    line: 30
    
  - id: "non_empty_cart"
    kind: precondition
    scope: "checkout"
    expression: "cart.items.length > 0"
    proof_obligation: true
    status: runtime_check
    method: generated_validation
    evidence: "Validation before checkout"
    generated_code: |
      if not cart.items:
          raise PreconditionViolation("non_empty_cart",
              "Cannot checkout empty cart")
              
  # ========================================
  # Postconditions
  # ========================================
  
  - id: "created_user_is_pending"
    kind: postcondition
    scope: "create_user"
    expression: "result.status == UserStatus.Pending"
    proof_obligation: true
    status: proven
    method: construction
    evidence: "create_user always sets status to Pending"
    file: null
    line: null
    
  - id: "order_total_positive"
    kind: postcondition
    scope: "create_order"
    expression: "result.total > Money.zero"
    proof_obligation: true
    status: proven
    method: lean_proof
    evidence: "Proven from non-empty cart and positive prices"
    file: "LeanOS/Constraints.lean"
    line: 50
    
  - id: "id_unchanged_on_update"
    kind: postcondition
    scope: "update_user"
    expression: "result.id == input.id"
    proof_obligation: true
    status: proven
    method: construction
    evidence: "update_user preserves id field"
    file: null
    line: null
    
  # ========================================
  # Laws
  # ========================================
  
  - id: "get_after_create"
    kind: law
    scope: "create_user, get_user"
    expression: "get_user(create_user(input).id) == create_user(input)"
    proof_obligation: true
    status: sorry
    method: lean_proof
    evidence: "Requires database semantics to prove"
    file: "LeanOS/Constraints.lean"
    line: 60
    note: "Verified by integration tests instead"
    
  - id: "idempotent_activation"
    kind: law
    scope: "activate_user"
    expression: "activate_user(activate_user(u)) == activate_user(u)"
    proof_obligation: true
    status: proven
    method: lean_proof
    evidence: "Proven: activating active user is no-op"
    file: "LeanOS/Constraints.lean"
    line: 70
    
  - id: "composition_definition"
    kind: law
    scope: "register_user"
    expression: "register_user = send_welcome >=> create_user >=> validate"
    proof_obligation: false
    status: definitional
    method: construction
    evidence: "register_user is defined as this composition"

# ========================================
# Summary
# ========================================
summary:
  total: 14
  
  by_status:
    proven: 9
    runtime_check: 3
    database_enforced: 1
    sorry: 1
    
  by_kind:
    invariant: 6
    precondition: 2
    postcondition: 4
    law: 2
    
  coverage:
    proven_percentage: 64.3
    verified_percentage: 92.9  # proven + runtime + db
    unverified: 1
    
  issues:
    - constraint: "get_after_create"
      issue: "Cannot prove without database model"
      resolution: "Covered by integration tests"

# ========================================
# Generated Validations
# ========================================
generated_validations:
  description: "Runtime checks to be generated in gen phase"
  
  constructors:
    - type: "Order"
      checks:
        - constraint: "order_item_limit"
          code: "assert len(items) <= 100"
          
  morphisms:
    - morphism: "checkout"
      pre_checks:
        - constraint: "non_empty_cart"
          code: "assert len(cart.items) > 0"
          
  database:
    - table: "users"
      constraints:
        - constraint: "unique_email"
          sql: "UNIQUE (email)"
```

## Verification Decision Tree

```
For each constraint:
  │
  ├─ proof_obligation: true?
  │   │
  │   ├─ Can prove in Lean? → status: proven
  │   │
  │   ├─ Enforced by construction? → status: proven, method: construction
  │   │
  │   └─ Cannot prove? → status: sorry, plan alternative verification
  │
  └─ proof_obligation: false?
      │
      ├─ Runtime checkable? → status: runtime_check
      │
      ├─ Database enforced? → status: database_enforced
      │
      └─ Definitional? → status: definitional
```

## Validation Rules

1. **All constraints addressed**: Every constraint has status
2. **Proof obligations checked**: proof_obligation: true → must have proof attempt
3. **Runtime checks planned**: Non-proven constraints have validation plan
4. **No unaddressed constraints**: Everything either proven or has mitigation
5. **Summary accurate**: Counts match constraint list

## Validation Checklist

- [ ] All constraints from spec/constraints.yaml present
- [ ] Each constraint has status
- [ ] Each proof_obligation: true has proof file reference or sorry note
- [ ] Each runtime_check has generated_code
- [ ] Summary counts are correct
- [ ] Issues documented

## Do NOT

- **Ignore proof obligations** — Must attempt proof
- **Skip runtime checks** — If not proven, must check at runtime
- **Hide sorries** — Document and plan alternatives
- **Leave constraints unaddressed** — Every one needs status
