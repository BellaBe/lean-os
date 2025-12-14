---
name: spec-constraints
description: |
  Define constraints, invariants, and laws for the system. Creates proof
  obligations for formal verification. Use when: specifying business rules,
  defining invariants, creating validation requirements, expressing laws.
---

# Spec Constraints

Define constraints that must be proven or enforced.

## Categorical Foundation

Constraints are propositions about our category:

```
Invariant:     ∀ x : A. P(x)
Precondition:  P(input) → morphism defined
Postcondition: morphism(input) = output → Q(output)
Law:           f ∘ g = h (algebraic equality)
```

## Input

- `artifacts/v{N}/spec/objects.yaml`
- `artifacts/v{N}/spec/morphisms.yaml`
- `artifacts/v{N}/spec/effects.yaml`
- Natural language requirements

## Output

`artifacts/v{N}/spec/constraints.yaml`

## Process

1. **Extract invariants** — Properties always true for types
2. **Extract preconditions** — What must hold before morphism
3. **Extract postconditions** — What holds after morphism
4. **Extract laws** — Algebraic equalities
5. **Mark proof obligations** — Which need formal proof

## Constraint Kinds

### Invariant

Property that always holds for a type.

```yaml
- id: "positive_balance"
  kind: invariant
  scope: "Account"
  expression: "balance >= Money.zero"
  proof_obligation: true
  description: "Account balance is never negative"
```

**Checked:** At construction and after every modification.

### Precondition

Property that must hold before a morphism can execute.

```yaml
- id: "user_must_be_active"
  kind: precondition
  scope: "create_order"
  expression: "user.status == UserStatus.Active"
  proof_obligation: true
  description: "Only active users can create orders"
```

**Checked:** At morphism entry.

### Postcondition

Property that holds after a morphism executes.

```yaml
- id: "order_has_id"
  kind: postcondition
  scope: "create_order"
  expression: "result.id != null && result.created_at != null"
  proof_obligation: true
  description: "Created order has ID and timestamp"
```

**Checked:** At morphism exit (proven to hold given precondition).

### Law

Algebraic equality between morphism compositions.

```yaml
- id: "idempotent_activation"
  kind: law
  scope: "activate_user"
  expression: "activate_user ∘ activate_user = activate_user"
  proof_obligation: true
  description: "Activating an already active user is idempotent"
```

**Checked:** By formal proof.

## Expression Language

### Comparisons
```
x == y          # Equality
x != y          # Inequality
x < y           # Less than
x <= y          # Less than or equal
x > y           # Greater than
x >= y          # Greater than or equal
```

### Logical Operators
```
P && Q          # Conjunction (and)
P || Q          # Disjunction (or)
!P              # Negation (not)
P -> Q          # Implication (if P then Q)
P <-> Q         # Biconditional (P iff Q)
```

### Quantifiers
```
forall x : T. P(x)              # For all x of type T, P holds
exists x : T. P(x)              # There exists x of type T where P holds
forall x in collection. P(x)    # For all elements in collection
exists x in collection. P(x)    # There exists element in collection
```

### Field Access
```
object.field                    # Direct field
object.nested.field             # Nested field
```

### Collections
```
collection.length               # Size
collection.isEmpty              # Empty check
collection.contains(x)          # Membership
collection.forall(P)            # All satisfy P
collection.exists(P)            # Some satisfies P
```

### Arithmetic
```
x + y                           # Addition
x - y                           # Subtraction
x * y                           # Multiplication
x / y                           # Division
x % y                           # Modulo
```

### Special
```
null                            # Null reference
result                          # Output of morphism (in postconditions)
input                           # Input to morphism (in pre/postconditions)
old(expr)                       # Value before morphism (in postconditions)
```

## Common Patterns

### Non-Null Invariant
```yaml
- id: "user_email_required"
  kind: invariant
  scope: "User"
  expression: "email != null"
```

### Range Constraint
```yaml
- id: "valid_quantity"
  kind: invariant
  scope: "LineItem"
  expression: "quantity > 0 && quantity <= 1000"
```

### Uniqueness
```yaml
- id: "unique_email"
  kind: invariant
  scope: "System"  # System-wide constraint
  expression: "forall u1, u2 : User. u1.id != u2.id -> u1.email != u2.email"
  proof_obligation: false  # Enforced by database
```

### State Transition
```yaml
- id: "valid_status_transition"
  kind: precondition
  scope: "suspend_user"
  expression: "user.status == UserStatus.Active"
```

### Preservation
```yaml
- id: "id_preserved"
  kind: postcondition
  scope: "update_user"
  expression: "result.id == old(user.id)"
```

### Idempotency
```yaml
- id: "get_is_idempotent"
  kind: law
  scope: "get_user"
  expression: "get_user(id) == get_user(id)"
  proof_obligation: false  # Follows from function definition
```

### Composition Law
```yaml
- id: "validate_then_create"
  kind: law
  scope: "register_user"
  expression: "register_user = send_welcome ∘ create_user ∘ validate"
```

## Proof Obligations

When `proof_obligation: true`:
- Constraint becomes a theorem in verify-laws
- Must be proven in Lean 4
- Failure blocks code generation

When `proof_obligation: false`:
- Constraint becomes a runtime check
- Generated as validation code
- Tested but not proven

### Deciding Proof Obligation

| Constraint Type | Proof Obligation | Reason |
|-----------------|------------------|--------|
| Type invariant (simple) | true | Can prove from constructor |
| Type invariant (complex) | false | May need runtime check |
| Precondition | true | Must prove morphism safe |
| Postcondition | true | Must prove morphism correct |
| Algebraic law | true | Core correctness property |
| Uniqueness | false | Database enforced |
| Business limit | false | Runtime configuration |

## Output Format

```yaml
version: "1.0"
constraints:
  # ========================================
  # Type Invariants
  # ========================================
  
  - id: "positive_money"
    kind: invariant
    scope: "Money"
    expression: "value >= 0"
    proof_obligation: true
    description: "Money values are non-negative"
    traces_to: ["req:financial-integrity"]
    
  - id: "valid_email_format"
    kind: invariant
    scope: "Email"
    expression: "matches(value, EMAIL_REGEX)"
    proof_obligation: true
    description: "Email matches valid format"
    traces_to: ["req:email-validation"]
    
  - id: "user_has_id"
    kind: invariant
    scope: "User"
    expression: "id != null"
    proof_obligation: true
    description: "Every user has an ID"
    traces_to: ["req:user-identity"]
    
  - id: "order_item_limit"
    kind: invariant
    scope: "Order"
    expression: "items.length <= 100"
    proof_obligation: false  # Runtime check
    description: "Orders limited to 100 items"
    traces_to: ["req:order-limits"]
    
  # ========================================
  # Preconditions
  # ========================================
  
  - id: "active_user_for_order"
    kind: precondition
    scope: "create_order"
    expression: "user.status == UserStatus.Active"
    proof_obligation: true
    description: "Only active users can create orders"
    traces_to: ["req:order-eligibility"]
    
  - id: "non_empty_cart"
    kind: precondition
    scope: "checkout"
    expression: "cart.items.length > 0"
    proof_obligation: true
    description: "Cannot checkout empty cart"
    traces_to: ["req:checkout-validation"]
    
  # ========================================
  # Postconditions
  # ========================================
  
  - id: "created_user_is_pending"
    kind: postcondition
    scope: "create_user"
    expression: "result.status == UserStatus.Pending"
    proof_obligation: true
    description: "New users start in pending status"
    traces_to: ["req:user-lifecycle"]
    
  - id: "order_total_positive"
    kind: postcondition
    scope: "create_order"
    expression: "result.total > Money.zero"
    proof_obligation: true
    description: "Order total is positive"
    traces_to: ["req:order-validation"]
    
  - id: "id_unchanged_on_update"
    kind: postcondition
    scope: "update_user"
    expression: "result.id == input.id"
    proof_obligation: true
    description: "User ID cannot change"
    traces_to: ["req:identity-preservation"]
    
  # ========================================
  # Laws
  # ========================================
  
  - id: "get_after_create"
    kind: law
    scope: "create_user, get_user"
    expression: "get_user(create_user(input).id) == create_user(input)"
    proof_obligation: true
    description: "Get returns what was created"
    traces_to: ["req:data-consistency"]
    
  - id: "idempotent_activation"
    kind: law
    scope: "activate_user"
    expression: "activate_user(activate_user(u)) == activate_user(u)"
    proof_obligation: true
    description: "Activation is idempotent"
    traces_to: ["req:idempotency"]
    
  - id: "composition_definition"
    kind: law
    scope: "register_user"
    expression: "register_user = send_welcome_email >=> create_user >=> validate_input"
    proof_obligation: false  # Definitional
    description: "Registration is this composition"
    traces_to: ["req:registration-flow"]
```

## Validation Rules

1. **Scope exists**: Every scope must reference valid object or morphism
2. **Expression valid**: Expressions must be well-typed
3. **References resolved**: All identifiers in expressions exist
4. **Proof marked**: Critical constraints have proof_obligation: true
5. **Traced**: Every constraint traces to requirements

## Validation Checklist

- [ ] All scopes reference objects.yaml or morphisms.yaml
- [ ] All expressions use valid syntax
- [ ] All field references valid for scope type
- [ ] proof_obligation set appropriately
- [ ] All traces_to reference valid requirements

## Do NOT

- **Include implementation logic** — Just the proposition
- **Reference infrastructure** — No DB constraints, API validation
- **Mix domain and technical** — Domain constraints only
- **Over-specify** — Focus on what matters for correctness
