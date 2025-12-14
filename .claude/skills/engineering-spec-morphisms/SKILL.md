---
name: spec-morphisms
description: |
  Extract operations from requirements as categorical morphisms. Identifies
  domain, codomain, effects, and whether morphisms are generators or derived
  from composition. Use when: defining operations, adding functionality,
  analyzing behavior, specifying workflows.
---

# Spec Morphisms

Extract categorical morphisms (operations) from requirements.

## Categorical Foundation

Morphisms are arrows between objects. Every operation is a morphism:

```
f: A → B           (pure morphism)
f: A → M[B]        (effectful morphism, Kleisli arrow)
```

The category doesn't distinguish "atomic" from "composed" — both are morphisms.
We track this for implementation purposes only.

## Input

- Natural language requirements
- `artifacts/v{N}/spec/objects.yaml`

## Output

`artifacts/v{N}/spec/morphisms.yaml`

## Process

1. **Identify operations** — Verbs acting on domain objects
2. **Determine domain** — What input is required?
3. **Determine codomain** — What output is produced?
4. **Classify effects** — Pure? IO? Can fail?
5. **Identify compositions** — Is this built from other morphisms?

## Morphism Classification

### Generator Morphisms

Atomic operations defined directly. Cannot be decomposed further in our domain.

```yaml
- id: "create_user"
  domain: "CreateUserInput"
  codomain: "User"
  effects: ["IO", "Either[UserError, _]"]
  pure: false
  generator: true
  description: "Create a new user account"
```

### Derived Morphisms

Compositions of other morphisms. Defined by their chain.

```yaml
- id: "register_user"
  domain: "RegistrationInput"
  codomain: "Unit"
  effects: ["IO", "Either[RegistrationError, _]"]
  pure: false
  generator: false
  composed_of: ["validate_input", "create_user", "send_welcome_email"]
  composition_type: kleisli
  description: "Complete user registration flow"
```

## Effect Classification

| Effect | Notation | When Used |
|--------|----------|-----------|
| Pure | (none) | Deterministic, no side effects |
| IO | `IO[_]` | External I/O (DB, network, file) |
| Either | `Either[E, _]` | Can fail with error type E |
| Option | `Option[_]` | Can fail with no information |
| State | `State[S, _]` | Threads mutable state |
| Reader | `Reader[R, _]` | Reads from environment |
| Async | `Async[_]` | Asynchronous execution |

### Combining Effects

Most morphisms combine multiple effects:

```yaml
effects: ["IO", "Either[UserError, _]"]
# Means: A → IO[Either[UserError, B]]
# This is a Kleisli arrow in the App monad
```

## Composition Types

### Pure Composition (∘)

When both morphisms are pure:

```
g: B → C
f: A → B
g ∘ f: A → C
```

```yaml
composition_type: pure
```

### Kleisli Composition (>=>)

When morphisms have monadic effects:

```
g: B → M[C]
f: A → M[B]
g >=> f: A → M[C]
```

```yaml
composition_type: kleisli
```

## Common Patterns

### CRUD Operations

```yaml
# Create
- id: "create_X"
  domain: "CreateXInput"
  codomain: "X"
  effects: ["IO", "Either[XError, _]"]
  generator: true
  
# Read (by ID)
- id: "get_X"
  domain: "XId"
  codomain: "X"
  effects: ["IO", "Either[XError, _]"]
  generator: true
  
# Read (list with filter)
- id: "list_X"
  domain: "XFilter"
  codomain: "List[X]"
  effects: ["IO", "Either[XError, _]"]
  generator: true
  
# Update
- id: "update_X"
  domain: "Tuple[XId, UpdateXInput]"
  codomain: "X"
  effects: ["IO", "Either[XError, _]"]
  generator: true
  
# Delete
- id: "delete_X"
  domain: "XId"
  codomain: "Unit"
  effects: ["IO", "Either[XError, _]"]
  generator: true
```

### Validation

```yaml
- id: "validate_email"
  domain: "String"
  codomain: "Email"
  effects: ["Either[ValidationError, _]"]
  pure: true  # No IO, just validation
  generator: true
```

### Transformation

```yaml
- id: "to_response"
  domain: "User"
  codomain: "UserResponse"
  effects: []
  pure: true
  generator: true
```

### Workflow (Derived)

```yaml
- id: "checkout"
  domain: "CheckoutInput"
  codomain: "Order"
  effects: ["IO", "Either[CheckoutError, _]"]
  generator: false
  composed_of:
    - "validate_cart"
    - "reserve_inventory"
    - "process_payment"
    - "create_order"
    - "send_confirmation"
  composition_type: kleisli
```

## Output Format

```yaml
version: "1.0"
morphisms:
  # ========================================
  # Generator Morphisms (atomic operations)
  # ========================================
  
  # Validation (pure)
  - id: "validate_email"
    domain: "String"
    codomain: "Email"
    effects: ["Either[ValidationError, _]"]
    pure: true
    generator: true
    description: "Validate and parse email string"
    traces_to: ["req:email-validation"]
    
  - id: "validate_password"
    domain: "String"
    codomain: "HashedPassword"
    effects: ["Either[ValidationError, _]"]
    pure: true
    generator: true
    description: "Validate password strength and hash"
    traces_to: ["req:password-policy"]
    
  # User CRUD (effectful)
  - id: "create_user"
    domain: "CreateUserInput"
    codomain: "User"
    effects: ["IO", "Either[UserError, _]"]
    pure: false
    generator: true
    description: "Create a new user in the system"
    traces_to: ["req:user-creation"]
    
  - id: "get_user"
    domain: "UserId"
    codomain: "User"
    effects: ["IO", "Either[UserError, _]"]
    pure: false
    generator: true
    description: "Retrieve user by ID"
    traces_to: ["req:user-retrieval"]
    
  - id: "get_user_by_email"
    domain: "Email"
    codomain: "User"
    effects: ["IO", "Either[UserError, _]"]
    pure: false
    generator: true
    description: "Retrieve user by email address"
    traces_to: ["req:user-lookup"]
    
  - id: "update_user_status"
    domain: "Tuple[UserId, UserStatus]"
    codomain: "User"
    effects: ["IO", "Either[UserError, _]"]
    pure: false
    generator: true
    description: "Update user account status"
    traces_to: ["req:user-status-management"]
    
  # External operations
  - id: "send_email"
    domain: "EmailMessage"
    codomain: "Unit"
    effects: ["IO", "Either[EmailError, _]"]
    pure: false
    generator: true
    description: "Send an email message"
    traces_to: ["req:email-notifications"]
    
  # Pure transformations
  - id: "build_welcome_email"
    domain: "User"
    codomain: "EmailMessage"
    effects: []
    pure: true
    generator: true
    description: "Build welcome email for new user"
    traces_to: ["req:welcome-email"]
    
  # ========================================
  # Derived Morphisms (compositions)
  # ========================================
  
  - id: "register_user"
    domain: "RegistrationInput"
    codomain: "User"
    effects: ["IO", "Either[RegistrationError, _]"]
    pure: false
    generator: false
    composed_of:
      - "validate_email"
      - "validate_password"
      - "check_email_not_exists"
      - "create_user"
      - "send_welcome_email"
    composition_type: kleisli
    description: "Complete user registration workflow"
    traces_to: ["req:user-registration-flow"]
    
  - id: "send_welcome_email"
    domain: "User"
    codomain: "Unit"
    effects: ["IO", "Either[EmailError, _]"]
    pure: false
    generator: false
    composed_of:
      - "build_welcome_email"
      - "send_email"
    composition_type: kleisli
    description: "Build and send welcome email"
    traces_to: ["req:welcome-email"]
    
  - id: "check_email_not_exists"
    domain: "Email"
    codomain: "Email"
    effects: ["IO", "Either[UserError, _]"]
    pure: false
    generator: true  # Actually generator, checks DB
    description: "Verify email is not already registered"
    traces_to: ["req:unique-email"]
```

## Type Checking Compositions

For a composition `[f₁, f₂, ..., fₙ]` to be valid:

```
f₁: A₁ → M[A₂]
f₂: A₂ → M[A₃]
...
fₙ: Aₙ → M[Aₙ₊₁]

Requirement: codomain(fᵢ) = domain(fᵢ₊₁)
             (ignoring the monad M)
```

The resulting composition has:
- Domain: domain(f₁) = A₁
- Codomain: codomain(fₙ) = Aₙ₊₁

## Validation Rules

1. **Domain exists**: Every domain type must exist in objects.yaml
2. **Codomain exists**: Every codomain type must exist in objects.yaml
3. **Effects valid**: All effects must be well-formed
4. **Composition valid**: composed_of chain must type-check
5. **No orphans**: Every morphism should be reachable or a top-level operation
6. **Pure consistency**: `pure: true` implies `effects: []`

## Validation Checklist

- [ ] All domain types exist in objects.yaml
- [ ] All codomain types exist in objects.yaml
- [ ] All effects follow valid syntax
- [ ] All composed_of references exist
- [ ] Composition chains type-check
- [ ] pure flag matches effects list
- [ ] All traces_to reference valid requirements

## Do NOT

- **Specify implementation details** — Just signature and composition
- **Include HTTP verbs/paths** — That's the API functor's job
- **Include SQL/queries** — That's the persistence functor's job
- **Include framework-specific code** — That's code generation
- **Create "wrapper" morphisms for infra** — That's natural transformations

## Pattern Recognition

| Requirement Pattern | Morphism Structure |
|---------------------|-------------------|
| "create X from Y" | `create_X: Y → M[X]` |
| "get X by id" | `get_X: XId → M[X]` |
| "update X with Y" | `update_X: (XId, Y) → M[X]` |
| "delete X" | `delete_X: XId → M[Unit]` |
| "validate X" | `validate_X: Raw → Either[Error, X]` |
| "transform X to Y" | `to_Y: X → Y` (pure) |
| "when X, do A then B then C" | derived morphism with composed_of |
| "X triggers Y" | composition or event (based on sync/async) |
