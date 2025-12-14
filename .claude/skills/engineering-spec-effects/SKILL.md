---
name: spec-effects
description: |
  Define effect types used by morphisms. Creates the effect algebra including
  IO, error types, state, and reader effects. Use when: defining error types,
  specifying effect semantics, building the monad foundation.
---

# Spec Effects

Define the effect algebra for the system.

## Categorical Foundation

Effects are type constructors that modify morphism signatures:

```
Pure:     f: A → B
Effectful: f: A → M[B]

Where M is a monad (or monad stack)
```

Effects enable:
- Controlled side effects (IO)
- Error handling (Either, Option)
- Dependency injection (Reader)
- State threading (State)

## Input

- `artifacts/v{N}/spec/morphisms.yaml` — To extract used effects
- Natural language requirements — For error type definitions

## Output

`artifacts/v{N}/spec/effects.yaml`

## Process

1. **Collect effects** from morphisms.yaml
2. **Define error types** with variants
3. **Define environment types** if Reader used
4. **Define state types** if State used
5. **Document effect semantics**

## Effect Kinds

### IO Effect

Represents external input/output operations.

```yaml
- id: "IO"
  kind: io
  parameters:
    - name: "A"
      variance: covariant
  description: "Effectful computation performing I/O"
```

**Used when:**
- Database operations
- Network calls
- File system access
- Time/random operations

### Error Effect

Represents computations that can fail.

```yaml
- id: "Either[E, _]"
  kind: error
  parameters:
    - name: "E"
      variance: covariant
    - name: "A"
      variance: covariant
  description: "Computation that may fail with error E"
```

**Used when:**
- Validation can fail
- Resource not found
- Business rule violation
- External service failure

### Option Effect

Represents optional results (error without information).

```yaml
- id: "Option"
  kind: error
  parameters:
    - name: "A"
      variance: covariant
  description: "Computation that may produce no result"
```

**Used when:**
- Lookup may not find item
- Optional field access
- Filter that might match nothing

### Reader Effect

Represents dependency on environment.

```yaml
- id: "Reader[R, _]"
  kind: reader
  parameters:
    - name: "R"
      variance: contravariant
    - name: "A"
      variance: covariant
  description: "Computation reading from environment R"
```

**Used when:**
- Configuration access
- Dependency injection
- Request context

### State Effect

Represents stateful computation.

```yaml
- id: "State[S, _]"
  kind: state
  parameters:
    - name: "S"
      variance: invariant
    - name: "A"
      variance: covariant
  description: "Computation threading state S"
```

**Used when:**
- Accumulating results
- Transaction management
- Session state

### Async Effect

Represents asynchronous computation.

```yaml
- id: "Async"
  kind: async
  parameters:
    - name: "A"
      variance: covariant
  description: "Asynchronous computation"
```

**Note:** In practice, IO often subsumes Async. Separate only if needed.

## Error Type Definitions

For each `Either[E, _]` effect, define the error type:

```yaml
error_types:
  - id: "UserError"
    description: "Errors in user operations"
    variants:
      - name: "NotFound"
        payload: "UserId"
        description: "User with given ID does not exist"
        
      - name: "AlreadyExists"
        payload: "Email"
        description: "User with email already registered"
        
      - name: "InvalidCredentials"
        payload: null
        description: "Email or password incorrect"
        
      - name: "AccountSuspended"
        payload: "SuspensionReason"
        description: "User account is suspended"
        
      - name: "ValidationFailed"
        payload: "List[String]"
        description: "Input validation errors"
```

### Error Type Patterns

**Domain Errors** — Business rule violations:
```yaml
- id: "OrderError"
  variants:
    - name: "InsufficientInventory"
      payload: "ProductId"
    - name: "PaymentDeclined"
      payload: "PaymentError"
    - name: "OrderNotModifiable"
      payload: "OrderStatus"
```

**Validation Errors** — Input validation failures:
```yaml
- id: "ValidationError"
  variants:
    - name: "InvalidField"
      payload: "Tuple[String, String]"  # (field, message)
    - name: "MissingRequired"
      payload: "String"  # field name
    - name: "InvalidFormat"
      payload: "Tuple[String, String]"  # (field, expected_format)
```

**Aggregate Errors** — For unified handling:
```yaml
- id: "AppError"
  variants:
    - name: "Domain"
      payload: "DomainError"  # Union of all domain errors
    - name: "Validation"
      payload: "ValidationError"
    - name: "Infrastructure"
      payload: "InfraError"
```

## Environment Type Definitions

For `Reader[R, _]` effects:

```yaml
environment_types:
  - id: "Env"
    description: "Application environment"
    fields:
      - name: "config"
        type: "AppConfig"
      - name: "logger"
        type: "Logger"
      - name: "tracer"
        type: "Tracer"
```

## Output Format

```yaml
version: "1.0"

# Standard effects
effects:
  - id: "IO"
    kind: io
    parameters:
      - name: "A"
        variance: covariant
    description: "Side-effectful computation"
    
  - id: "Either[E, _]"
    kind: error
    parameters:
      - name: "E"
        variance: covariant
        description: "Error type"
      - name: "A"
        variance: covariant
        description: "Success type"
    description: "Computation that may fail with typed error"
    
  - id: "Option"
    kind: error
    parameters:
      - name: "A"
        variance: covariant
    description: "Computation that may produce no result"
    
  - id: "Reader[R, _]"
    kind: reader
    parameters:
      - name: "R"
        variance: contravariant
        description: "Environment type"
      - name: "A"
        variance: covariant
        description: "Result type"
    description: "Computation reading from environment"

# Domain error types
error_types:
  - id: "ValidationError"
    description: "Input validation failures"
    variants:
      - name: "InvalidEmail"
        payload: "String"
        description: "Email format invalid"
      - name: "PasswordTooWeak"
        payload: "List[String]"
        description: "Password policy violations"
      - name: "MissingField"
        payload: "String"
        description: "Required field missing"
    traces_to: ["req:input-validation"]
    
  - id: "UserError"
    description: "User domain errors"
    variants:
      - name: "NotFound"
        payload: "UserId"
        description: "User does not exist"
      - name: "AlreadyExists"
        payload: "Email"
        description: "Email already registered"
      - name: "InvalidCredentials"
        payload: null
        description: "Authentication failed"
      - name: "AccountSuspended"
        payload: "SuspensionReason"
        description: "Account is suspended"
    traces_to: ["req:user-errors"]
    
  - id: "EmailError"
    description: "Email service errors"
    variants:
      - name: "SendFailed"
        payload: "String"
        description: "Failed to send email"
      - name: "InvalidRecipient"
        payload: "Email"
        description: "Recipient address invalid"
    traces_to: ["req:email-errors"]
    
  # Aggregate error type
  - id: "AppError"
    description: "Application-level error union"
    variants:
      - name: "Validation"
        payload: "ValidationError"
      - name: "User"
        payload: "UserError"
      - name: "Email"
        payload: "EmailError"
    traces_to: ["req:error-handling"]

# Environment types (if Reader effect used)
environment_types:
  - id: "AppConfig"
    description: "Application configuration"
    fields:
      - name: "database_url"
        type: "String"
      - name: "email_service_url"
        type: "String"
      - name: "jwt_secret"
        type: "String"
    traces_to: ["req:configuration"]
```

## Extracting Error Types

From morphisms.yaml, find all `Either[E, _]` effects and extract E:

```yaml
# morphism
- id: "create_user"
  effects: ["IO", "Either[UserError, _]"]

# → Must define UserError in effects.yaml
```

### Error Variant Extraction

From requirements, identify failure modes:

| Requirement | Error Variant |
|-------------|---------------|
| "User must exist" | `NotFound(UserId)` |
| "Email must be unique" | `AlreadyExists(Email)` |
| "Must be authenticated" | `InvalidCredentials` |
| "Account can be suspended" | `AccountSuspended(Reason)` |

## Validation Rules

1. **Coverage**: Every `Either[E, _]` must have E defined
2. **Completeness**: Error variants should cover all failure modes
3. **No orphans**: Every error type should be used
4. **Valid payloads**: Error payloads must reference existing objects
5. **Hierarchy**: Consider unified AppError for top-level handling

## Validation Checklist

- [ ] All effects from morphisms.yaml are defined
- [ ] All error types have variants
- [ ] All variant payloads reference valid types
- [ ] Error types cover all failure scenarios
- [ ] Environment types defined if Reader used

## Do NOT

- **Define infrastructure errors here** — DbError, HttpError are functor concerns
- **Mix transport and domain errors** — Domain errors are categorical
- **Create catch-all "Error" type** — Be specific about failure modes
- **Include stack traces in types** — That's runtime, not type structure
