---
name: build-transformations
description: |
  Define natural transformations for cross-cutting concerns. Maps
  standardization config to categorical transformations (middleware,
  decorators). Use when: adding auth, logging, tracing, resilience patterns.
---

# Build Transformations

Define natural transformations for cross-cutting concerns.

## Categorical Foundation

A natural transformation α: F → G between functors F, G: C → D consists of:
- **Components**: α_A : F(A) → G(A) for each object A in C
- **Naturality**: For each f: A → B, G(f) ∘ α_A = α_B ∘ F(f)

In our context, transformations wrap morphisms uniformly:

```
Original:    f: A → M[B]
Transformed: α(f): A → M[B]  (with added behavior)
```

## Input

- `artifacts/v{N}/build/functors.yaml`
- `artifacts/v{N}/targets.yaml`

## Output

`artifacts/v{N}/build/transformations.yaml`

## Process

1. **Read standardization config** from targets.yaml
2. **For each enabled feature** — Define transformation
3. **Specify components** — How each morphism is wrapped
4. **State naturality** — Prove wrapping commutes
5. **Define composition order**

## Cross-Cutting as Transformations

| Feature | Transformation | Effect |
|---------|----------------|--------|
| Auth | α_auth | Verify credentials before morphism |
| Logging | α_log | Log entry/exit around morphism |
| Tracing | α_trace | Add span around morphism |
| Timeout | α_timeout | Limit execution time |
| Retry | α_retry | Retry on transient failure |
| Circuit Breaker | α_cb | Fail fast when service unhealthy |
| Validation | α_validate | Validate input before morphism |

## Transformation Definitions

### Auth Transformation

```yaml
- id: "auth"
  enabled: true  # from targets.standardization.auth.enabled
  kind: middleware
  
  config:
    type: "jwt"  # from targets.standardization.auth.type
    
  applies_to:
    functors: ["F_api"]  # Only API endpoints
    morphisms: "all"  # Or list specific ones
    exclude: ["health_check", "login"]
    
  components:
    pattern: |
      α_auth(endpoint) = λrequest.
        extract_token(request.headers)
        >>= verify_token
        >>= λuser. endpoint(request.with_user(user))
        
  naturality:
    statement: "Auth check commutes with request processing"
    explanation: "Verifying auth then processing = processing with verified context"
    status: stated
```

### Logging Transformation

```yaml
- id: "logging"
  enabled: true  # from targets.standardization.logging.enabled
  kind: decorator
  
  config:
    format: "json"
    level: "info"
    
  applies_to:
    functors: ["F_api", "F_persist"]
    morphisms: "all"
    
  components:
    pattern: |
      α_log(f) = λx.
        log_entry(f.name, x, level=info)
        >>= λ_. f(x)
        >>= λresult. log_exit(f.name, result, level=info)
        >>= λ_. return(result)
        
    on_error: |
      log_error(f.name, error, level=error)
      >>= λ_. raise(error)
      
  naturality:
    statement: "Logging doesn't affect computation result"
    explanation: "log(f(x)) returns same value as f(x)"
    status: stated
```

### Tracing Transformation

```yaml
- id: "tracing"
  enabled: false  # from targets.standardization.tracing.enabled
  kind: decorator
  
  # Not generated when disabled
```

### Timeout Transformation

```yaml
- id: "timeout"
  enabled: true  # from targets.standardization.resilience.timeout.enabled
  kind: decorator
  
  config:
    default_ms: 5000  # from targets.standardization.resilience.timeout.default_ms
    
  applies_to:
    functors: ["F_api", "F_persist"]
    morphisms: "io_morphisms"  # Only IO morphisms
    
  components:
    pattern: |
      α_timeout(f, ms=5000) = λx.
        race(
          f(x),
          delay(ms) >> raise(TimeoutError)
        )
        
  naturality:
    statement: "Timeout preserves result when completing in time"
    explanation: "If f(x) completes before timeout, result is unchanged"
    status: stated
```

### Retry Transformation

```yaml
- id: "retry"
  enabled: true  # from targets.standardization.resilience.retry.enabled
  kind: decorator
  
  config:
    max_attempts: 3
    backoff: "exponential"
    
  applies_to:
    functors: ["F_persist"]  # Database operations
    morphisms: "io_morphisms"
    exclude: ["delete_*"]  # Don't retry destructive ops
    
  components:
    pattern: |
      α_retry(f, max=3, backoff=exp) = λx.
        attempt(1, x)
        
      attempt(n, x) =
        f(x).catch(λe.
          if is_transient(e) && n < max then
            delay(backoff(n)) >> attempt(n+1, x)
          else
            raise(e)
        )
        
    backoff_functions:
      exponential: "λn. 100 * 2^n ms"
      constant: "λn. 100 ms"
      fibonacci: "λn. fib(n) * 100 ms"
      
  naturality:
    statement: "Retry returns first successful result"
    explanation: "If attempt k succeeds, result equals f(x) at attempt k"
    status: stated
```

### Circuit Breaker Transformation

```yaml
- id: "circuit_breaker"
  enabled: false  # from targets.standardization.resilience.circuit_breaker.enabled
  kind: decorator
  
  # Not generated when disabled
```

### Validation Transformation

```yaml
- id: "validation"
  enabled: true  # from targets.standardization.validation.enabled
  kind: middleware
  
  config:
    style: "pydantic"
    
  applies_to:
    functors: ["F_api"]
    morphisms: "all"
    
  components:
    pattern: |
      α_validate(endpoint) = λrequest.
        validate(request)
        >>= λvalid_request. endpoint(valid_request)
        
    on_invalid: |
      raise(ValidationError(errors))
      
  naturality:
    statement: "Validation doesn't affect valid inputs"
    explanation: "If request is valid, validate(request) >>= f = f(request)"
    status: stated
```

## Output Format

```yaml
version: "1.0"

transformations:
  # ========================================
  # Auth (middleware)
  # ========================================
  - id: "auth"
    enabled: true
    kind: middleware
    
    config:
      type: "jwt"
      
    source_functor: "F_api"
    target_functor: "F_api"
    
    applies_to:
      include: "all"
      exclude: ["health_check", "login", "register"]
      
    components:
      pattern: |
        α_auth(endpoint) = λrequest.
          verify_token(request.headers.authorization)
          >>= λuser. endpoint(request.with_context(user))
          
    naturality:
      statement: "G(f) ∘ α_A = α_B ∘ F(f)"
      explanation: "Auth check is independent of endpoint logic"
      status: stated
      
  # ========================================
  # Logging (decorator)
  # ========================================
  - id: "logging"
    enabled: true
    kind: decorator
    
    config:
      format: "json"
      level: "info"
      
    source_functor: "Identity"  # Applies to domain morphisms
    target_functor: "Identity"
    
    applies_to:
      include: "all"
      
    components:
      pattern: |
        α_log(f) = λx.
          log(level=info, event="enter", fn=f.name, input=x)
          >> f(x)
          >>= λr. log(level=info, event="exit", fn=f.name, output=r) >> return(r)
          
    naturality:
      statement: "Logging preserves semantics"
      status: stated
      
  # ========================================
  # Timeout (decorator)
  # ========================================
  - id: "timeout"
    enabled: true
    kind: decorator
    
    config:
      default_ms: 5000
      
    source_functor: "F_persist"
    target_functor: "F_persist"
    
    applies_to:
      include: "io_morphisms"
      
    components:
      pattern: |
        α_timeout(f, ms) = λx.
          with_timeout(ms, f(x))
          
    naturality:
      statement: "Timeout preserves successful results"
      status: stated
      
  # ========================================
  # Retry (decorator)
  # ========================================
  - id: "retry"
    enabled: true
    kind: decorator
    
    config:
      max_attempts: 3
      backoff: "exponential"
      base_delay_ms: 100
      
    source_functor: "F_persist"
    target_functor: "F_persist"
    
    applies_to:
      include: "io_morphisms"
      exclude: ["delete_*"]
      
    components:
      pattern: |
        α_retry(f) = λx. retry_loop(f, x, attempt=1)
        
        retry_loop(f, x, attempt) =
          f(x).catch_transient(λe.
            if attempt < max_attempts then
              sleep(backoff(attempt)) >> retry_loop(f, x, attempt+1)
            else
              raise(e)
          )
          
    naturality:
      statement: "Retry returns eventual success or final failure"
      status: stated
      
  # ========================================
  # Validation (middleware)
  # ========================================
  - id: "validation"
    enabled: true
    kind: middleware
    
    config:
      style: "pydantic"
      
    source_functor: "F_api"
    target_functor: "F_api"
    
    applies_to:
      include: "all"
      
    components:
      pattern: |
        α_validate(endpoint) = λrequest.
          validate_schema(request)
          >>= λvalid. endpoint(valid)
          
    naturality:
      statement: "Validation is idempotent on valid input"
      status: stated
      
  # ========================================
  # Tracing (disabled)
  # ========================================
  - id: "tracing"
    enabled: false
    note: "Disabled in targets.yaml"
    
  # ========================================
  # Circuit Breaker (disabled)
  # ========================================
  - id: "circuit_breaker"
    enabled: false
    note: "Disabled in targets.yaml"

# ========================================
# Composition Order
# ========================================
composition_order:
  description: "Order in which transformations are applied (outer to inner)"
  
  F_api:
    # Applied from outside in:
    # logging(auth(validation(timeout(endpoint))))
    - "logging"      # Outermost - log everything including auth
    - "auth"         # Auth check
    - "validation"   # Input validation
    - "timeout"      # Innermost - timeout on actual work
    
  F_persist:
    - "logging"
    - "timeout"
    - "retry"  # Retry inside timeout (individual attempts, not total)

# ========================================
# Validation
# ========================================
validation:
  transformations_generated:
    auth: true
    logging: true
    tracing: false
    timeout: true
    retry: true
    circuit_breaker: false
    validation: true
    
  naturality_stated: 6  # For each enabled transformation
```

## Transformation Composition

Transformations compose:

```
α_log ∘ α_auth ∘ α_validate ∘ α_timeout

Applied as (reading inside out):
  endpoint
  |> with_timeout
  |> with_validation
  |> with_auth
  |> with_logging
```

The composition order matters for semantics:
- Logging outside auth → logs auth failures
- Auth outside validation → validates only authenticated requests
- Timeout inside retry → each attempt has timeout

## Validation Rules

1. **Only enabled features**: Transformation only if feature enabled
2. **Valid functors**: applies_to functors must exist
3. **Naturality stated**: Each transformation has naturality statement
4. **Composition order**: Defined for each functor
5. **Config matches targets**: All config from targets.yaml

## Validation Checklist

- [ ] Each enabled standardization feature has transformation
- [ ] Each disabled feature has transformation with enabled: false
- [ ] All referenced functors exist in functors.yaml
- [ ] Naturality stated for each enabled transformation
- [ ] Composition order defined for each affected functor

## Do NOT

- **Create transformation for disabled feature** — Just stub
- **Apply auth to unauthenticated endpoints** — Use exclude list
- **Skip naturality statement** — Required for correctness
- **Mix transformation logic** — Each does one thing
