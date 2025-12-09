---
name: effect-analyzer
description: Analyze and tag morphisms with effect types (IO, Either, State). Use after morphism-specifier to enrich services.spec.yaml with monadic effects. Identifies which operations perform IO, can fail, or have state. Critical for Kleisli category construction and monad transformer composition.
---

# Effect Analyzer

Enrich morphisms with effect types. Transforms pure morphisms `A → B` into effectful morphisms `A → F[B]` where F is the appropriate effect monad.

## Input

Requires:
- `artifacts/engineering/v{X}/specifications/services.spec.yaml` (from morphism-specifier)
- `artifacts/engineering/v{X}/specifications/domain-concepts.yaml` (external_dependencies)

## Output

Enrich `artifacts/engineering/v{X}/specifications/services.spec.yaml` with effect annotations:

```yaml
# Added to each morphism
morphisms:
  - name: morphism_name
    domain: InputType
    codomain: OutputType
    
    # NEW: Effect specification
    effects:
      io: true | false
      fallible: true | false
      stateful: true | false
    
    # NEW: Effect type
    effect_signature: "A → IO[Either[Error, B]]"
    
    # NEW: Error types (if fallible)
    errors:
      - ErrorType1
      - ErrorType2
    
    # NEW: Kleisli category
    kleisli_category: IO | Either | IO_Either | Pure
```

## Effect Classification

### IO Effect

Operation performs side effects:

**Indicators:**
- Database read/write
- External API call
- File system access
- Network communication
- Time/random

```yaml
# Repository operations → IO
- name: save_merchant
  effects:
    io: true
    fallible: true
  kleisli_category: IO_Either

# External calls → IO
- name: fetch_shopify_products
  effects:
    io: true
    fallible: true
  kleisli_category: IO_Either

# Pure domain logic → no IO
- name: validate_email
  effects:
    io: false
    fallible: true
  kleisli_category: Either
```

### Fallible Effect (Either)

Operation can fail:

**Indicators:**
- total: false
- Validation
- External dependency
- Resource lookup

```yaml
# Can fail: not found
- name: get_merchant
  effects:
    fallible: true
  errors:
    - NotFoundError

# Can fail: validation
- name: validate_subscription
  effects:
    fallible: true
  errors:
    - ValidationError

# Cannot fail: always succeeds
- name: id_merchant
  effects:
    fallible: false
```

### State Effect

Operation modifies shared state:

**Indicators:**
- Mutable cache
- Session management
- Transaction context

```yaml
- name: update_cache
  effects:
    stateful: true
```

## Effect Signatures

Map effect combinations to signatures:

| IO | Fallible | Stateful | Signature |
|----|----------|----------|-----------|
| ✗ | ✗ | ✗ | `A → B` (Pure) |
| ✗ | ✓ | ✗ | `A → Either[E, B]` |
| ✓ | ✗ | ✗ | `A → IO[B]` |
| ✓ | ✓ | ✗ | `A → IO[Either[E, B]]` |
| ✓ | ✓ | ✓ | `A → StateT[IO[Either[E, _]], S, B]` |

## Error Type Hierarchy

Define error types for fallible morphisms:

```yaml
# Add to requirements.adt
coproducts:
  - name: DomainError
    variants:
      - name: NotFound
        payload: EntityId
      - name: ValidationFailed
        payload: ValidationErrors
      - name: BusinessRuleViolation
        payload: RuleName
      - name: Conflict
        payload: ConflictInfo
    derives_from: error

  - name: InfrastructureError
    variants:
      - name: DatabaseError
        payload: DbErrorInfo
      - name: ConnectionError
        payload: ConnectionInfo
      - name: TimeoutError
        payload: TimeoutInfo
    derives_from: error

  - name: ExternalError
    variants:
      - name: ShopifyError
        payload: ShopifyErrorResponse
      - name: GroqError
        payload: GroqErrorResponse
      - name: RateLimited
        payload: RetryAfter
    derives_from: error

  - name: AppError
    variants:
      - name: Domain
        payload: DomainError
      - name: Infrastructure
        payload: InfrastructureError
      - name: External
        payload: ExternalError
    derives_from: error
```

## Morphism Analysis Rules

### Layer-Based Detection

```yaml
# domain layer: Either only (no IO)
- layer: domain
  default_effects:
    io: false
    fallible: true
  kleisli_category: Either

# repository layer: IO + Either
- layer: repository
  default_effects:
    io: true
    fallible: true
  kleisli_category: IO_Either

# external layer: IO + Either
- layer: external
  default_effects:
    io: true
    fallible: true
  kleisli_category: IO_Either
```

### Operation-Based Detection

```yaml
# create → can fail (duplicate, validation)
- category: command
  operation_prefix: create_
  typical_errors:
    - ValidationError
    - ConflictError

# get → can fail (not found)
- category: query
  operation_prefix: get_
  typical_errors:
    - NotFoundError

# list → usually succeeds (empty list)
- category: query
  operation_prefix: list_
  typical_errors: []  # Returns empty, not error

# delete → can fail (not found)
- category: command
  operation_prefix: delete_
  typical_errors:
    - NotFoundError

# update → can fail (not found, validation, conflict)
- category: command
  operation_prefix: update_
  typical_errors:
    - NotFoundError
    - ValidationError
    - ConflictError
```

## Kleisli Composition

Effects determine composition strategy:

### Pure Composition
```
f: A → B
g: B → C
g ∘ f: A → C
```

### Kleisli[Either] Composition
```
f: A → Either[E, B]
g: B → Either[E, C]
g <=< f: A → Either[E, C]

# First runs f, if Right(b), runs g(b)
# If Left(e) at any point, short-circuits
```

### Kleisli[IO] Composition
```
f: A → IO[B]
g: B → IO[C]
g <=< f: A → IO[C]

# Sequences IO actions
```

### Kleisli[IO_Either] Composition
```
f: A → IO[Either[E, B]]
g: B → IO[Either[E, C]]
g <=< f: A → IO[Either[E, C]]

# Uses monad transformer
# Requires distributive law: Either[E, IO[A]] → IO[Either[E, A]]
```

## Composition Enrichment

Update compositions with effect propagation:

```yaml
compositions:
  - name: full_analysis_flow
    chain:
      - upload_photo      # IO[Either[E, PhotoId]]
      - request_analysis  # IO[Either[E, Analysis]]
      - process_analysis  # IO[Either[E, AnalysisResult]]
      - generate_recommendations  # IO[Either[E, Recommendations]]
    
    # NEW: Composed effect
    effect_signature: "PhotoInput → IO[Either[AppError, Recommendations]]"
    kleisli_category: IO_Either
    
    # NEW: Error accumulation
    possible_errors:
      - StorageError      # from upload_photo
      - DatabaseError     # from request_analysis
      - ExternalError     # from process_analysis (AI)
      - BusinessRuleViolation  # from generate_recommendations
```

## Validation Checklist

Before outputting, verify:

- [ ] Every morphism has effect classification
- [ ] Fallible morphisms have error types
- [ ] Error types exist in requirements.adt
- [ ] Compositions have correct effect propagation
- [ ] Kleisli categories are consistent within compositions
- [ ] No IO in pure domain layer

## Effect Laws

Generated effects must satisfy monad laws:

**Left Identity:** `return a >>= f ≡ f a`
**Right Identity:** `m >>= return ≡ m`
**Associativity:** `(m >>= f) >>= g ≡ m >>= (λx. f x >>= g)`

For transformers, also:
**Distributive:** `δ: Either[E, IO[A]] → IO[Either[E, A]]`

## Next Skill

Output feeds into:
- **resilience-specifier** → adds retry, circuit breaker for IO
- **categorical-structure-detector** → identifies Kleisli categories
