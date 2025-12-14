---
name: verify-coverage
description: |
  Verify 100% coverage from spec through build to gen. Traces every spec
  item to generated code. Use when: validating completeness, finding gaps,
  ensuring nothing lost in translation.
---

# Verify Coverage

Verify complete traceability from spec to generated code.

## Input

- `artifacts/v{N}/spec/*.yaml`
- `artifacts/v{N}/build/*.yaml`
- `artifacts/v{N}/gen/*-manifest.yaml`

## Output

`artifacts/v{N}/verify/coverage-report.yaml`

## Process

1. **Collect spec items** — Objects, morphisms, effects, constraints
2. **Trace to build** — Each spec item in category/effects/functors
3. **Trace to gen** — Each build item in generated code
4. **Report gaps** — Any item without trace
5. **Calculate percentage**

## Coverage Requirements

```
SPEC → BUILD: 100%
  Every object in objects.yaml appears in category.yaml
  Every morphism in morphisms.yaml appears in category.yaml
  Every effect in effects.yaml appears in effects.yaml (build)
  
BUILD → GEN: 100% (for enabled targets)
  Every category object generates type definition
  Every category morphism generates function implementation
  Every functor mapping generates target code
  Every transformation generates wrapper
```

## Traceability Matrix

### Objects

```
spec/objects.yaml          build/category.yaml         gen/types-manifest.yaml
─────────────────          ───────────────────         ───────────────────────
User                   →   objects: [User]         →   src/domain/user.py
UserId                 →   objects: [UserId]       →   src/domain/user.py
Email                  →   objects: [Email]        →   src/domain/value_objects.py
CreateUserInput        →   objects: [...]          →   src/domain/inputs.py
```

### Morphisms

```
spec/morphisms.yaml        build/category.yaml         gen/morphisms-manifest.yaml
───────────────────        ───────────────────         ─────────────────────────
create_user            →   morphisms: [create_user] →  src/domain/user_ops.py
get_user               →   morphisms: [get_user]    →  src/domain/user_ops.py
validate_email         →   morphisms: [...]         →  src/domain/validation.py
```

### Functors

```
build/functors.yaml        gen/morphisms-manifest.yaml
───────────────────        ─────────────────────────
F_api.POST /users      →   src/api/users.py
F_api.GET /users/{id}  →   src/api/users.py
F_persist.insert_user  →   src/repos/user_repo.py
```

### Transformations

```
build/transformations.yaml   gen/wiring-manifest.yaml
──────────────────────────   ────────────────────────
auth                     →   src/middleware/auth.py
logging                  →   src/middleware/logging.py
timeout                  →   src/middleware/timeout.py
```

## Output Format

```yaml
version: "1.0"

coverage:
  # ========================================
  # Objects Coverage
  # ========================================
  objects:
    spec_count: 15
    build_count: 15
    gen_count: 15
    
    percentage: 100.0
    status: PASS
    
    traces:
      - spec: "User"
        build: "category.yaml:objects"
        gen: "src/domain/user.py"
        status: complete
        
      - spec: "UserId"
        build: "category.yaml:objects"
        gen: "src/domain/user.py"
        status: complete
        
      - spec: "Email"
        build: "category.yaml:objects"
        gen: "src/domain/value_objects.py"
        status: complete
        
      - spec: "UserStatus"
        build: "category.yaml:objects"
        gen: "src/domain/user.py"
        status: complete
        
      - spec: "CreateUserInput"
        build: "category.yaml:objects"
        gen: "src/domain/inputs.py"
        status: complete
        
      # ... all objects
        
    gaps: []
    
  # ========================================
  # Morphisms Coverage
  # ========================================
  morphisms:
    spec_count: 12
    build_count: 12
    gen_count: 12
    
    percentage: 100.0
    status: PASS
    
    traces:
      - spec: "create_user"
        build: "category.yaml:morphisms"
        gen: "src/domain/user_ops.py"
        functor_applications:
          - functor: "F_api"
            gen: "src/api/users.py:create_user_handler"
          - functor: "F_persist"
            gen: "src/repos/user_repo.py:insert"
        status: complete
        
      - spec: "get_user"
        build: "category.yaml:morphisms"
        gen: "src/domain/user_ops.py"
        functor_applications:
          - functor: "F_api"
            gen: "src/api/users.py:get_user_handler"
          - functor: "F_persist"
            gen: "src/repos/user_repo.py:find_by_id"
        status: complete
        
      - spec: "validate_email"
        build: "category.yaml:morphisms"
        gen: "src/domain/validation.py"
        functor_applications: []  # Pure, no functor application
        status: complete
        
      - spec: "register_user"
        build: "category.yaml:morphisms"
        gen: "src/domain/user_ops.py"
        note: "Derived morphism, generates composition"
        status: complete
        
      # ... all morphisms
        
    gaps: []
    
  # ========================================
  # Effects Coverage
  # ========================================
  effects:
    spec_count: 4
    build_count: 4
    gen_count: 4
    
    percentage: 100.0
    status: PASS
    
    traces:
      - spec: "IO"
        build: "effects.yaml:layers"
        gen: "async/await pattern"
        status: complete
        
      - spec: "Either[AppError, _]"
        build: "effects.yaml:layers"
        gen: "Result type + exception handling"
        status: complete
        
      - spec: "Reader[Env, _]"
        build: "effects.yaml:layers"
        gen: "Dependency injection container"
        status: complete
        
      # ... all effects
        
    gaps: []
    
  # ========================================
  # Constraints Coverage
  # ========================================
  constraints:
    spec_count: 14
    verified_count: 13
    unverified_count: 1
    
    percentage: 92.9
    status: WARN
    
    traces:
      - spec: "positive_money"
        verification: "proven"
        gen: "Money type constructor"
        status: complete
        
      - spec: "valid_email_format"
        verification: "proven"
        gen: "Email type constructor"
        status: complete
        
      - spec: "order_item_limit"
        verification: "runtime_check"
        gen: "src/domain/order.py:__init__"
        status: complete
        
      - spec: "get_after_create"
        verification: "sorry"
        gen: "Integration test coverage"
        status: partial
        
    gaps:
      - id: "get_after_create"
        reason: "Cannot prove, covered by tests"
        
  # ========================================
  # Functors Coverage
  # ========================================
  functors:
    - id: "F_api"
      enabled: true
      
      objects_mapped:
        total: 8
        generated: 8
        percentage: 100.0
        
      morphisms_mapped:
        total: 12
        generated: 12
        percentage: 100.0
        
      status: PASS
      
    - id: "F_persist"
      enabled: true
      
      objects_mapped:
        total: 5
        generated: 5
        percentage: 100.0
        
      morphisms_mapped:
        total: 8
        generated: 8
        percentage: 100.0
        
      status: PASS
      
    - id: "F_events"
      enabled: false
      status: SKIPPED
      
  # ========================================
  # Transformations Coverage
  # ========================================
  transformations:
    - id: "auth"
      enabled: true
      applied_to: 10  # endpoints
      generated: "src/middleware/auth.py"
      status: PASS
      
    - id: "logging"
      enabled: true
      applied_to: 15  # morphisms
      generated: "src/middleware/logging.py"
      status: PASS
      
    - id: "timeout"
      enabled: true
      applied_to: 8  # IO morphisms
      generated: "src/middleware/timeout.py"
      status: PASS
      
    - id: "retry"
      enabled: true
      applied_to: 6  # DB operations
      generated: "src/middleware/retry.py"
      status: PASS
      
    - id: "validation"
      enabled: true
      applied_to: 12  # endpoints
      generated: "src/middleware/validation.py"
      status: PASS
      
    - id: "tracing"
      enabled: false
      status: SKIPPED
      
    - id: "circuit_breaker"
      enabled: false
      status: SKIPPED

# ========================================
# Overall Summary
# ========================================
overall:
  spec_to_build:
    objects: "15/15 (100%)"
    morphisms: "12/12 (100%)"
    effects: "4/4 (100%)"
    total: "100%"
    status: PASS
    
  build_to_gen:
    types: "15/15 (100%)"
    morphisms: "12/12 (100%)"
    functors: "2/2 enabled (100%)"
    transformations: "5/5 enabled (100%)"
    total: "100%"
    status: PASS
    
  constraints:
    verified: "13/14 (92.9%)"
    status: WARN
    note: "1 constraint covered by integration tests"
    
  overall_status: PASS
  
  summary: |
    Complete traceability from spec to generated code.
    All objects, morphisms, and effects have implementations.
    All enabled functors and transformations are generated.
    One constraint (get_after_create) relies on test coverage.

# ========================================
# File Inventory
# ========================================
generated_files:
  domain:
    - "src/domain/__init__.py"
    - "src/domain/user.py"
    - "src/domain/order.py"
    - "src/domain/value_objects.py"
    - "src/domain/inputs.py"
    - "src/domain/user_ops.py"
    - "src/domain/order_ops.py"
    - "src/domain/validation.py"
    
  api:
    - "src/api/__init__.py"
    - "src/api/users.py"
    - "src/api/orders.py"
    - "src/api/routes.py"
    
  repos:
    - "src/repos/__init__.py"
    - "src/repos/user_repo.py"
    - "src/repos/order_repo.py"
    
  middleware:
    - "src/middleware/__init__.py"
    - "src/middleware/auth.py"
    - "src/middleware/logging.py"
    - "src/middleware/timeout.py"
    - "src/middleware/retry.py"
    - "src/middleware/validation.py"
    
  infrastructure:
    - "src/main.py"
    - "src/container.py"
    - "src/config.py"
    
  total_count: 21
```

## Coverage Calculation

```python
# Objects coverage
objects_coverage = len(generated_objects) / len(spec_objects) * 100

# Morphisms coverage  
morphisms_coverage = len(generated_morphisms) / len(spec_morphisms) * 100

# Constraints coverage
constraints_coverage = len(verified_constraints) / len(spec_constraints) * 100

# Overall
overall = (objects_coverage + morphisms_coverage + constraints_coverage) / 3
```

## Status Determination

| Coverage | Status |
|----------|--------|
| 100% | PASS |
| 95-99% | WARN |
| < 95% | FAIL |

## Gap Analysis

When coverage < 100%, identify gaps:

```yaml
gaps:
  objects:
    - id: "TempObject"
      reason: "Internal type, not exposed"
      resolution: "Expected - internal implementation detail"
      
  morphisms:
    - id: "helper_function"
      reason: "Not in category, helper only"
      resolution: "Move to spec or mark as internal"
      
  constraints:
    - id: "complex_invariant"
      reason: "Cannot prove statically"
      resolution: "Runtime check added"
```

## Validation Rules

1. **100% spec→build**: Every spec item in build artifacts
2. **100% build→gen**: Every build item generates code (for enabled targets)
3. **Document gaps**: Any < 100% must be explained
4. **No orphans**: Generated code traces back to spec
5. **Constraints addressed**: Even sorry constraints have mitigation

## Validation Checklist

- [ ] All spec objects in category.yaml
- [ ] All spec morphisms in category.yaml
- [ ] All spec effects in build effects.yaml
- [ ] All category items generate code
- [ ] All enabled functors fully mapped
- [ ] All enabled transformations generated
- [ ] Gaps documented with resolution
- [ ] Overall status determined

## Do NOT

- **Accept gaps silently** — Must document and justify
- **Skip disabled targets** — Mark as SKIPPED, don't fail
- **Count internal helpers** — Only spec items matter
- **Ignore constraints** — Even sorry needs mitigation plan
