---
name: level-7-transformations
description: |
  Level 7: Natural Transformations. Morphisms between functors that commute
  with functor action. Used for middleware, adapters, and cross-cutting concerns.
  
  Input: level-5.manifest.yaml, level-6.manifest.yaml
  Output: level-7.manifest.yaml + transformation definitions
  
  UNIVERSAL: Works for any domain. Examples are illustrative only.
---

# Level 7: Natural Transformations

Morphisms between functors. Systematic transformations that respect structure.

## Principle

A natural transformation α: F ⟹ G consists of:
- Component morphisms α_A: F(A) → G(A) for each object A
- Naturality condition: commutative squares

```
Natural Transformation α: F ⟹ G

For each object A:
  α_A: F(A) → G(A)

Naturality square (for each f: A → B):

     F(A) ──F(f)──> F(B)
      │              │
    α_A            α_B
      │              │
      ▼              ▼
     G(A) ──G(f)──> G(B)

Condition: α_B ∘ F(f) = G(f) ∘ α_A
```

## Standard Transformations

Common natural transformations in systems:

```yaml
standard_transformations:
  Auth:
    source: "Handler"
    target: "AuthenticatedHandler"
    description: "Adds authentication to handlers"
    component: "Verify token, attach identity"
    
  Metrics:
    source: "Handler"
    target: "MetricsHandler"
    description: "Adds metrics collection"
    component: "Record request count, latency"
    
  Logging:
    source: "Handler"
    target: "LoggedHandler"
    description: "Adds structured logging"
    component: "Log request/response"
    
  Tracing:
    source: "Handler"
    target: "TracedHandler"
    description: "Adds distributed tracing"
    component: "Create span, propagate context"
    
  Caching:
    source: "Query"
    target: "CachedQuery"
    description: "Adds caching layer"
    component: "Check cache, populate on miss"
    
  Retry:
    source: "ExternalCall"
    target: "RetryingCall"
    description: "Adds retry logic"
    component: "Retry with backoff"
```

## Process

```yaml
process:
  step_1_load_inputs:
    inputs:
      - "level-5.manifest.yaml"   # Functors
      - "level-6.manifest.yaml"   # Adjunctions (unit/counit are transformations)
    action: "Load and validate inputs exist"
    
  step_2_enumerate_transformations:
    action: "Identify all natural transformations"
    sources:
      - "Adjunction units (η)"
      - "Adjunction counits (ε)"
      - "Cross-cutting concerns from specification"
      - "Middleware from specification"
    algorithm: |
      transformations = []
      
      # From adjunctions
      for adj in level_6.adjunctions:
          transformations.append(adj.unit)
          transformations.append(adj.counit)
          
      # From specification
      for transform in specification.transformations:
          transformations.append(transform)
          
      return transformations
    
  step_3_define_components:
    action: "Define component for each object"
    for_each: "transformation in transformations"
    algorithm: |
      for object in transformation.source_functor.source.objects:
          component = define_component(object, transformation)
          transformation.components.append(component)
          
  step_4_validate_naturality:
    action: "Verify naturality squares commute"
    for_each: "transformation in transformations"
    check: "α_B ∘ F(f) = G(f) ∘ α_A for all f: A → B"
    critical: "Naturality must hold"
    
  step_5_produce_manifest:
    action: "Write level-7.manifest.yaml"
```

## Transformation Structure

```yaml
transformation_pattern:
  name: "{TransformationName}"
  notation: "α: F ⟹ G"
  
  source:
    functor: "{SourceFunctor}"
    ref: "level-5.functor.{SourceFunctor}"
    
  target:
    functor: "{TargetFunctor}"
    ref: "level-5.functor.{TargetFunctor}"
    
  components:
    - object: "A"
      morphism: "α_A: F(A) → G(A)"
      implementation: "How to transform"
    # One component per object
    
  naturality:
    statement: "∀ f: A → B. α_B ∘ F(f) = G(f) ∘ α_A"
    proof_obligation: "level-8.proof.naturality.{name}"
```

## Manifest Item Schema

```yaml
transformation_item:
  id: "transformation.{Name}"
  name: "{Name}"
  kind: "natural_transformation"
  traces:
    - ref: "level-5.functor.{Source}"
      role: "source_functor"
    - ref: "level-5.functor.{Target}"
      role: "target_functor"
  definition:
    source_functor: "{Source}"
    target_functor: "{Target}"
    components:
      - {object: "A", morphism: "α_A", implementation: "..."}
      # All components
  naturality:
    verified: pending
    proof_ref: null
  status: "pending|defined|naturality_verified"
```

## Middleware Chain

Transformations compose vertically (∘) and horizontally (∗):

```yaml
middleware_composition:
  vertical:
    description: "α ∘ β when target(β) = source(α)"
    example: "Auth ∘ Logging = first log, then auth"
    
  horizontal:
    description: "α ∗ β for parallel functors"
    example: "Metrics on HTTP ∗ Tracing on HTTP"
    
  chain:
    order: [RequestId, Logging, Metrics, Tracing, Auth]
    composition: "Auth ∘ Tracing ∘ Metrics ∘ Logging ∘ RequestId"
    application: "innermost first"
```

## Validation Rules

```yaml
validation:
  components_complete:
    rule: "∀ A ∈ source_functor.source.objects: α_A defined"
    description: "Component exists for every object"
    critical: true
    
  type_correct:
    rule: "α_A: F(A) → G(A)"
    description: "Components have correct types"
    critical: true
    
  naturality:
    rule: "∀ f: A → B. α_B ∘ F(f) = G(f) ∘ α_A"
    description: "Naturality squares commute"
    critical: true
    proof_required: true
```

## Output Structure

```
level-7.manifest.yaml
generated/{language}/src/{project}/
├── transformations/
│   ├── auth.{ext}           # Auth transformation
│   ├── logging.{ext}        # Logging transformation
│   ├── metrics.{ext}        # Metrics transformation
│   └── tracing.{ext}        # Tracing transformation
└── middleware/
    ├── chain.{ext}          # Middleware composition
    └── components.{ext}     # Individual components
```

## Invariant

```
∀ transformation α: F ⟹ G:
  |α.components| = |F.source.objects|
  naturality.verified = true

Violation is FATAL. Pipeline MUST NOT proceed to Level 8.
```

## Example (Illustrative Only)

```yaml
# level-7.manifest.yaml
items:
  - id: "transformation.Auth"
    kind: "natural_transformation"
    name: "Auth"
    traces:
      - ref: "level-5.functor.Handler"
        role: "source_functor"
      - ref: "level-5.functor.AuthenticatedHandler"
        role: "target_functor"
    definition:
      source_functor: "Handler"
      target_functor: "AuthenticatedHandler"
      components:
        - object: "CustomerRequest"
          morphism: "auth_CustomerRequest"
          implementation: "verify_token(request)"
        - object: "OrderRequest"
          morphism: "auth_OrderRequest"
          implementation: "verify_token(request)"
    naturality:
      statement: "Auth_Response ∘ Handler(f) = AuthHandler(f) ∘ Auth_Request"
      verified: pending
      proof_obligation: "level-8.proof.naturality.Auth"

counts:
  total: 4  # Auth, Logging, Metrics, Tracing
  
validation:
  all_components_defined: true
  naturality_pending_proof: true
  complete: true
```
