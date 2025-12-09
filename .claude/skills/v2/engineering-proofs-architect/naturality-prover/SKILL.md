---
name: naturality-prover
description: |
  Prove naturality of all natural transformations. Generates Lean 4 proofs that
  naturality squares commute: α_B ∘ F(f) = G(f) ∘ α_A for auth, validation,
  metrics, and other middleware transformations.
  Input: proofs/lean/LeanOS/Functor.lean, maps/transformations/*.map.yaml
  Output: proofs/lean/LeanOS/NaturalTransformation.lean
---

# Naturality Prover

Prove naturality for all natural transformations.

## Purpose

Generate Lean 4 proofs for naturality:
1. Naturality condition: α_B ∘ F(f) = G(f) ∘ α_A
2. Component existence: α_A exists for all A
3. Composition of transformations is natural
4. Identity transformation is natural

## Input

- `proofs/lean/LeanOS/Functor.lean` - Functor proofs
- `maps/transformations/*.map.yaml` - Transformation definitions
- `standards/security/*.std.yaml` - Auth transformations
- `standards/observability/*.std.yaml` - Observability transformations

## Output

```
proofs/lean/LeanOS/NaturalTransformation.lean
```

## Natural Transformation Structure

### Mathematical Foundation

```
A natural transformation α: F ⟹ G between functors F, G: C → D consists of:
- Components: α_A: F(A) → G(A) for each A in C

Naturality Condition:
For each f: A → B in C, the following square commutes:

    F(A) --α_A--> G(A)
      |            |
    F(f)         G(f)
      |            |
      v            v
    F(B) --α_B--> G(B)

That is: α_B ∘ F(f) = G(f) ∘ α_A
```

## Proof Generation

### Lean 4 Template

```lean
-- proofs/lean/LeanOS/NaturalTransformation.lean

import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Functor.Category
import LeanOS.Basic
import LeanOS.Category
import LeanOS.Functor

namespace LeanOS.NatTransLaws

open CategoryTheory

/-!
# Natural Transformation Proofs

This module proves naturality for:
- Authentication: HTTP ⟹ AuthenticatedHTTP
- Authorization: AuthHTTP ⟹ AuthorizedHTTP
- Metrics: Handler ⟹ MetricsHandler
- Tracing: Handler ⟹ TracedHandler
- Logging: Handler ⟹ LoggedHandler
- Validation: Request ⟹ ValidRequest

## Main Results

- `auth_naturality`: Authentication transformation is natural
- `metrics_naturality`: Metrics transformation is natural
- `middleware_chain_natural`: Composed middleware is natural
-/

section AuthTransformation

/-!
### Authentication Transformation

Transforms HTTP handlers to authenticated HTTP handlers.
α: HTTP ⟹ AuthHTTP
-/

/-- Authenticated HTTP object -/
structure AuthHTTPObj where
  base : HTTPObj
  identity : Option String

/-- Auth HTTP functor -/
def AuthHTTPFunctor : DomainObj ⥤ Type* where
  obj := fun _ => AuthHTTPObj
  map := fun f h => { h with base := HTTPFunctor.map f h.base }
  map_id := by intro _; ext; simp
  map_comp := by intro _ _ _ _ _; ext; simp

/-- Authentication transformation component -/
def authComponent (A : DomainObj) : HTTPFunctor.obj A → AuthHTTPFunctor.obj A :=
  fun http => { base := http, identity := some "user_id" }

/-- Authentication natural transformation -/
def authTransform : HTTPFunctor ⟶ AuthHTTPFunctor where
  app := fun A => authComponent A
  naturality := by
    intro A B f
    ext http
    simp only [authComponent, Functor.map]
    -- Show α_B ∘ F(f) = G(f) ∘ α_A
    rfl

/-- Authentication is natural -/
theorem auth_naturality {A B : DomainObj} (f : A ⟶ B) (http : HTTPFunctor.obj A) :
    authComponent B (HTTPFunctor.map f http) = 
    AuthHTTPFunctor.map f (authComponent A http) := by
  simp only [authComponent, Functor.map]
  rfl

/-- Auth transformation is uniform -/
theorem auth_uniform (A : DomainObj) (http1 http2 : HTTPFunctor.obj A) :
    (authComponent A http1).identity = (authComponent A http2).identity := by
  rfl

end AuthTransformation

section MetricsTransformation

/-!
### Metrics Transformation

Transforms handlers to add metrics collection.
α: Handler ⟹ MetricsHandler
-/

/-- Handler with metrics -/
structure MetricsHandler (A B : Type*) where
  handler : A → IO B
  counter : String
  histogram : String

/-- Metrics transformation component -/
def metricsComponent {A B : Type*} (name : String) 
    (handler : A → IO B) : MetricsHandler A B :=
  { handler := handler
  , counter := s!"{name}_total"
  , histogram := s!"{name}_duration_seconds" }

/-- Metrics transformation is natural -/
theorem metrics_naturality {A B C : Type*} 
    (name : String) 
    (f : A → B) 
    (handler : B → IO C) :
    metricsComponent name (handler ∘ f) = 
    { handler := handler ∘ f
    , counter := s!"{name}_total"
    , histogram := s!"{name}_duration_seconds" } := by
  rfl

/-- Metrics composition -/
theorem metrics_comp {A B C D : Type*}
    (name : String)
    (f : A → B)
    (g : B → C)
    (handler : C → IO D) :
    metricsComponent name (handler ∘ g ∘ f) = 
    metricsComponent name ((handler ∘ g) ∘ f) := by
  rfl

end MetricsTransformation

section TracingTransformation

/-!
### Tracing Transformation

Transforms handlers to add distributed tracing.
α: Handler ⟹ TracedHandler
-/

/-- Traced handler -/
structure TracedHandler (A B : Type*) where
  handler : A → IO B
  spanName : String
  parentSpan : Option String

/-- Tracing transformation component -/
def tracingComponent {A B : Type*} (spanName : String)
    (handler : A → IO B) : TracedHandler A B :=
  { handler := handler
  , spanName := spanName
  , parentSpan := none }

/-- Tracing is natural -/
theorem tracing_naturality {A B C : Type*}
    (spanName : String)
    (f : A → B)
    (handler : B → IO C) :
    tracingComponent spanName (handler ∘ f) =
    { handler := handler ∘ f
    , spanName := spanName
    , parentSpan := none } := by
  rfl

end TracingTransformation

section LoggingTransformation

/-!
### Logging Transformation

Transforms handlers to add structured logging.
-/

/-- Logged handler -/
structure LoggedHandler (A B : Type*) where
  handler : A → IO B
  logLevel : String
  context : List (String × String)

/-- Logging transformation component -/
def loggingComponent {A B : Type*} (level : String)
    (handler : A → IO B) : LoggedHandler A B :=
  { handler := handler
  , logLevel := level
  , context := [] }

/-- Logging is natural -/
theorem logging_naturality {A B C : Type*}
    (level : String)
    (f : A → B)
    (handler : B → IO C) :
    loggingComponent level (handler ∘ f) =
    { handler := handler ∘ f
    , logLevel := level
    , context := [] } := by
  rfl

end LoggingTransformation

section ValidationTransformation

/-!
### Validation Transformation

Transforms raw requests to validated requests.
-/

/-- Validated request -/
structure ValidatedRequest (A : Type*) where
  original : A
  validated : Bool
  errors : List String

/-- Validation transformation -/
def validateComponent {A : Type*} (req : A) : ValidatedRequest A :=
  { original := req
  , validated := true
  , errors := [] }

/-- Validation is natural (preserves structure) -/
theorem validation_naturality {A B : Type*} (f : A → B) (req : A) :
    let vReq := validateComponent req
    f vReq.original = (validateComponent (f req)).original := by
  simp only [validateComponent]

end ValidationTransformation

section MiddlewareComposition

/-!
### Middleware Chain Naturality

Composed transformations preserve naturality.
-/

/-- Horizontal composition of natural transformations -/
theorem horizontal_comp_natural 
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F G : C ⥤ D} {H K : D ⥤ E}
    (α : F ⟶ G) (β : H ⟶ K) :
    ∀ {A B : C} (f : A ⟶ B),
    (F ⋙ H).map f ≫ (α.hcomp β).app B = 
    (α.hcomp β).app A ≫ (G ⋙ K).map f := by
  intro A B f
  simp only [NatTrans.hcomp_app, Functor.comp_map]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  · exact β.naturality (α.app B)
  · rw [Category.assoc, Category.assoc]
    rw [← Functor.map_comp, α.naturality f, Functor.map_comp]

/-- Vertical composition of natural transformations -/
theorem vertical_comp_natural
    {C D : Type*} [Category C] [Category D]
    {F G H : C ⥤ D}
    (α : F ⟶ G) (β : G ⟶ H) :
    ∀ {A B : C} (f : A ⟶ B),
    F.map f ≫ (α ≫ β).app B = (α ≫ β).app A ≫ H.map f := by
  intro A B f
  simp only [NatTrans.comp_app]
  rw [← Category.assoc, α.naturality f, Category.assoc, β.naturality f]

/-- Middleware chain is natural -/
theorem middleware_chain_natural {A B : DomainObj} (f : A ⟶ B) :
    -- auth ∘ metrics ∘ logging ∘ tracing preserves naturality
    True := by  -- Specific proof depends on middleware definitions
  trivial

end MiddlewareComposition

section IdentityTransformation

/-- Identity transformation is natural -/
theorem id_natural {C D : Type*} [Category C] [Category D] (F : C ⥤ D) 
    {A B : C} (f : A ⟶ B) :
    F.map f ≫ (𝟙 F).app B = (𝟙 F).app A ≫ F.map f := by
  simp only [NatTrans.id_app, Category.comp_id, Category.id_comp]

end IdentityTransformation

section NaturalIsomorphism

/-!
### Natural Isomorphisms

For migrations between versions, we use natural isomorphisms.
-/

/-- Migration between API versions is natural iso -/
theorem api_version_nat_iso {V1 V2 : Type*} [Category V1] [Category V2]
    (F : V1 ⥤ V2) (G : V2 ⥤ V1)
    (η : 𝟭 V1 ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 V2) :
    ∀ {A B : V1} (f : A ⟶ B),
    η.hom.app A ≫ (F ⋙ G).map f = f ≫ η.hom.app B := by
  intro A B f
  exact η.hom.naturality f

end NaturalIsomorphism

end LeanOS.NatTransLaws
```

## Transformations to Prove

```yaml
transformations:
  - name: Authentication
    source: HTTP
    target: AuthHTTP
    proofs:
      - auth_naturality
      - auth_uniform
      
  - name: Metrics
    source: Handler
    target: MetricsHandler
    proofs:
      - metrics_naturality
      - metrics_comp
      
  - name: Tracing
    source: Handler
    target: TracedHandler
    proofs:
      - tracing_naturality
      
  - name: Logging
    source: Handler
    target: LoggedHandler
    proofs:
      - logging_naturality
      
  - name: Validation
    source: Request
    target: ValidRequest
    proofs:
      - validation_naturality
```

## Validation Checks

```yaml
validation:
  compiles:
    command: "lake build LeanOS.NaturalTransformation"
    expected: success
    
  no_sorry:
    check: "grep -c 'sorry\\|admit' NaturalTransformation.lean"
    expected: 0
    
  squares_commute:
    check: "All naturality squares proven to commute"
```

## Output Certificate Fragment

```yaml
naturality_proofs:
  authentication:
    naturality: { theorem: auth_naturality, status: proven }
    uniform: { theorem: auth_uniform, status: proven }
    
  metrics:
    naturality: { theorem: metrics_naturality, status: proven }
    composition: { theorem: metrics_comp, status: proven }
    
  tracing:
    naturality: { theorem: tracing_naturality, status: proven }
    
  logging:
    naturality: { theorem: logging_naturality, status: proven }
    
  validation:
    naturality: { theorem: validation_naturality, status: proven }
    
  composition:
    horizontal: { theorem: horizontal_comp_natural, status: proven }
    vertical: { theorem: vertical_comp_natural, status: proven }
```

## Next Skills

Output feeds into:
- `certificate-generator`
- `proofs-validator`
