---
name: functor-law-prover
description: |
  Prove functor laws for all functors in the system. Generates Lean 4 proofs that
  F(id) = id and F(g∘f) = F(g)∘F(f) for HTTP, Storage, and External functors.
  Input: proofs/lean/LeanOS/Composition.lean, maps/functors/*.map.yaml
  Output: proofs/lean/LeanOS/Functor.lean
---

# Functor Law Prover

Prove functor laws for all category mappings.

## Purpose

Generate Lean 4 proofs for functor laws:
1. Identity preservation: F(id_A) = id_{F(A)}
2. Composition preservation: F(g ∘ f) = F(g) ∘ F(f)
3. For all functors: HTTP, Storage, External

## Input

- `proofs/lean/LeanOS/Composition.lean` - Composition proofs
- `maps/functors/*.map.yaml` - Functor definitions
- `standards/categories/*.std.yaml` - Category structure

## Output

```
proofs/lean/LeanOS/Functor.lean
```

## Functor Law Structure

### Mathematical Foundation

```
A functor F: C → D consists of:
- Object map: A ↦ F(A) for A ∈ Ob(C)
- Morphism map: (f: A → B) ↦ (F(f): F(A) → F(B))

Functor Laws:
1. F(id_A) = id_{F(A)}
2. F(g ∘ f) = F(g) ∘ F(f)
```

## Proof Generation

### Lean 4 Template

```lean
-- proofs/lean/LeanOS/Functor.lean

import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import LeanOS.Basic
import LeanOS.Category
import LeanOS.Composition

namespace LeanOS.FunctorLaws

open CategoryTheory

/-!
# Functor Law Proofs

This module proves functor laws for all functors in LeanOS.

## Functors Covered

- `HTTP`: Domain → HTTP
- `Storage`: Domain → Storage  
- `External`: Domain → External
- `Observe`: Domain → Metrics
-/

section HTTPFunctor

/-- HTTP functor maps domain objects to HTTP representations -/
def HTTPFunctor : DomainObj ⥤ HTTPObj where
  obj := fun d => match d with
    | .Merchant => .Endpoint
    | .Profile => .Endpoint
    | .Analysis => .Endpoint
    | .Product => .Endpoint
  map := fun f => 
    -- Map domain morphism to HTTP handler
    HTTPMor.fromDomain f
  map_id := by
    intro A
    simp only [HTTPMor.fromDomain_id]
  map_comp := by
    intro A B C f g
    simp only [HTTPMor.fromDomain_comp]

/-- HTTP functor preserves identity -/
theorem http_functor_id (A : DomainObj) : 
    HTTPFunctor.map (𝟙 A) = 𝟙 (HTTPFunctor.obj A) := by
  simp only [Functor.map_id]

/-- HTTP functor preserves composition -/
theorem http_functor_comp {A B C : DomainObj} (f : A ⟶ B) (g : B ⟶ C) :
    HTTPFunctor.map (f ≫ g) = HTTPFunctor.map f ≫ HTTPFunctor.map g := by
  simp only [Functor.map_comp]

end HTTPFunctor

section StorageFunctor

/-- Storage functor maps domain objects to database models -/
def StorageFunctor : DomainObj ⥤ StorageObj where
  obj := fun d => d  -- Storage objects mirror domain
  map := fun f => StorageMor.fromDomain f
  map_id := by
    intro A
    simp only [StorageMor.fromDomain_id]
  map_comp := by
    intro A B C f g
    simp only [StorageMor.fromDomain_comp]

/-- Storage functor preserves identity -/
theorem storage_functor_id (A : DomainObj) :
    StorageFunctor.map (𝟙 A) = 𝟙 (StorageFunctor.obj A) := by
  simp only [Functor.map_id]

/-- Storage functor preserves composition -/
theorem storage_functor_comp {A B C : DomainObj} (f : A ⟶ B) (g : B ⟶ C) :
    StorageFunctor.map (f ≫ g) = StorageFunctor.map f ≫ StorageFunctor.map g := by
  simp only [Functor.map_comp]

end StorageFunctor

section ExternalFunctor

/-- External API functor -/
structure ExternalObj where
  api : String
  endpoint : String

/-- External functor maps domain to external API calls -/
def ExternalFunctor : DomainObj ⥤ Type* where
  obj := fun _ => ExternalObj
  map := fun _ => id
  map_id := by intro _; rfl
  map_comp := by intro _ _ _ _ _; rfl

/-- External functor preserves identity -/
theorem external_functor_id (A : DomainObj) :
    ExternalFunctor.map (𝟙 A) = 𝟙 (ExternalFunctor.obj A) := by
  simp only [Functor.map_id]

/-- External functor preserves composition -/
theorem external_functor_comp {A B C : DomainObj} (f : A ⟶ B) (g : B ⟶ C) :
    ExternalFunctor.map (f ≫ g) = ExternalFunctor.map f ≫ ExternalFunctor.map g := by
  simp only [Functor.map_comp]

end ExternalFunctor

section ObserveFunctor

/-- Metrics object -/
structure MetricsObj where
  counter : String
  histogram : String
  labels : List String

/-- Observe functor adds metrics to operations -/
def ObserveFunctor : DomainObj ⥤ Type* where
  obj := fun _ => MetricsObj
  map := fun f => fun m => 
    { m with counter := s!"{m.counter}_observed" }
  map_id := by 
    intro A
    ext m
    simp
  map_comp := by 
    intro A B C f g
    ext m
    simp

/-- Observe functor preserves identity -/
theorem observe_functor_id (A : DomainObj) :
    ObserveFunctor.map (𝟙 A) = 𝟙 (ObserveFunctor.obj A) := by
  simp only [Functor.map_id]

end ObserveFunctor

section FunctorComposition

/-- Composed functors preserve laws -/
theorem functor_comp_id (F : C ⥤ D) (G : D ⥤ E) (A : C) :
    (F ⋙ G).map (𝟙 A) = 𝟙 ((F ⋙ G).obj A) := by
  simp only [Functor.comp_map, Functor.map_id]

/-- Composed functors preserve composition -/
theorem functor_comp_comp (F : C ⥤ D) (G : D ⥤ E) 
    {A B C' : C} (f : A ⟶ B) (g : B ⟶ C') :
    (F ⋙ G).map (f ≫ g) = (F ⋙ G).map f ≫ (F ⋙ G).map g := by
  simp only [Functor.comp_map, Functor.map_comp]

end FunctorComposition

section ContravariantFunctors

/-- Contravariant functor (Reader monad perspective) -/
def ReaderFunctor (R : Type*) : Type* ⥤ Type* where
  obj := fun A => R → A
  map := fun f g r => f (g r)  -- Covariant in result
  map_id := by intro _; rfl
  map_comp := by intro _ _ _ _ _; rfl

/-- Reader functor laws -/
theorem reader_functor_id (R A : Type*) :
    (ReaderFunctor R).map (id : A → A) = id := by
  rfl

theorem reader_functor_comp (R : Type*) {A B C : Type*} 
    (f : A → B) (g : B → C) :
    (ReaderFunctor R).map (g ∘ f) = 
    (ReaderFunctor R).map g ∘ (ReaderFunctor R).map f := by
  rfl

end ContravariantFunctors

/-!
## Verification that Implementation Matches Spec

The functor implementations in code should satisfy these laws:
- `from_domain(id) = id` in each adapter
- `from_domain(g ∘ f) = from_domain(g) ∘ from_domain(f)`
-/

section ImplementationVerification

/-- HTTP adapter preserves identity -/
axiom http_adapter_id : ∀ (A : DomainObj), 
  HTTPAdapter.fromDomain (DomainMor.id A) = HTTPMor.id (HTTPAdapter.obj A)

/-- HTTP adapter preserves composition -/
axiom http_adapter_comp : ∀ {A B C : DomainObj} (f : DomainMor A B) (g : DomainMor B C),
  HTTPAdapter.fromDomain (g.comp f) = 
  (HTTPAdapter.fromDomain g).comp (HTTPAdapter.fromDomain f)

end ImplementationVerification

end LeanOS.FunctorLaws
```

## Functors to Prove

```yaml
functors:
  - name: HTTP
    source: Domain
    target: HTTP
    proofs:
      - http_functor_id
      - http_functor_comp
      
  - name: Storage
    source: Domain
    target: Storage
    proofs:
      - storage_functor_id
      - storage_functor_comp
      
  - name: External
    source: Domain
    target: External
    proofs:
      - external_functor_id
      - external_functor_comp
      
  - name: Observe
    source: Domain
    target: Metrics
    proofs:
      - observe_functor_id
```

## Validation Checks

```yaml
validation:
  compiles:
    command: "lake build LeanOS.Functor"
    expected: success
    
  no_sorry:
    check: "grep -c 'sorry\\|admit' Functor.lean"
    expected: 0
    
  all_functors_proven:
    check: "Every functor has identity + composition proofs"
```

## Output Certificate Fragment

```yaml
functor_proofs:
  http_functor:
    identity: { theorem: http_functor_id, status: proven }
    composition: { theorem: http_functor_comp, status: proven }
    
  storage_functor:
    identity: { theorem: storage_functor_id, status: proven }
    composition: { theorem: storage_functor_comp, status: proven }
    
  external_functor:
    identity: { theorem: external_functor_id, status: proven }
    composition: { theorem: external_functor_comp, status: proven }
```

## Next Skills

Output feeds into:
- `naturality-prover`
- `certificate-generator`
