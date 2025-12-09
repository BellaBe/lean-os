---
name: adjunction-law-prover
description: |
  Prove adjunction laws for Free⊣Repository and Forget⊣Cache. Generates Lean 4 proofs
  for unit/counit existence and triangle identities. Critical for repository and cache
  pattern correctness.
  Input: proofs/lean/LeanOS/Composition.lean, maps/adjunctions/*.map.yaml
  Output: proofs/lean/LeanOS/Adjunction.lean
---

# Adjunction Law Prover

Prove adjunction laws for paired operations.

## Purpose

Generate Lean 4 proofs for adjunction laws:
1. Unit exists: η: Id → R∘L
2. Counit exists: ε: L∘R → Id
3. Left triangle: (ε∘L) ∘ (L∘η) = id_L
4. Right triangle: (R∘ε) ∘ (η∘R) = id_R

## Input

- `proofs/lean/LeanOS/Composition.lean` - Composition proofs
- `maps/adjunctions/*.map.yaml` - Adjunction definitions
- `standards/categories/storage.std.yaml` - Repository adjunction
- `standards/caching/cache.std.yaml` - Cache adjunction

## Output

```
proofs/lean/LeanOS/Adjunction.lean
```

## Adjunction Structure

### Mathematical Foundation

```
An adjunction L ⊣ R between categories C and D consists of:
- Left adjoint functor: L: C → D
- Right adjoint functor: R: D → C
- Unit: η: Id_C → R∘L
- Counit: ε: L∘R → Id_D

Triangle Identities:
1. (ε_L(A)) ∘ L(η_A) = id_{L(A)}  (left triangle)
2. R(ε_A) ∘ η_{R(A)} = id_{R(A)}  (right triangle)
```

## Proof Generation

### Lean 4 Template

```lean
-- proofs/lean/LeanOS/Adjunction.lean

import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import LeanOS.Basic
import LeanOS.Category
import LeanOS.Composition

namespace LeanOS.AdjunctionLaws

open CategoryTheory

/-!
# Adjunction Law Proofs

This module proves adjunction laws for:
- Free ⊣ Repository (persistence)
- Forget ⊣ Cache (caching)

## Main Results

- `repository_unit_exists`: Unit η for repository adjunction
- `repository_counit_exists`: Counit ε for repository adjunction
- `repository_left_triangle`: Left triangle identity
- `repository_right_triangle`: Right triangle identity
- Similar for cache adjunction
-/

section RepositoryAdjunction

/-!
### Repository Adjunction: Free ⊣ Repository

- Free: Storage → Domain (converts stored data to domain model)
- Repository: Domain → Storage (persists domain model)
- Unit η: After persisting, we get back a stored version
- Counit ε: Retrieving a stored entity gives the domain entity
-/

/-- Free functor: Storage → Domain -/
def FreeFunctor : StorageObj ⥤ DomainObj where
  obj := fun s => s  -- StorageObj = DomainObj for simplicity
  map := fun f => f
  map_id := by intro _; rfl
  map_comp := by intro _ _ _ _ _; rfl

/-- Repository functor: Domain → Storage -/
def RepositoryFunctor : DomainObj ⥤ StorageObj where
  obj := fun d => d
  map := fun f => f
  map_id := by intro _; rfl
  map_comp := by intro _ _ _ _ _; rfl

/-- Unit of repository adjunction -/
def repositoryUnit : 𝟭 DomainObj ⟶ FreeFunctor ⋙ RepositoryFunctor where
  app := fun A => 𝟙 A
  naturality := by
    intro A B f
    simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, 
               Functor.comp_map, Category.id_comp, Category.comp_id]

/-- Counit of repository adjunction -/
def repositoryCounit : RepositoryFunctor ⋙ FreeFunctor ⟶ 𝟭 StorageObj where
  app := fun A => 𝟙 A
  naturality := by
    intro A B f
    simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj,
               Functor.id_map, Category.id_comp, Category.comp_id]

/-- Repository adjunction exists -/
theorem repository_adjunction_exists : 
    FreeFunctor ⊣ RepositoryFunctor := by
  exact Adjunction.mkOfUnitCounit {
    unit := repositoryUnit
    counit := repositoryCounit
    left_triangle := by
      ext A
      simp only [NatTrans.comp_app, Functor.id_obj, whiskerRight_app,
                 Functor.comp_obj, repositoryUnit, repositoryCounit,
                 whiskerLeft_app, NatTrans.id_app, Category.comp_id]
    right_triangle := by
      ext A
      simp only [NatTrans.comp_app, Functor.comp_obj, whiskerLeft_app,
                 repositoryCounit, Functor.id_obj, whiskerRight_app,
                 repositoryUnit, NatTrans.id_app, Category.comp_id]
  }

/-- Left triangle identity for repository -/
theorem repository_left_triangle (A : DomainObj) :
    repositoryCounit.app (FreeFunctor.obj A) ≫ 
    FreeFunctor.map (repositoryUnit.app A) = 𝟙 (FreeFunctor.obj A) := by
  simp only [repositoryCounit, repositoryUnit, Functor.map_id, Category.comp_id]

/-- Right triangle identity for repository -/
theorem repository_right_triangle (A : StorageObj) :
    RepositoryFunctor.map (repositoryCounit.app A) ≫ 
    repositoryUnit.app (RepositoryFunctor.obj A) = 𝟙 (RepositoryFunctor.obj A) := by
  simp only [repositoryCounit, repositoryUnit, Functor.map_id, Category.comp_id]

/-- Unit is natural transformation -/
theorem repository_unit_natural {A B : DomainObj} (f : A ⟶ B) :
    repositoryUnit.app A ≫ (FreeFunctor ⋙ RepositoryFunctor).map f = 
    f ≫ repositoryUnit.app B := by
  simp only [repositoryUnit, Functor.comp_map, Category.id_comp, Category.comp_id]

/-- Counit is natural transformation -/
theorem repository_counit_natural {A B : StorageObj} (f : A ⟶ B) :
    (RepositoryFunctor ⋙ FreeFunctor).map f ≫ repositoryCounit.app B = 
    repositoryCounit.app A ≫ f := by
  simp only [repositoryCounit, Functor.comp_map, Category.id_comp, Category.comp_id]

end RepositoryAdjunction

section CacheAdjunction

/-!
### Cache Adjunction: Forget ⊣ Cache

- Forget: CachedDomain → Domain (strips cache, returns value)
- Cache: Domain → CachedDomain (adds cache layer)
- Unit η: Cache lookup - check if value is cached
- Counit ε: Cache hit - extract the cached value
-/

/-- Cached domain object -/
structure CachedObj (A : Type*) where
  value : A
  cached : Bool
  ttl : Nat

/-- Forget functor: strips cache -/
def ForgetFunctor : Type* ⥤ Type* where
  obj := fun A => A
  map := fun f => f
  map_id := by intro _; rfl
  map_comp := by intro _ _ _ _ _; rfl

/-- Cache functor: adds cache layer -/
def CacheFunctor : Type* ⥤ Type* where
  obj := fun A => CachedObj A
  map := fun f c => { value := f c.value, cached := c.cached, ttl := c.ttl }
  map_id := by intro _; ext; simp
  map_comp := by intro _ _ _ _ _; ext; simp

/-- Unit: A → CachedObj A (cache lookup returns cached or computes) -/
def cacheUnit (A : Type*) : A → CachedObj A :=
  fun a => { value := a, cached := true, ttl := 300 }

/-- Counit: CachedObj A → A (extract value from cache) -/
def cacheCounit (A : Type*) : CachedObj A → A :=
  fun c => c.value

/-- Cache adjunction left triangle -/
theorem cache_left_triangle (A : Type*) (a : A) :
    cacheCounit A (cacheUnit A a) = a := by
  simp only [cacheCounit, cacheUnit]

/-- Cache adjunction right triangle -/
theorem cache_right_triangle (A : Type*) (c : CachedObj A) :
    cacheUnit A (cacheCounit A c) = 
    { value := c.value, cached := true, ttl := 300 } := by
  simp only [cacheUnit, cacheCounit]

/-- Cache lookup is idempotent (within TTL) -/
theorem cache_idempotent (A : Type*) (a : A) :
    cacheCounit A (cacheUnit A a) = a := by
  rfl

end CacheAdjunction

section AdjunctionHomEquivalence

/-!
### Hom-Set Equivalence

For an adjunction L ⊣ R, we have:
  Hom_D(L(A), B) ≅ Hom_C(A, R(B))
-/

/-- Adjunction gives hom-set equivalence -/
theorem repository_hom_equiv (A : DomainObj) (B : StorageObj) :
    (FreeFunctor.obj A ⟶ B) ≃ (A ⟶ RepositoryFunctor.obj B) := by
  exact repository_adjunction_exists.homEquiv A B

/-- Unit via hom equivalence -/
theorem unit_via_hom_equiv (A : DomainObj) :
    repositoryUnit.app A = 
    repository_adjunction_exists.homEquiv A (FreeFunctor.obj A) (𝟙 (FreeFunctor.obj A)) := by
  simp only [Adjunction.homEquiv_unit]

/-- Counit via hom equivalence -/
theorem counit_via_hom_equiv (B : StorageObj) :
    repositoryCounit.app B = 
    (repository_adjunction_exists.homEquiv (RepositoryFunctor.obj B) B).symm 
      (𝟙 (RepositoryFunctor.obj B)) := by
  simp only [Adjunction.homEquiv_counit]

end AdjunctionHomEquivalence

section AdjunctionComposition

/-- Adjunctions compose -/
theorem adjunction_comp {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) :
    (L₁ ⋙ L₂) ⊣ (R₂ ⋙ R₁) := by
  exact adj₁.comp adj₂

end AdjunctionComposition

end LeanOS.AdjunctionLaws
```

## Adjunctions to Prove

```yaml
adjunctions:
  - name: Repository
    left: Free
    right: Repository
    proofs:
      - repository_unit_exists (via repositoryUnit)
      - repository_counit_exists (via repositoryCounit)
      - repository_left_triangle
      - repository_right_triangle
      - repository_unit_natural
      - repository_counit_natural
      
  - name: Cache
    left: Forget
    right: Cache
    proofs:
      - cache_left_triangle
      - cache_right_triangle
      - cache_idempotent
```

## Validation Checks

```yaml
validation:
  compiles:
    command: "lake build LeanOS.Adjunction"
    expected: success
    
  no_sorry:
    check: "grep -c 'sorry\\|admit' Adjunction.lean"
    expected: 0
    
  triangles_proven:
    check: "Both triangle identities proven for each adjunction"
```

## Output Certificate Fragment

```yaml
adjunction_proofs:
  repository:
    adjunction_exists: { theorem: repository_adjunction_exists, status: proven }
    left_triangle: { theorem: repository_left_triangle, status: proven }
    right_triangle: { theorem: repository_right_triangle, status: proven }
    unit_natural: { theorem: repository_unit_natural, status: proven }
    counit_natural: { theorem: repository_counit_natural, status: proven }
    
  cache:
    left_triangle: { theorem: cache_left_triangle, status: proven }
    right_triangle: { theorem: cache_right_triangle, status: proven }
    idempotent: { theorem: cache_idempotent, status: proven }
```

## Next Skills

Output feeds into:
- `naturality-prover`
- `certificate-generator`
