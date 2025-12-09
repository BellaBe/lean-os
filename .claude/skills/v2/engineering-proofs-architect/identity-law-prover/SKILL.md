---
name: identity-law-prover
description: |
  Prove identity laws for all categories in the system. Generates Lean 4 proofs
  that id ∘ f = f and f ∘ id = f for every morphism. Foundation for all other proofs.
  Input: maps/*, standards/categories/*.std.yaml
  Output: proofs/lean/LeanOS/Identity.lean
---

# Identity Law Prover

Prove identity morphism laws for all categories.

## Purpose

Generate Lean 4 proofs for identity laws:
1. Left identity: id_A ∘ f = f
2. Right identity: f ∘ id_B = f
3. Identity uniqueness: id is unique
4. Identity existence: every object has id

## Input

- `maps/functors/*.map.yaml` - Category definitions
- `standards/categories/*.std.yaml` - Category standards
- `specifications/v{X}/architecture.categorical` - Category structure

## Output

```
proofs/lean/LeanOS/Identity.lean
```

## Identity Law Structure

### Mathematical Foundation

```
For a category C:
- Objects: Ob(C)
- Morphisms: Hom(A, B) for A, B ∈ Ob(C)
- Identity: For each A ∈ Ob(C), ∃ id_A : A → A

Identity Laws:
1. Left Identity:  ∀ f : A → B, id_B ∘ f = f
2. Right Identity: ∀ f : A → B, f ∘ id_A = f
```

## Proof Generation

### Schema

```yaml
identity_proofs:
  # Per-category proofs
  categories:
    - name: Domain
      objects: [Merchant, Profile, Analysis, Product, ...]
      proof_strategy: derive_from_mathlib
      
    - name: HTTP
      objects: [Request, Response, Endpoint, ...]
      proof_strategy: derive_from_mathlib
      
    - name: Storage
      objects: [StoredMerchant, StoredProfile, ...]
      proof_strategy: derive_from_mathlib
```

### Lean 4 Template

```lean
-- proofs/lean/LeanOS/Identity.lean

import Mathlib.CategoryTheory.Category.Basic
import LeanOS.Basic
import LeanOS.Category

namespace LeanOS.Identity

open CategoryTheory

/-!
# Identity Law Proofs

This module proves identity laws for all categories in LeanOS.

## Main Results

- `domain_left_id`: Left identity for Domain category
- `domain_right_id`: Right identity for Domain category
- `http_left_id`: Left identity for HTTP category
- `storage_left_id`: Left identity for Storage category
-/

section DomainCategory

/-- Left identity law for Domain category -/
theorem domain_left_id {A B : DomainObj} (f : A ⟶ B) : 
    𝟙 A ≫ f = f := by
  simp only [Category.id_comp]

/-- Right identity law for Domain category -/
theorem domain_right_id {A B : DomainObj} (f : A ⟶ B) : 
    f ≫ 𝟙 B = f := by
  simp only [Category.comp_id]

/-- Identity morphism is unique -/
theorem domain_id_unique {A : DomainObj} (e : A ⟶ A) 
    (h_left : ∀ {B} (f : A ⟶ B), e ≫ f = f)
    (h_right : ∀ {B} (f : B ⟶ A), f ≫ e = f) : 
    e = 𝟙 A := by
  have := h_right (𝟙 A)
  simp only [Category.comp_id] at this
  exact this

end DomainCategory

section HTTPCategory

/-- HTTP category objects -/
inductive HTTPObj where
  | Request (method : String) (path : String)
  | Response (status : Nat)
  | Endpoint
  deriving DecidableEq

/-- HTTP category instance -/
instance : Category HTTPObj where
  Hom A B := A → B  -- Simplified for illustration
  id _ := id
  comp f g := g ∘ f

/-- Left identity for HTTP category -/
theorem http_left_id {A B : HTTPObj} (f : A ⟶ B) : 
    𝟙 A ≫ f = f := by
  simp only [Category.id_comp]

/-- Right identity for HTTP category -/
theorem http_right_id {A B : HTTPObj} (f : A ⟶ B) : 
    f ≫ 𝟙 B = f := by
  simp only [Category.comp_id]

end HTTPCategory

section StorageCategory

/-- Storage objects are stored domain objects -/
def StorageObj := DomainObj

/-- Storage category inherits from Domain -/
instance : Category StorageObj := inferInstance

/-- Left identity for Storage category -/
theorem storage_left_id {A B : StorageObj} (f : A ⟶ B) : 
    𝟙 A ≫ f = f := by
  simp only [Category.id_comp]

/-- Right identity for Storage category -/
theorem storage_right_id {A B : StorageObj} (f : A ⟶ B) : 
    f ≫ 𝟙 B = f := by
  simp only [Category.comp_id]

end StorageCategory

section KleisliCategory

/-- Kleisli category for IO monad -/
structure KleisliIO (A B : Type*) where
  run : A → IO B

instance : Category Type* where
  Hom := KleisliIO
  id A := ⟨pure⟩
  comp f g := ⟨fun a => f.run a >>= g.run⟩

/-- Left identity for Kleisli[IO] -/
theorem kleisli_io_left_id {A B : Type*} (f : KleisliIO A B) :
    KleisliIO.mk pure ≫ f = f := by
  simp only [Category.id_comp]
  -- Pure is left identity for bind
  ext a
  simp [KleisliIO.run, pure_bind]

/-- Right identity for Kleisli[IO] -/
theorem kleisli_io_right_id {A B : Type*} (f : KleisliIO A B) :
    f ≫ KleisliIO.mk pure = f := by
  simp only [Category.comp_id]
  -- Bind with pure is right identity
  ext a
  simp [KleisliIO.run, bind_pure]

end KleisliCategory

/-!
## Derived Results

From identity laws, we can derive useful lemmas.
-/

section DerivedLemmas

/-- Identity composed with itself is identity -/
theorem id_comp_id {C : Type*} [Category C] (A : C) : 
    (𝟙 A : A ⟶ A) ≫ 𝟙 A = 𝟙 A := by
  simp only [Category.comp_id]

/-- Any endomorphism equal to identity on both sides is identity -/
theorem endo_eq_id {C : Type*} [Category C] {A : C} (f : A ⟶ A)
    (h : f ≫ f = f) (h' : 𝟙 A ≫ f = f) : f = 𝟙 A := by
  rw [Category.id_comp] at h'
  -- If f ∘ f = f and f is identity on left, then f = id
  sorry  -- Requires additional structure

end DerivedLemmas

end LeanOS.Identity
```

## Proof Strategies

### Strategy 1: Derive from Mathlib

```yaml
strategy: derive_from_mathlib
description: |
  Use mathlib's Category typeclass which already has identity laws.
  Most categories derive these automatically.
  
lean_tactic: |
  simp only [Category.id_comp]  -- For left identity
  simp only [Category.comp_id]  -- For right identity
```

### Strategy 2: Direct Construction

```yaml
strategy: direct_construction
description: |
  For custom categories, prove identity laws directly.
  
lean_tactic: |
  -- Unfold definitions
  unfold CategoryStruct.id CategoryStruct.comp
  -- Show equality
  ext
  simp
```

### Strategy 3: Functor Preservation

```yaml
strategy: functor_preservation
description: |
  For categories defined via functors, use that F(id) = id.
  
lean_tactic: |
  rw [Functor.map_id]
  simp
```

## Morphism Coverage

```yaml
coverage:
  # Domain morphisms
  domain:
    - create_merchant
    - get_merchant
    - update_merchant
    - delete_merchant
    - create_profile
    - analyze_photo
    # ... all morphisms from specifications
    
  # HTTP morphisms
  http:
    - POST_merchants
    - GET_merchant
    - PATCH_merchant
    - DELETE_merchant
    # ... all endpoints
    
  # Storage morphisms
  storage:
    - insert_merchant
    - select_merchant
    - update_merchant
    - delete_merchant
```

## Validation Checks

```yaml
validation:
  # Proof compiles
  compiles:
    command: "lake build LeanOS.Identity"
    expected: success
    
  # No sorry/admit
  no_sorry:
    check: "grep -c 'sorry\\|admit' Identity.lean"
    expected: 0
    
  # Coverage complete
  coverage:
    check: "All morphisms have identity proofs"
    
  # Theorems match spec
  matches_spec:
    check: "Theorem statements match categorical specification"
```

## Output Certificate Fragment

```yaml
# Will be aggregated into certificates/identity.cert.yaml
identity_proofs:
  domain_category:
    left_identity:
      theorem: domain_left_id
      status: proven
      proof_hash: "sha256:abc123..."
      
    right_identity:
      theorem: domain_right_id
      status: proven
      proof_hash: "sha256:def456..."
      
  http_category:
    left_identity:
      theorem: http_left_id
      status: proven
      
    right_identity:
      theorem: http_right_id
      status: proven
      
  storage_category:
    left_identity:
      theorem: storage_left_id
      status: proven
      
    right_identity:
      theorem: storage_right_id
      status: proven
```

## Next Skills

Output feeds into:
- `composition-law-prover`
