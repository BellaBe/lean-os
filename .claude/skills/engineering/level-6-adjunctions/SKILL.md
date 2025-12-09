---
name: level-6-adjunctions
description: |
  Level 6: Adjunctions. Paired functors with unit and counit natural
  transformations satisfying triangle identities. Adjunctions capture
  "optimal" translations between categories.
  
  Input: level-5.manifest.yaml
  Output: level-6.manifest.yaml + adjunction definitions
  
  UNIVERSAL: Works for any domain. Examples are illustrative only.
---

# Level 6: Adjunctions

Paired functors with optimal translation properties.

## Principle

An adjunction L ⊣ R consists of:
- Left functor L: C → D
- Right functor R: D → C
- Unit η: Id_C → R ∘ L
- Counit ε: L ∘ R → Id_D
- Triangle identities

```
Adjunction L ⊣ R:

     L
  C ⇄ D
     R

Unit:   η_A: A → R(L(A))        "embed then forget"
Counit: ε_B: L(R(B)) → B        "forget then embed"

Triangle identities:
  (ε ∘ L) ∘ (L ∘ η) = id_L      "L triangle"
  (R ∘ ε) ∘ (η ∘ R) = id_R      "R triangle"
```

## Standard Adjunctions

Common adjunctions in system architecture:

```yaml
standard_adjunctions:
  Free_Repository:
    left: "Free"
    right: "Repository"
    description: "Free ⊣ Repository - database persistence"
    unit: "Save entity, get stored version"
    counit: "Load stored, get entity"
    
  Forget_Cache:
    left: "Forget"
    right: "Cache"
    description: "Forget ⊣ Cache - caching layer"
    unit: "Check cache before compute"
    counit: "Invalidate stale cache"
    
  Domain_External:
    left: "ToExternal"
    right: "FromExternal"
    description: "Domain ⊣ External - API integration"
    unit: "Call API, get domain result"
    counit: "Convert external to domain"
```

## Process

```yaml
process:
  step_1_load_inputs:
    inputs:
      - "level-5.manifest.yaml"   # Functors
    action: "Load and validate inputs exist"
    
  step_2_identify_adjunctions:
    action: "Find adjoint pairs among functors"
    algorithm: |
      adjunctions = []
      for L in level_5.functors:
          for R in level_5.functors:
              if L.target == R.source and R.target == L.source:
                  if specification.defines_adjunction(L, R):
                      adjunctions.append(Adjunction(L, R))
      return adjunctions
    
  step_3_define_unit:
    action: "Define unit natural transformation for each adjunction"
    for_each: "adjunction in adjunctions"
    definition: |
      η: Id_C → R ∘ L
      For each A in C:
        η_A: A → R(L(A))
        
  step_4_define_counit:
    action: "Define counit natural transformation for each adjunction"
    for_each: "adjunction in adjunctions"
    definition: |
      ε: L ∘ R → Id_D
      For each B in D:
        ε_B: L(R(B)) → B
        
  step_5_validate_triangles:
    action: "Verify triangle identities"
    checks:
      left_triangle: "(ε_L(A)) ∘ L(η_A) = id_{L(A)}"
      right_triangle: "R(ε_B) ∘ (η_{R(B)}) = id_{R(B)}"
    critical: "Triangle identities must hold"
    
  step_6_produce_manifest:
    action: "Write level-6.manifest.yaml"
```

## Adjunction Structure

```yaml
adjunction_pattern:
  name: "{Left} ⊣ {Right}"
  
  left:
    functor: "{LeftFunctor}"
    ref: "level-5.functor.{LeftFunctor}"
    
  right:
    functor: "{RightFunctor}"
    ref: "level-5.functor.{RightFunctor}"
    
  unit:
    name: "η"
    type: "Id → R ∘ L"
    components:
      - object: "A"
        morphism: "η_A: A → R(L(A))"
    # One component per object in source category
    
  counit:
    name: "ε"
    type: "L ∘ R → Id"
    components:
      - object: "B"
        morphism: "ε_B: L(R(B)) → B"
    # One component per object in target category
    
  triangles:
    left:
      statement: "(ε ∘ L) ∘ (L ∘ η) = id_L"
      proof_obligation: "level-8.proof.adjunction.{name}.left_triangle"
    right:
      statement: "(R ∘ ε) ∘ (η ∘ R) = id_R"
      proof_obligation: "level-8.proof.adjunction.{name}.right_triangle"
```

## Manifest Item Schema

Each adjunction in the manifest:

```yaml
adjunction_item:
  id: "adjunction.{Left}_{Right}"
  name: "{Left} ⊣ {Right}"
  kind: "adjunction"
  traces:
    - ref: "level-5.functor.{Left}"
      role: "left_adjoint"
    - ref: "level-5.functor.{Right}"
      role: "right_adjoint"
  definition:
    left: "{Left}"
    right: "{Right}"
    unit:
      components:
        - {object: "A", morphism: "η_A: A → R(L(A))"}
        # All unit components
    counit:
      components:
        - {object: "B", morphism: "ε_B: L(R(B)) → B"}
        # All counit components
  triangles:
    left: {verified: pending, proof_ref: null}
    right: {verified: pending, proof_ref: null}
  status: "pending|defined|triangles_verified"
```

## Repository Adjunction Pattern

The most common adjunction - Free ⊣ Repository:

```yaml
repository_adjunction:
  description: |
    Models the relationship between domain entities and database storage.
    
    Free: Storage → Domain
      - Loads model from database
      - Converts to domain entity
      
    Repository: Domain → Storage
      - Takes domain entity
      - Converts to model and persists
      
    Unit η: entity → Repository(Free(entity))
      - "save then load gives equivalent"
      
    Counit ε: Free(Repository(model)) → model
      - "load then save gives equivalent"
      
  implementation:
    unit: |
      async def save_and_reload(entity: E) -> E:
          model = to_model(entity)
          await session.add(model)
          await session.flush()
          return from_model(model)
          
    counit: |
      async def load_and_check(model: M) -> M:
          entity = from_model(model)
          return to_model(entity)
```

## Validation Rules

```yaml
validation:
  functor_pairing:
    rule: "L.target = R.source and R.target = L.source"
    description: "Adjoint functors must be properly paired"
    critical: true
    
  unit_completeness:
    rule: "∀ A ∈ L.source: η_A defined"
    description: "Unit has component for every object"
    critical: true
    
  counit_completeness:
    rule: "∀ B ∈ L.target: ε_B defined"
    description: "Counit has component for every object"
    critical: true
    
  left_triangle:
    rule: "(ε_{L(A)}) ∘ L(η_A) = id_{L(A)}"
    description: "Left triangle identity holds"
    critical: true
    proof_required: true
    
  right_triangle:
    rule: "R(ε_B) ∘ (η_{R(B)}) = id_{R(B)}"
    description: "Right triangle identity holds"
    critical: true
    proof_required: true
```

## Output Structure

```
level-6.manifest.yaml
generated/{language}/src/{project}/
├── adjunctions/
│   ├── repository.{ext}     # Free ⊣ Repository
│   ├── cache.{ext}          # Forget ⊣ Cache
│   └── external.{ext}       # Domain ⊣ External
└── units/
    ├── repository_unit.{ext}    # η for repository
    └── repository_counit.{ext}  # ε for repository
```

## Invariant

```
∀ adjunction L ⊣ R:
  |unit.components| = |L.source.objects|
  |counit.components| = |L.target.objects|
  left_triangle.verified = true
  right_triangle.verified = true

Violation is FATAL. Pipeline MUST NOT proceed to Level 7.
```

## Example (Illustrative Only)

Given Free and Repository functors:

```yaml
# level-6.manifest.yaml
items:
  - id: "adjunction.Free_Repository"
    kind: "adjunction"
    name: "Free ⊣ Repository"
    traces:
      - ref: "level-5.functor.Free"
        role: "left_adjoint"
      - ref: "level-5.functor.Repository"
        role: "right_adjoint"
    definition:
      left: "Free"
      right: "Repository"
      unit:
        name: "η"
        description: "Save entity, get stored version"
        components:
          - object: "Customer"
            morphism: "η_Customer: Customer → Customer"
            implementation: "save_customer"
          - object: "Order"
            morphism: "η_Order: Order → Order"
            implementation: "save_order"
          - object: "Product"
            morphism: "η_Product: Product → Product"
            implementation: "save_product"
      counit:
        name: "ε"
        description: "Load stored, get entity"
        components:
          - object: "CustomerModel"
            morphism: "ε_CustomerModel: CustomerModel → CustomerModel"
            implementation: "load_customer"
          - object: "OrderModel"
            morphism: "ε_OrderModel: OrderModel → OrderModel"
            implementation: "load_order"
          - object: "ProductModel"
            morphism: "ε_ProductModel: ProductModel → ProductModel"
            implementation: "load_product"
    triangles:
      left:
        statement: "ε_{Free(A)} ∘ Free(η_A) = id_{Free(A)}"
        verified: pending
        proof_obligation: "level-8.proof.adjunction.Free_Repository.left"
      right:
        statement: "Repository(ε_B) ∘ η_{Repository(B)} = id_{Repository(B)}"
        verified: pending
        proof_obligation: "level-8.proof.adjunction.Free_Repository.right"

counts:
  total: 1
  by_kind:
    adjunction: 1
    
validation:
  all_units_defined: true
  all_counits_defined: true
  triangles_pending_proof: true
  complete: true
```

## Proof Obligations Generated

Each adjunction generates these proof obligations for Level 8:

```yaml
proof_obligations:
  - id: "proof.adjunction.{L}_{R}.left_triangle"
    statement: "∀ A. (ε_{L(A)}) ∘ L(η_A) = id_{L(A)}"
    adjunction: "{L} ⊣ {R}"
    
  - id: "proof.adjunction.{L}_{R}.right_triangle"
    statement: "∀ B. R(ε_B) ∘ (η_{R(B)}) = id_{R(B)}"
    adjunction: "{L} ⊣ {R}"
```

These MUST be discharged in Level 8.
