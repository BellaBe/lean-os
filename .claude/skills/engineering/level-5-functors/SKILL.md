---
name: level-5-functors
description: |
  Level 5: Functors. Structure-preserving maps between Level 4 categories.
  Functors map objects to objects and morphisms to morphisms while preserving
  identity and composition.
  
  Input: level-4.manifest.yaml
  Output: level-5.manifest.yaml + functor definitions
  
  UNIVERSAL: Works for any domain. Examples are illustrative only.
---

# Level 5: Functors

Structure-preserving maps between categories.

## Principle

A functor F: C → D consists of:
- Object map: F(A) for each object A in C
- Morphism map: F(f) for each morphism f in C

```
Functor F: C → D

Object map:    A ↦ F(A)
Morphism map:  (f: A → B) ↦ (F(f): F(A) → F(B))

Laws:
  Preserves identity:    F(id_A) = id_{F(A)}
  Preserves composition: F(g ∘ f) = F(g) ∘ F(f)
```

## Standard Functors

Every system typically has these functors:

```yaml
standard_functors:
  HTTP:
    source: "Domain"
    target: "HTTP"
    description: "Maps domain operations to HTTP handlers"
    object_map: "Entity → (Request, Response)"
    morphism_map: "Operation → Handler"
    
  Storage:
    source: "Domain"
    target: "Storage"
    description: "Maps domain entities to database models"
    object_map: "Entity → Model"
    morphism_map: "Operation → Query"
    
  Free:
    source: "Storage"
    target: "Domain"
    description: "Left adjoint - loads from storage"
    object_map: "Model → Entity"
    morphism_map: "Query result → Domain value"
    
  Repository:
    source: "Domain"
    target: "Storage"
    description: "Right adjoint - persists to storage"
    object_map: "Entity → Model"
    morphism_map: "Domain value → Query"
    
  External:
    source: "Domain"
    target: "External"
    description: "Maps to external API calls"
    object_map: "Entity → ExternalDTO"
    morphism_map: "Operation → API call"
```

## Process

```yaml
process:
  step_1_load_inputs:
    inputs:
      - "level-4.manifest.yaml"   # Categories
    action: "Load and validate inputs exist"
    
  step_2_enumerate_functors:
    action: "Determine functors needed"
    algorithm: |
      functors = []
      
      # For each pair of categories, determine if functor exists
      for source in level_4.categories:
          for target in level_4.categories:
              if specification.defines_functor(source, target):
                  functors.append(Functor(source, target))
                  
      return functors
    
  step_3_define_object_maps:
    action: "Define object mapping for each functor"
    for_each: "functor in functors"
    algorithm: |
      for object in functor.source.objects:
          target_object = compute_target_object(object, functor.rules)
          functor.object_map[object] = target_object
          
  step_4_define_morphism_maps:
    action: "Define morphism mapping for each functor"
    for_each: "functor in functors"
    algorithm: |
      for morphism in functor.source.morphisms:
          target_morphism = compute_target_morphism(morphism, functor.rules)
          functor.morphism_map[morphism] = target_morphism
          
  step_5_validate_laws:
    action: "Verify functor laws"
    checks:
      - identity_preservation: "F(id_A) = id_{F(A)}"
      - composition_preservation: "F(g ∘ f) = F(g) ∘ F(f)"
    critical: "Laws must hold"
    
  step_6_produce_manifest:
    action: "Write level-5.manifest.yaml"
```

## Functor Structure

```yaml
functor_pattern:
  name: "{FunctorName}"
  
  source:
    category: "{SourceCategory}"
    ref: "level-4.category.{SourceCategory}"
    
  target:
    category: "{TargetCategory}"
    ref: "level-4.category.{TargetCategory}"
    
  object_map:
    - domain: "{SourceObject}"
      codomain: "{TargetObject}"
      transformation: "How to transform"
    # One entry per source object
    
  morphism_map:
    - domain: "{SourceMorphism}"
      codomain: "{TargetMorphism}"
      transformation: "How to transform"
    # One entry per source morphism
    
  laws:
    identity_preservation:
      statement: "F(id_A) = id_{F(A)}"
      proof_obligation: "level-8.proof.functor.{name}.identity"
    composition_preservation:
      statement: "F(g ∘ f) = F(g) ∘ F(f)"
      proof_obligation: "level-8.proof.functor.{name}.composition"
```

## Manifest Item Schema

Each functor in the manifest:

```yaml
functor_item:
  id: "functor.{Name}"
  name: "{Name}"
  kind: "functor"
  traces:
    - ref: "level-4.category.{Source}"
      role: "source"
    - ref: "level-4.category.{Target}"
      role: "target"
  definition:
    source: "{SourceCategory}"
    target: "{TargetCategory}"
    object_map:
      - {from: "Entity1", to: "Model1"}
      - {from: "Entity2", to: "Model2"}
      # All object mappings
    morphism_map:
      - {from: "op1", to: "query1"}
      - {from: "op2", to: "query2"}
      # All morphism mappings
  laws:
    identity: {verified: pending, proof_ref: null}
    composition: {verified: pending, proof_ref: null}
  status: "pending|defined|laws_verified"
```

## Functor Completeness

Every object and morphism in source MUST have a mapping:

```yaml
completeness_rule:
  objects: |
    ∀ A ∈ Source.objects: ∃ F(A) ∈ Target.objects
  morphisms: |
    ∀ f ∈ Source.morphisms: ∃ F(f) ∈ Target.morphisms
  identities: |
    ∀ id_A ∈ Source.identities: F(id_A) = id_{F(A)}
```

## Validation Rules

```yaml
validation:
  completeness:
    rule: "All source objects and morphisms have mappings"
    critical: true
    
  target_validity:
    rule: "All mapped targets exist in target category"
    critical: true
    
  type_preservation:
    rule: "f: A → B ⟹ F(f): F(A) → F(B)"
    description: "Functor preserves typing"
    critical: true
    
  identity_law:
    rule: "F(id_A) = id_{F(A)}"
    description: "Functor preserves identity"
    critical: true
    proof_required: true
    
  composition_law:
    rule: "F(g ∘ f) = F(g) ∘ F(f)"
    description: "Functor preserves composition"
    critical: true
    proof_required: true
```

## Output Structure

```
level-5.manifest.yaml
generated/{language}/src/{project}/
├── functors/
│   ├── http_functor.{ext}       # Domain → HTTP
│   ├── storage_functor.{ext}    # Domain → Storage
│   ├── free_functor.{ext}       # Storage → Domain
│   └── external_functor.{ext}   # Domain → External
└── transformations/
    └── functor_impl.{ext}       # Implementation helpers
```

## Invariant

```
∀ functor F: C → D:
  |F.object_map| = |C.objects|
  |F.morphism_map| = |C.morphisms|
  F.identity_law = verified
  F.composition_law = verified

Violation is FATAL. Pipeline MUST NOT proceed to Level 6.
```

## Example (Illustrative Only)

Given Domain category with 3 objects and 10 morphisms:

```yaml
# level-5.manifest.yaml
items:
  - id: "functor.HTTP"
    kind: "functor"
    traces:
      - ref: "level-4.category.Domain"
        role: "source"
      - ref: "level-4.category.HTTP"
        role: "target"
    definition:
      source: "Domain"
      target: "HTTP"
      object_map:
        - from: "Customer"
          to: ["CreateCustomerRequest", "CustomerResponse"]
        - from: "Order"
          to: ["CreateOrderRequest", "OrderResponse"]
        - from: "Product"
          to: ["CreateProductRequest", "ProductResponse"]
      morphism_map:
        - from: "create_customer"
          to: "POST /customers"
          handler: "create_customer_handler"
        - from: "get_customer"
          to: "GET /customers/{id}"
          handler: "get_customer_handler"
        # ... all morphisms mapped
    laws:
      identity:
        statement: "HTTP(id_Customer) = id_{CustomerResponse}"
        verified: pending
        proof_obligation: "level-8.proof.functor.HTTP.identity"
      composition:
        statement: "HTTP(g ∘ f) = HTTP(g) ∘ HTTP(f)"
        verified: pending
        proof_obligation: "level-8.proof.functor.HTTP.composition"
        
  - id: "functor.Storage"
    kind: "functor"
    traces:
      - ref: "level-4.category.Domain"
        role: "source"
      - ref: "level-4.category.Storage"
        role: "target"
    definition:
      source: "Domain"
      target: "Storage"
      object_map:
        - from: "Customer"
          to: "CustomerModel"
        - from: "Order"
          to: "OrderModel"
        - from: "Product"
          to: "ProductModel"
      morphism_map:
        - from: "create_customer"
          to: "INSERT INTO customers"
        - from: "get_customer"
          to: "SELECT FROM customers WHERE id = ?"
        # ... all morphisms mapped
        
  - id: "functor.Free"
    kind: "functor"
    traces:
      - ref: "level-4.category.Storage"
        role: "source"
      - ref: "level-4.category.Domain"
        role: "target"
    definition:
      source: "Storage"
      target: "Domain"
      object_map:
        - from: "CustomerModel"
          to: "Customer"
        - from: "OrderModel"
          to: "Order"
        - from: "ProductModel"
          to: "Product"
      morphism_map:
        - from: "load_customer_model"
          to: "Customer value"
      note: "Left adjoint to Repository"

counts:
  total: 3
  by_kind:
    functor: 3
    
validation:
  all_objects_mapped: true
  all_morphisms_mapped: true
  laws_pending_proof: true
  complete: true
```

## Proof Obligations Generated

Each functor generates these proof obligations for Level 8:

```yaml
proof_obligations:
  - id: "proof.functor.{F}.identity"
    statement: "∀ A ∈ Source. F(id_A) = id_{F(A)}"
    functor: "{F}"
    
  - id: "proof.functor.{F}.composition"
    statement: "∀ f: A → B, g: B → C ∈ Source. F(g ∘ f) = F(g) ∘ F(f)"
    functor: "{F}"
```

These MUST be discharged in Level 8.
