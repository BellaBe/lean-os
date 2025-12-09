---
name: level-2-morphisms
description: |
  Level 2: Morphisms. Arrows between Level 1 entities. Every morphism has a
  domain (input type), codomain (output type), and effects.
  
  Input: level-1.manifest.yaml, specifications/v{X}/services.spec.yaml
  Output: level-2.manifest.yaml + morphism signatures
  
  UNIVERSAL: Works for any domain. Examples are illustrative only.
---

# Level 2: Morphisms

Arrows between entities. Morphisms are the operations of our Domain category.

## Principle

A morphism is a typed arrow: domain → codomain, possibly with effects.

```
Morphism f: A → B
  domain(f) = A    (input type)
  codomain(f) = B  (output type)

With effects:
  f: A → F[B]  where F is effect (IO, Either, etc.)
  
∀ morphism ∈ Level 2:
  domain(morphism) ∈ Level 1 ∪ Level 0
  codomain(morphism) ∈ Level 1 ∪ Level 0
  effects(morphism) ⊆ Level 0.effects
```

**Critical distinction - Effect usage is SYNTACTIC here:**

```yaml
effect_semantics:
  level_0: "Monad symbols as type constructors (syntax)"
  level_2: "Morphisms USE these symbols in signatures (syntax)"
  level_4: "Monads GET their laws - unit, bind, associativity"
  level_8: "Laws PROVEN in Lean"
  
  example:
    level_2_signature: "get_customer: CustomerId → IO[Either[Error, Customer]]"
    interpretation_at_l2: "Just a type - IO[Either[...]] is syntax"
    interpretation_at_l4: "IO and Either are monads with laws"
    composition: |
      At L2, we write signatures like: get >=> validate >=> update
      At L4, >=> (Kleisli composition) is defined with laws
      At L8, associativity of >=> is proven
```

Most Level 2 morphisms are **Kleisli arrows**: `A → M[B]` where M is the App monad.
But at Level 2, we only describe this syntactically. The Kleisli category structure
(identity = pure, composition = >>=) comes at Level 4.

## Categorical Definition

```
Morphism in Category Domain:
  - Arrow from object A to object B
  - Composable: g ∘ f when codomain(f) = domain(g)
  - Identity: id_A: A → A for each object A
  - Associativity: (h ∘ g) ∘ f = h ∘ (g ∘ f)
```

## Process

```yaml
process:
  step_1_load_inputs:
    inputs:
      - "level-0.manifest.yaml"           # Effects, primitives
      - "level-1.manifest.yaml"           # Entities (objects)
      - "specifications/v{X}/services.spec.yaml"  # Morphism definitions
    action: "Load and validate inputs exist"
    on_missing: "HALT - required input not found"
    
  step_2_enumerate:
    action: "Extract complete morphism list from specifications"
    source: "services.spec.yaml → modules → morphisms"
    algorithm: |
      morphisms_to_generate = []
      for module in specifications.services.modules:
          for morphism in module.morphisms:
              morphisms_to_generate.append(morphism)
      return morphisms_to_generate
    critical: "This list is exhaustive - count must match spec"
    
  step_3_validate_types:
    action: "Verify all domain/codomain types exist"
    algorithm: |
      for morphism in morphisms_to_generate:
          if morphism.domain not in (level_0 ∪ level_1):
              HALT(f"Unknown domain type: {morphism.domain}")
          if morphism.codomain not in (level_0 ∪ level_1):
              HALT(f"Unknown codomain type: {morphism.codomain}")
          for effect in morphism.effects:
              if effect not in level_0.effects:
                  HALT(f"Unknown effect: {effect}")
    on_missing: "HALT - fix type definitions first"
    
  step_4_generate:
    action: "Generate definition for EACH morphism"
    algorithm: |
      generated = []
      for morphism in morphisms_to_generate:
          definition = generate_morphism(morphism, level_0, level_1)
          generated.append(definition)
      assert len(generated) == len(morphisms_to_generate)
    traces: "Domain/codomain trace to Level 1, effects to Level 0"
    
  step_5_generate_identities:
    action: "Generate identity morphism for each Level 1 entity"
    algorithm: |
      for entity in level_1.items.where(kind="entity"):
          identity = generate_identity(entity)
          generated.append(identity)
    required: "Identity morphisms are mandatory for category laws"
    
  step_6_validate_output:
    action: "Verify output completeness"
    checks:
      - "len(generated_morphisms) == len(specified_morphisms)"
      - "len(identity_morphisms) == len(entities)"
      - "all types resolved"
      - "all effects valid"
    on_failure: "HALT - generation incomplete"
    
  step_7_produce_manifest:
    action: "Write level-2.manifest.yaml"
```

## Morphism Structure

Every morphism follows this pattern:

```yaml
morphism_pattern:
  # Name
  name: "operation_name"  # e.g., create_customer, get_order
  
  # Typing
  domain: "Input type (entity, primitive, or product)"
  codomain: "Output type (entity, primitive, or product)"
  
  # Effects (from Level 0)
  effects:
    - "IO"                  # Side effect (database, network)
    - "Either[Error, _]"    # Can fail with typed error
    # Combination: IO[Either[Error, Result]]
    
  # Traces
  traces:
    - ref: "level-1.entity.{Domain}"
      role: "domain"
    - ref: "level-1.entity.{Codomain}"
      role: "codomain"
    - ref: "level-0.effect.IO"
      role: "effect"
```

## Manifest Item Schema

Each morphism in the manifest:

```yaml
morphism_item:
  id: "morphism.{module}.{name}"
  name: "{name}"
  kind: "morphism"
  module: "{module_name}"
  traces:
    - ref: "level-1.entity.{EntityName}"
      role: "domain|codomain"
    - ref: "level-0.effect.{Effect}"
      role: "effect"
    - ref: "level-0.type.{Type}"
      role: "parameter|return"
  definition:
    domain: "{InputType}"
    codomain: "{OutputType}"
    effects: ["IO", "Either[{Error}, _]"]
    signature: "{Domain} → {Effects}[{Codomain}]"
  status: "pending|generated|validated"
```

## Identity Morphisms

Every entity gets an identity morphism (required for category laws):

```yaml
identity_morphism:
  id: "morphism.identity.{Entity}"
  name: "id_{Entity}"
  kind: "identity"
  traces:
    - ref: "level-1.entity.{Entity}"
      role: "object"
  definition:
    domain: "{Entity}"
    codomain: "{Entity}"
    effects: []  # Identity is pure
    signature: "{Entity} → {Entity}"
    implementation: "return input unchanged"
```

## Effect Patterns

Common effect signatures:

```yaml
effect_patterns:
  pure:
    signature: "A → B"
    description: "No effects"
    example: "validate_email: String → Either[Error, Email]"
    
  io:
    signature: "A → IO[B]"
    description: "Side effect, always succeeds"
    example: "log_event: Event → IO[Unit]"
    
  fallible:
    signature: "A → Either[E, B]"
    description: "Pure but may fail"
    example: "parse_json: String → Either[ParseError, Json]"
    
  io_fallible:
    signature: "A → IO[Either[E, B]]"
    description: "Side effect that may fail"
    example: "get_customer: CustomerId → IO[Either[NotFound, Customer]]"
    note: "Most common pattern for database/network operations"
```

## Validation Rules

```yaml
validation:
  completeness:
    rule: "|generated_morphisms| == |specified_morphisms|"
    description: "Every specified morphism is generated"
    critical: true
    
  identities_exist:
    rule: "|identity_morphisms| == |entities|"
    description: "Every entity has an identity morphism"
    critical: true
    
  type_validity:
    rule: "∀ m: domain(m) ∈ (Level0 ∪ Level1) ∧ codomain(m) ∈ (Level0 ∪ Level1)"
    description: "All types reference existing items"
    critical: true
    
  effect_validity:
    rule: "∀ effect ∈ morphism.effects: effect ∈ level-0.effects"
    description: "All effects are defined in Level 0"
    critical: true
    
  composability:
    rule: "If specification declares g ∘ f, then codomain(f) = domain(g)"
    description: "Declared compositions are type-valid"
    critical: true
```

## Output Structure

```
level-2.manifest.yaml
generated/{language}/src/{project}/domain/
├── morphisms/
│   ├── __init__.{ext}         # Exports all morphism signatures
│   ├── {module}_ops.{ext}     # Morphisms grouped by module
│   └── identity.{ext}         # Identity morphisms
└── errors/
    ├── __init__.{ext}
    └── {module}_errors.{ext}  # Error types for Either
```

## Invariant

```
|level-2.manifest.items where kind="morphism"| == |specifications.morphisms|
|level-2.manifest.items where kind="identity"| == |level-1.entities|

Violation is FATAL. Pipeline MUST NOT proceed to Level 3.
```

## Example (Illustrative Only)

Given a specification with 2 modules, 4 morphisms:

```yaml
# specifications/services.spec.yaml
modules:
  - name: customers
    morphisms:
      - name: create_customer
        domain: CreateCustomerDTO
        codomain: Customer
        effects: [IO, Either[ValidationError, _]]
      - name: get_customer
        domain: CustomerId
        codomain: Customer
        effects: [IO, Either[NotFound, _]]
  - name: orders
    morphisms:
      - name: place_order
        domain: PlaceOrderDTO
        codomain: Order
        effects: [IO, Either[OrderError, _]]
      - name: get_order
        domain: OrderId
        codomain: Order
        effects: [IO, Either[NotFound, _]]
```

Level 2 MUST generate:
- 4 morphisms (from spec)
- 3 identity morphisms (one per entity from Level 1)

```yaml
# level-2.manifest.yaml
items:
  # Specified morphisms
  - id: "morphism.customers.create_customer"
    kind: "morphism"
    module: "customers"
    traces:
      - ref: "level-1.entity.Customer"
        role: "codomain"
      - ref: "level-0.effect.IO"
        role: "effect"
      - ref: "level-0.effect.Either"
        role: "effect"
    definition:
      domain: "CreateCustomerDTO"
      codomain: "Customer"
      effects: ["IO", "Either[ValidationError, _]"]
      signature: "CreateCustomerDTO → IO[Either[ValidationError, Customer]]"
      
  - id: "morphism.customers.get_customer"
    kind: "morphism"
    module: "customers"
    traces:
      - ref: "level-0.identifier.CustomerId"
        role: "domain"
      - ref: "level-1.entity.Customer"
        role: "codomain"
    definition:
      domain: "CustomerId"
      codomain: "Customer"
      effects: ["IO", "Either[NotFound, _]"]
      signature: "CustomerId → IO[Either[NotFound, Customer]]"
      
  # ... other morphisms ...
  
  # Identity morphisms (auto-generated)
  - id: "morphism.identity.Customer"
    kind: "identity"
    traces:
      - ref: "level-1.entity.Customer"
        role: "object"
    definition:
      domain: "Customer"
      codomain: "Customer"
      effects: []
      signature: "Customer → Customer"
      
  - id: "morphism.identity.Order"
    kind: "identity"
    traces:
      - ref: "level-1.entity.Order"
        role: "object"
    definition:
      domain: "Order"
      codomain: "Order"
      effects: []
      signature: "Order → Order"
      
  - id: "morphism.identity.Product"
    kind: "identity"
    traces:
      - ref: "level-1.entity.Product"
        role: "object"
    definition:
      domain: "Product"
      codomain: "Product"
      effects: []
      signature: "Product → Product"

counts:
  total: 7
  by_kind:
    morphism: 4
    identity: 3
    
validation:
  source_coverage:
    specified_morphisms: 4
    generated_morphisms: 4
    coverage: "100%"
  identity_coverage:
    entities: 3
    identities: 3
    coverage: "100%"
  complete: true
```
