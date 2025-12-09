---
name: level-1-entities
description: |
  Level 1: Entities. Products of Level 0 primitives. Every entity is a product
  type composed from identifiers, base types, and constraints.
  
  Input: level-0.manifest.yaml, specifications/v{X}/requirements.adt
  Output: level-1.manifest.yaml + entity definitions
  
  UNIVERSAL: Works for any domain. Examples are illustrative only.
---

# Level 1: Entities

Products of primitives. Entities are the objects of our Domain category.

## Principle

An entity is a product type: fields combined with ×.

```
Entity = Field₁ × Field₂ × ... × Fieldₙ
       = (Id × Data × Metadata)

∀ entity ∈ Level 1: 
  ∃ fields ⊆ Level 0: entity = Π fields
```

## Categorical Definition

```
Entity in Category Domain:
  - Object: The entity type itself
  - Identity morphism: id_Entity
  - Product structure: Entity = A × B × C × ...
  - Projections: π₁: Entity → A, π₂: Entity → B, ...
```

## Process

```yaml
process:
  step_1_load_inputs:
    inputs:
      - "level-0.manifest.yaml"           # Available primitives
      - "specifications/v{X}/requirements.adt"    # Type definitions
      - "specifications/v{X}/domain-concepts.yaml" # Entity descriptions
    action: "Load and validate inputs exist"
    on_missing: "HALT - required input not found"
    
  step_2_enumerate:
    action: "Extract complete entity list from specifications"
    source: "domain-concepts.yaml → entities section"
    output: "entities_to_generate: List[EntitySpec]"
    critical: "This list is exhaustive - no additions, no omissions"
    algorithm: |
      entities_to_generate = []
      for entity in specifications.domain_concepts.entities:
          entities_to_generate.append(entity)
      return entities_to_generate
    
  step_3_validate_primitives:
    action: "Verify all referenced types exist in Level 0"
    algorithm: |
      for entity in entities_to_generate:
          for field in entity.fields:
              if field.type not in level_0_manifest.items:
                  HALT(f"Missing primitive: {field.type}")
    on_missing: "HALT - add missing primitive to Level 0 first"
    
  step_4_generate:
    action: "Generate definition for EACH entity in list"
    algorithm: |
      generated = []
      for entity in entities_to_generate:
          definition = generate_entity(entity, level_0_manifest)
          generated.append(definition)
      assert len(generated) == len(entities_to_generate)
    traces: "Each field traces to its Level 0 primitive"
    
  step_5_validate_output:
    action: "Verify output completeness"
    checks:
      - "len(generated) == len(entities_to_generate)"
      - "all entities have valid traces"
      - "no orphan types"
    on_failure: "HALT - generation incomplete"
    
  step_6_produce_manifest:
    action: "Write level-1.manifest.yaml"
    content:
      - items: "All generated entity definitions"
      - counts: "Verified counts"
      - traces: "All trace references"
      - validation: "Completeness proof"
      
  step_7_generate_code:
    action: "Generate code for target language"
    output: "generated/{language}/src/{project}/domain/entities/"
    per_entity: "One file per entity"
```

## Entity Structure

Every entity follows this pattern:

```yaml
entity_pattern:
  # Required: Unique identifier
  id:
    name: "id"
    type: "{Entity}Id"
    traces: "level-0.identifier.{Entity}Id"
    required: true
    
  # Domain-specific fields (from specification)
  fields:
    source: "specifications.requirements.adt.{Entity}.fields"
    each_field:
      name: "field name from spec"
      type: "field type from spec"
      traces: "level-0.{type_category}.{type_name}"
      
  # Optional: Audit metadata (if specified)
  metadata:
    created_at:
      type: "DateTime"
      traces: "level-0.type.DateTime"
    updated_at:
      type: "DateTime"
      traces: "level-0.type.DateTime"
```

## Manifest Item Schema

Each entity in the manifest:

```yaml
entity_item:
  id: "entity.{EntityName}"
  name: "{EntityName}"
  kind: "entity"
  traces:
    - ref: "level-0.identifier.{EntityName}Id"
      role: "identity"
    - ref: "level-0.{type_category}.{TypeName}"
      role: "field:{field_name}"
    # ... one trace per field type
  definition:
    type: "product"
    fields:
      - name: "id"
        type: "{EntityName}Id"
      - name: "{field_name}"
        type: "{FieldType}"
      # ... all fields from specification
  artifacts:
    - path: "generated/{lang}/src/{project}/domain/entities/{entity_name}.{ext}"
  status: "pending|generated|validated"
```

## Enumeration Types (Simple Coproducts)

Enums are also Level 1 items - coproducts with finite variants:

```yaml
enum_pattern:
  id: "enum.{EnumName}"
  name: "{EnumName}"
  kind: "enum"
  traces:
    - ref: "level-0.type.String"
      role: "underlying"
  definition:
    type: "coproduct"
    variants: 
      source: "specifications.requirements.adt.{EnumName}.variants"
```

## Code Generation Templates

### Python

```python
# generated/{project}/domain/entities/{entity_name}.py

from dataclasses import dataclass
from datetime import datetime

from ..primitives import {EntityName}Id
from ..primitives import {imported_types}

@dataclass(frozen=True, slots=True)
class {EntityName}:
    """
    {description from specification}
    
    Categorical: Object in Domain category
    Product: {field_types joined with " × "}
    Manifest: level-1.manifest.yaml#entity.{EntityName}
    """
    
    id: {EntityName}Id
    # ... all fields from specification
    
    def __post_init__(self) -> None:
        # Invariant validation from constraints
        pass
```

### TypeScript

```typescript
// generated/{project}/domain/entities/{entityName}.ts

import type { {EntityName}Id } from '../primitives';

export interface {EntityName} {
  readonly id: {EntityName}Id;
  // ... all fields from specification
}
```

### Go

```go
// generated/{project}/domain/entities/{entity_name}.go

package entities

type {EntityName} struct {
    ID {EntityName}ID
    // ... all fields from specification
}
```

## Validation Rules

```yaml
validation:
  completeness:
    rule: "|generated| == |specified|"
    description: "Every specified entity is generated"
    critical: true
    on_violation: "HALT"
    
  trace_validity:
    rule: "∀ trace ∈ entity.traces: trace.ref ∈ level-0.manifest"
    description: "All traces point to existing Level 0 items"
    critical: true
    on_violation: "HALT"
    
  identifier_existence:
    rule: "∀ entity: level-0.identifier.{entity}Id exists"
    description: "Every entity has its identifier in Level 0"
    critical: true
    on_violation: "HALT - add identifier to Level 0"
    
  no_orphan_types:
    rule: "∀ type ∈ entity.fields: type is traced to Level 0"
    description: "No untraced types"
    critical: true
    on_violation: "HALT - add type to Level 0"
    
  artifact_existence:
    rule: "∀ artifact ∈ entity.artifacts: file_exists(artifact.path)"
    description: "All declared artifacts exist"
    critical: true
    on_violation: "HALT - code generation failed"
```

## Output Structure

```
level-1.manifest.yaml          # Complete manifest with all entities
generated/{language}/src/{project}/domain/
├── __init__.{ext}             # Exports all entities
├── entities/
│   ├── __init__.{ext}
│   └── {entity_name}.{ext}    # One file per entity - ALL of them
└── enums/
    ├── __init__.{ext}
    └── {enum_name}.{ext}      # One file per enum - ALL of them
```

## Invariant

```
|level-1.manifest.items where kind="entity"| == |specifications.entities|
|level-1.manifest.items where kind="enum"| == |specifications.enums|

Violation of this invariant is a FATAL ERROR.
The pipeline MUST NOT proceed to Level 2.
```

## Example (Illustrative Only)

Given a specification with 3 entities:

```yaml
# specifications/domain-concepts.yaml
entities:
  - name: Customer
    fields: [id, email, name]
  - name: Order  
    fields: [id, customer_id, placed_at]
  - name: Product
    fields: [id, name, price]
```

Level 1 MUST generate exactly 3 entity items:

```yaml
# level-1.manifest.yaml
items:
  - id: "entity.Customer"
    kind: "entity"
    traces:
      - ref: "level-0.identifier.CustomerId"
      - ref: "level-0.constraint.Email"
      - ref: "level-0.type.String"
    definition:
      fields:
        - {name: "id", type: "CustomerId"}
        - {name: "email", type: "Email"}
        - {name: "name", type: "String"}
        
  - id: "entity.Order"
    kind: "entity"
    traces:
      - ref: "level-0.identifier.OrderId"
      - ref: "level-0.identifier.CustomerId"
      - ref: "level-0.type.DateTime"
    definition:
      fields:
        - {name: "id", type: "OrderId"}
        - {name: "customer_id", type: "CustomerId"}
        - {name: "placed_at", type: "DateTime"}
        
  - id: "entity.Product"
    kind: "entity"
    traces:
      - ref: "level-0.identifier.ProductId"
      - ref: "level-0.type.String"
      - ref: "level-0.constraint.Money"
    definition:
      fields:
        - {name: "id", type: "ProductId"}
        - {name: "name", type: "String"}
        - {name: "price", type: "Money"}

counts:
  total: 3
  by_kind:
    entity: 3
    
validation:
  output_completeness:
    expected: 3
    actual: 3
    complete: true
```

The count MUST match. If specification has 11 entities, manifest has 11. If 3, then 3. No more, no less.
