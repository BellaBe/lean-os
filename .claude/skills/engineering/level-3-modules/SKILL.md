---
name: level-3-modules
description: |
  Level 3: Modules. Groupings of Level 2 morphisms that operate on the same
  aggregate root. Each module is a coherent unit of operations.
  
  Input: level-2.manifest.yaml, specifications/v{X}/services.spec.yaml
  Output: level-3.manifest.yaml + module definitions
  
  UNIVERSAL: Works for any domain. Examples are illustrative only.
---

# Level 3: Modules

Groupings of morphisms. Modules define coherent operational units.

## Principle

A module is a collection of morphisms with a common aggregate root.

```
Module M = { f₁, f₂, ..., fₙ }
  where ∀ fᵢ: aggregate_root(fᵢ) = E for some entity E

Module forms a sub-category:
  - Objects: Types involved in module operations
  - Morphisms: Operations in the module
  - Closed under composition within module
```

## Categorical Definition

```
Module as Sub-category:
  - Subset of Domain category morphisms
  - Shares identity morphisms from Domain
  - Composition: If f, g ∈ Module and g ∘ f defined, then g ∘ f ∈ Module
  
Module as Kleisli Category (when effects present):
  - Objects: Types A, B, C, ...
  - Morphisms: A → F[B] where F is effect monad
  - Composition: Kleisli composition (>=>)
```

## Process

```yaml
process:
  step_1_load_inputs:
    inputs:
      - "level-2.manifest.yaml"           # Morphisms
      - "specifications/v{X}/services.spec.yaml"  # Module structure
    action: "Load and validate inputs exist"
    on_missing: "HALT - required input not found"
    
  step_2_enumerate:
    action: "Extract complete module list from specifications"
    source: "services.spec.yaml → modules"
    algorithm: |
      modules_to_generate = []
      for module in specifications.services.modules:
          modules_to_generate.append(module)
      return modules_to_generate
    critical: "This list is exhaustive"
    
  step_3_validate_morphisms:
    action: "Verify all module morphisms exist in Level 2"
    algorithm: |
      for module in modules_to_generate:
          for morphism_name in module.morphisms:
              morphism_id = f"morphism.{module.name}.{morphism_name}"
              if morphism_id not in level_2_manifest.items:
                  HALT(f"Missing morphism: {morphism_id}")
    on_missing: "HALT - add morphism to Level 2 first"
    
  step_4_generate:
    action: "Generate definition for EACH module"
    algorithm: |
      generated = []
      for module in modules_to_generate:
          definition = generate_module(module, level_2)
          generated.append(definition)
      assert len(generated) == len(modules_to_generate)
    traces: "Each morphism traces to Level 2"
    
  step_5_validate_output:
    action: "Verify output completeness"
    checks:
      - "len(generated) == len(specified_modules)"
      - "all morphisms accounted for"
      - "no orphan morphisms"
    on_failure: "HALT - generation incomplete"
    
  step_6_produce_manifest:
    action: "Write level-3.manifest.yaml"
```

## Module Structure

Every module follows this pattern:

```yaml
module_pattern:
  name: "module_name"  # e.g., customers, orders, payments
  
  aggregate_root: "Entity"  # The main entity this module operates on
  
  operations:
    - ref: "level-2.morphism.{module}.{operation}"
    # All morphisms belonging to this module
    
  dependencies:
    entities: ["Entity1", "Entity2"]  # Entities this module uses
    external: ["ExternalService"]     # External dependencies (if any)
    
  invariants:
    - "Business rules that must hold"
```

## Manifest Item Schema

Each module in the manifest:

```yaml
module_item:
  id: "module.{name}"
  name: "{name}"
  kind: "module"
  traces:
    - ref: "level-2.morphism.{module}.{op1}"
      role: "operation"
    - ref: "level-2.morphism.{module}.{op2}"
      role: "operation"
    # ... all operations
    - ref: "level-1.entity.{AggregateRoot}"
      role: "aggregate_root"
  definition:
    aggregate_root: "{Entity}"
    operations:
      - name: "{operation_name}"
        ref: "level-2.morphism.{module}.{operation_name}"
    dependencies:
      - ref: "level-1.entity.{Entity}"
        role: "read|write"
  artifacts:
    - path: "generated/{lang}/src/{project}/application/services/{module}_service.{ext}"
  status: "pending|generated|validated"
```

## Morphism Coverage Validation

Every morphism from Level 2 MUST belong to exactly one module:

```yaml
coverage_rule:
  statement: |
    ∀ morphism ∈ Level 2 (kind="morphism"):
      ∃! module ∈ Level 3: morphism ∈ module.operations
      
  translation: "Every morphism belongs to exactly one module"
  
  exception: "Identity morphisms are shared (belong to all modules using that entity)"
```

## Validation Rules

```yaml
validation:
  completeness:
    rule: "|generated_modules| == |specified_modules|"
    description: "Every specified module is generated"
    critical: true
    
  morphism_coverage:
    rule: "∀ morphism ∈ Level2.non_identity: ∃ module containing it"
    description: "Every non-identity morphism belongs to a module"
    critical: true
    
  no_duplicate_morphisms:
    rule: "∀ morphism: appears in exactly one module"
    description: "Morphisms are not duplicated across modules"
    critical: true
    
  trace_validity:
    rule: "∀ trace ∈ module.traces: trace.ref ∈ level-2.manifest"
    description: "All traces point to existing Level 2 items"
    critical: true
    
  aggregate_root_exists:
    rule: "∀ module: aggregate_root ∈ level-1.entities"
    description: "Every module has a valid aggregate root"
    critical: true
```

## Output Structure

```
level-3.manifest.yaml
generated/{language}/src/{project}/application/
├── services/
│   ├── __init__.{ext}           # Exports all services
│   └── {module}_service.{ext}   # One service per module - ALL of them
└── ports/
    ├── __init__.{ext}
    └── {module}_port.{ext}      # Interface per module
```

## Invariant

```
|level-3.manifest.items| == |specifications.modules|

∀ morphism ∈ Level 2 (kind ≠ identity):
  ∃ module ∈ Level 3: morphism.id ∈ module.operations

Violation is FATAL. Pipeline MUST NOT proceed to Level 4.
```

## Example (Illustrative Only)

Given a specification with 3 modules:

```yaml
# specifications/services.spec.yaml
modules:
  - name: customers
    aggregate_root: Customer
    morphisms: [create_customer, get_customer, update_customer, delete_customer]
    
  - name: orders
    aggregate_root: Order
    morphisms: [place_order, get_order, cancel_order]
    
  - name: inventory
    aggregate_root: Product
    morphisms: [add_stock, remove_stock, get_stock]
```

Level 3 MUST generate exactly 3 modules:

```yaml
# level-3.manifest.yaml
items:
  - id: "module.customers"
    kind: "module"
    traces:
      - ref: "level-2.morphism.customers.create_customer"
        role: "operation"
      - ref: "level-2.morphism.customers.get_customer"
        role: "operation"
      - ref: "level-2.morphism.customers.update_customer"
        role: "operation"
      - ref: "level-2.morphism.customers.delete_customer"
        role: "operation"
      - ref: "level-1.entity.Customer"
        role: "aggregate_root"
    definition:
      aggregate_root: "Customer"
      operations:
        - {name: "create_customer", ref: "level-2.morphism.customers.create_customer"}
        - {name: "get_customer", ref: "level-2.morphism.customers.get_customer"}
        - {name: "update_customer", ref: "level-2.morphism.customers.update_customer"}
        - {name: "delete_customer", ref: "level-2.morphism.customers.delete_customer"}
        
  - id: "module.orders"
    kind: "module"
    traces:
      - ref: "level-2.morphism.orders.place_order"
        role: "operation"
      - ref: "level-2.morphism.orders.get_order"
        role: "operation"
      - ref: "level-2.morphism.orders.cancel_order"
        role: "operation"
      - ref: "level-1.entity.Order"
        role: "aggregate_root"
    definition:
      aggregate_root: "Order"
      operations:
        - {name: "place_order", ref: "level-2.morphism.orders.place_order"}
        - {name: "get_order", ref: "level-2.morphism.orders.get_order"}
        - {name: "cancel_order", ref: "level-2.morphism.orders.cancel_order"}
        
  - id: "module.inventory"
    kind: "module"
    traces:
      - ref: "level-2.morphism.inventory.add_stock"
        role: "operation"
      - ref: "level-2.morphism.inventory.remove_stock"
        role: "operation"
      - ref: "level-2.morphism.inventory.get_stock"
        role: "operation"
      - ref: "level-1.entity.Product"
        role: "aggregate_root"
    definition:
      aggregate_root: "Product"
      operations:
        - {name: "add_stock", ref: "level-2.morphism.inventory.add_stock"}
        - {name: "remove_stock", ref: "level-2.morphism.inventory.remove_stock"}
        - {name: "get_stock", ref: "level-2.morphism.inventory.get_stock"}

counts:
  total: 3
  by_kind:
    module: 3
    
validation:
  module_coverage:
    specified: 3
    generated: 3
    coverage: "100%"
  morphism_coverage:
    total_morphisms: 10  # From Level 2 (excluding identities)
    assigned_to_modules: 10
    orphans: 0
    coverage: "100%"
  complete: true
```

## Service Generation Pattern

Each module generates a service class:

```python
# Python example
@dataclass
class {Module}Service:
    """
    Service for {aggregate_root} operations.
    
    Module: level-3.manifest.yaml#module.{module}
    Operations: {operation_count}
    """
    
    # Dependencies (repositories, clients)
    {dependency}: I{Dependency}
    
    # Operations (from Level 2 morphisms)
    async def {operation}(self, {params}) -> Result[{Error}, {Return}]:
        """
        Morphism: level-2.manifest.yaml#morphism.{module}.{operation}
        Signature: {domain} → {effects}[{codomain}]
        """
        pass
```
