---
name: manifest-schema
description: |
  Universal manifest schema for all levels. Every level produces a manifest
  that traces to its inputs. Manifests are the source of truth for coverage
  validation. If an item is not in the manifest, it does not exist.
---

# Manifest Schema

Universal structure for traceability across all levels.

## Principles

1. **Complete enumeration** - Manifest lists ALL items at this level
2. **Trace to source** - Every item traces to input items it composes
3. **Count validation** - |output| must equal expected count
4. **No orphans** - Every input item must produce output
5. **No phantoms** - Every output item must trace to input

## Schema

```yaml
# level-{N}.manifest.yaml

schema_version: "1.0"

# Level identification
level:
  number: 0-11
  name: "primitives|entities|morphisms|modules|categories|functors|adjunctions|transformations|proofs|code|bootstrap|infrastructure"
  description: "What this level represents"

# Source traceability
source:
  # Level 0 has no source (it's the foundation)
  # Level 1+ traces to previous level
  level: N-1
  manifest: "level-{N-1}.manifest.yaml"
  version: "semantic version of source manifest"

# All items at this level
items:
  - id: "unique identifier within this level"
    name: "human readable name"
    kind: "type|identifier|effect|entity|morphism|module|..."
    
    # ═══════════════════════════════════════════════════════════
    # SCOPE AND SHARING
    # ═══════════════════════════════════════════════════════════
    
    # Scope determines where this item lives and who uses it
    scope: "shared|module|internal"  # default: module
    
    # For shared items: who uses this (auto-computed from traces)
    used_by:
      - ref: "consumer_item_id"
        module: "which module the consumer belongs to"
    
    # ═══════════════════════════════════════════════════════════
    # GENERICS / POLYMORPHISM
    # ═══════════════════════════════════════════════════════════
    
    # Type parameters for generic items (optional)
    type_params:
      - name: "A"                    # Type variable name
        constraint: "Entity"         # Optional constraint
    
    # ═══════════════════════════════════════════════════════════
    # TRACEABILITY
    # ═══════════════════════════════════════════════════════════
    
    # Composition trace - what input items this composes
    traces:
      - ref: "source_level.item_id"
        role: "how this input is used"
    
    # Definition (level-specific)
    definition:
      # Structure varies by level
      
    # Output artifacts (for code-producing levels)
    artifacts:
      - path: "relative/path/to/file"
        checksum: "sha256"
        
    # Validation status
    status: "pending|generated|validated|failed"

# Summary counts
counts:
  total: N
  by_kind:
    type: X
    identifier: Y
    # ...
  by_scope:           # NEW: count by scope
    shared: S
    module: M
    internal: I
  status:
    pending: 0
    generated: N
    validated: N
    failed: 0

# Validation report
validation:
  timestamp: "ISO-8601"
  source_coverage:
    total_source_items: M
    items_used: M
    items_unused: 0
    coverage: "100%"
  output_completeness:
    expected: N
    actual: N
    missing: []
    extra: []
    complete: true
  traces_valid: true
  all_artifacts_exist: true
  
# Version control
version:
  manifest: "1.0.0"
  created: "ISO-8601"
  updated: "ISO-8601"
  checksum: "sha256 of this manifest"
```

## Scope Definitions

```yaml
scope_values:
  shared:
    description: "Used by multiple modules"
    criteria: "Traced by items from 2+ different modules"
    code_location: "shared/ directory"
    stability: "HIGH - changes affect multiple modules"
    examples:
      - "Pagination, PaginatedResult"
      - "AppError, ValidationError"
      - "validate_email, validate_not_empty"
      - "IRepository[E, Id]"
      - "Auth, Logging middleware"
    
  module:
    description: "Used by single module only"
    criteria: "Traced by items from exactly 1 module"
    code_location: "modules/{module}/ directory"
    stability: "MEDIUM - changes affect one module"
    examples:
      - "Customer, CustomerService"
      - "OrderError"
      - "create_order"
    
  internal:
    description: "Implementation detail, not exported"
    criteria: "Not traced by any external item"
    code_location: "modules/{module}/_internal/"
    stability: "LOW - can change freely"
    examples:
      - "Helper functions"
      - "Private validators"
```

## Scope Detection Algorithm

```yaml
detect_scope:
  algorithm: |
    for item in all_items:
        # Find all items that trace to this item
        consumers = find_items_tracing_to(item)
        
        if len(consumers) == 0:
            item.scope = "internal"
            item.used_by = []
        else:
            # Get unique modules of consumers
            modules = unique([get_module(c) for c in consumers])
            
            if len(modules) >= 2:
                item.scope = "shared"
            else:
                item.scope = "module"
                
            item.used_by = [
                {ref: c.id, module: get_module(c)} 
                for c in consumers
            ]
            
  run_at: "After all items enumerated, before code generation"
```

## Type Parameters

For polymorphic/generic items:

```yaml
type_params_usage:
  # Generic entity
  - id: "entity.shared.PaginatedResult"
    type_params:
      - {name: "A"}
    definition:
      fields:
        - {name: "items", type: "List[A]"}
        - {name: "pagination", type: "Pagination"}
        
  # Generic with constraint
  - id: "module.shared.Repository"
    type_params:
      - {name: "E", constraint: "Entity"}
      - {name: "Id", constraint: "Identifier"}
    definition:
      operations:
        - {name: "get", signature: "Id → App[E]"}
        - {name: "save", signature: "E → App[E]"}
        
  # Instantiation
  - id: "module.customers.CustomerRepository"
    instantiates: "module.shared.Repository"
    type_args:
      - {param: "E", value: "Customer"}
      - {param: "Id", value: "CustomerId"}
```

## Level-Specific Item Definitions

### Level 0: Primitives

```yaml
items:
  - id: "type.String"
    name: "String"
    kind: "type"
    traces: []  # Primitives have no traces (axiomatic)
    definition:
      category: "base"
      python: "str"
      typescript: "string"
      go: "string"
      lean: "String"
      
  - id: "identifier.MerchantId"
    name: "MerchantId"
    kind: "identifier"
    traces:
      - ref: "type.UUID"
        role: "underlying_type"
    definition:
      underlying: "UUID"
      python: "NewType('MerchantId', UUID)"
      factory: "merchant_id() -> MerchantId"
```

### Level 1: Entities

```yaml
items:
  - id: "entity.Merchant"
    name: "Merchant"
    kind: "entity"
    traces:
      - ref: "level-0.identifier.MerchantId"
        role: "id_field"
      - ref: "level-0.type.String"
        role: "shop_domain_field"
      - ref: "level-0.type.DateTime"
        role: "created_at_field"
    definition:
      type: "product"
      fields:
        - name: "id"
          type: "MerchantId"
        - name: "shop_domain"
          type: "String"
        - name: "created_at"
          type: "DateTime"
```

### Level 2: Morphisms

```yaml
items:
  - id: "morphism.get_merchant"
    name: "get_merchant"
    kind: "morphism"
    traces:
      - ref: "level-1.entity.Merchant"
        role: "codomain"
      - ref: "level-0.identifier.MerchantId"
        role: "domain"
      - ref: "level-0.effect.IO"
        role: "effect"
      - ref: "level-0.effect.Either"
        role: "error_handling"
    definition:
      domain: "MerchantId"
      codomain: "Merchant"
      effects: ["IO", "Either[MerchantError, _]"]
      signature: "MerchantId → IO[Either[MerchantError, Merchant]]"
```

### Level 3: Modules

```yaml
items:
  - id: "module.merchants"
    name: "merchants"
    kind: "module"
    traces:
      - ref: "level-2.morphism.create_merchant"
        role: "operation"
      - ref: "level-2.morphism.get_merchant"
        role: "operation"
      - ref: "level-2.morphism.update_merchant"
        role: "operation"
      - ref: "level-2.morphism.delete_merchant"
        role: "operation"
    definition:
      operations:
        - "create_merchant"
        - "get_merchant"
        - "update_merchant"
        - "delete_merchant"
      aggregate_root: "Merchant"
```

### Level 4: Categories

```yaml
items:
  - id: "category.Domain"
    name: "Domain"
    kind: "category"
    traces:
      - ref: "level-1.entity.*"
        role: "objects"
      - ref: "level-2.morphism.*"
        role: "morphisms"
    definition:
      objects: ["Merchant", "Token", "Profile", ...]
      morphisms: ["get_merchant", "store_token", ...]
      identity: "id_X for each object X"
      composition: "g ∘ f for composable morphisms"
```

### Level 5: Functors

```yaml
items:
  - id: "functor.HTTP"
    name: "HTTP"
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
        "Merchant": "MerchantRequest | MerchantResponse"
        "Token": "TokenRequest | TokenResponse"
      morphism_map:
        "get_merchant": "GET /merchants/{id}"
        "create_merchant": "POST /merchants"
```

### Level 6: Adjunctions

```yaml
items:
  - id: "adjunction.Repository"
    name: "Free ⊣ Repository"
    kind: "adjunction"
    traces:
      - ref: "level-5.functor.Free"
        role: "left_adjoint"
      - ref: "level-5.functor.Repository"
        role: "right_adjoint"
    definition:
      left: "Free"
      right: "Repository"
      unit: "η: Domain → Repository(Free(Domain))"
      counit: "ε: Free(Repository(Domain)) → Domain"
      triangles:
        left: "ε_F ∘ F(η) = id_F"
        right: "G(ε) ∘ η_G = id_G"
```

### Level 7: Natural Transformations

```yaml
items:
  - id: "transformation.Auth"
    name: "Auth"
    kind: "natural_transformation"
    traces:
      - ref: "level-5.functor.Handler"
        role: "source_functor"
      - ref: "level-5.functor.AuthenticatedHandler"
        role: "target_functor"
    definition:
      source: "Handler"
      target: "AuthenticatedHandler"
      components:
        "Request": "verify_token"
        "Response": "identity"
      naturality: "Auth_B ∘ Handler(f) = AuthHandler(f) ∘ Auth_A"
```

### Level 8: Proofs

```yaml
items:
  - id: "proof.identity_merchant"
    name: "Merchant identity law"
    kind: "proof"
    traces:
      - ref: "level-4.category.Domain"
        role: "category"
      - ref: "level-1.entity.Merchant"
        role: "object"
    definition:
      theorem: "id_Merchant ∘ f = f"
      proof_file: "proofs/lean/LeanOS/Identity.lean#merchant_id_left"
      status: "verified"
```

### Level 9: Code

```yaml
items:
  - id: "code.entity.Merchant"
    name: "Merchant entity code"
    kind: "code"
    traces:
      - ref: "level-1.entity.Merchant"
        role: "specification"
      - ref: "level-8.proof.identity_merchant"
        role: "verified_by"
    definition:
      language: "python"
      template: "dataclass"
    artifacts:
      - path: "generated/python/src/glamyouup/domain/entities/merchant.py"
        checksum: "sha256:..."
```

### Level 10: Bootstrap

```yaml
items:
  - id: "bootstrap.entry_point"
    name: "Application entry point"
    kind: "bootstrap"
    traces:
      - ref: "level-9.code.*"
        role: "wires"
    definition:
      type: "entry_point"
    artifacts:
      - path: "generated/python/src/glamyouup/__main__.py"
        checksum: "sha256:..."
```

### Level 11: Infrastructure

```yaml
items:
  - id: "infrastructure.docker"
    name: "Docker configuration"
    kind: "infrastructure"
    traces:
      - ref: "level-10.bootstrap.entry_point"
        role: "runs"
    definition:
      type: "container"
    artifacts:
      - path: "infrastructure/docker/Dockerfile"
        checksum: "sha256:..."
```

## Validation Rules

```yaml
validation_rules:
  universal:
    - "Every item has unique id"
    - "Every item has valid kind"
    - "Every trace references existing source item"
    - "counts.total == len(items)"
    - "All status are 'validated' for complete manifest"
    
  scope_rules:
    shared_valid:
      rule: "∀ item with scope=shared: len(unique_modules(used_by)) >= 2"
      description: "Shared items must be used by 2+ modules"
      
    shared_no_module_deps:
      rule: "∀ shared item: traces only to shared or level-0 items"
      description: "Shared items should not depend on module-scoped items"
      severity: "warning"  # Code smell, not fatal
      
    internal_not_exported:
      rule: "∀ item with scope=internal: used_by is empty"
      description: "Internal items are not traced by external items"
      
    scope_computed:
      rule: "scope is computed from used_by, not manually set"
      description: "Scope detection runs after item enumeration"
    
  type_param_rules:
    params_defined:
      rule: "∀ type_param reference: param exists in type_params"
      description: "Type parameters must be declared"
      
    constraints_valid:
      rule: "∀ type_param.constraint: constraint is a valid type/interface"
      description: "Constraints must reference existing types"
      
    instantiation_complete:
      rule: "∀ instantiation: all type_params have type_args"
      description: "Instantiations must provide all type arguments"
    
  level_specific:
    level_0:
      - "No traces (primitives are axiomatic)"
      - "All items have language mappings"
      - "scope = 'shared' for all (primitives are universal)"
      
    level_1_plus:
      - "Every item traces to at least one source item"
      - "Every source item is traced by at least one output item"
      - "validation.source_coverage.coverage == 100%"
      
  cross_level:
    - "level_N.source.version matches level_{N-1}.version.manifest"
    - "No circular traces"
    - "Trace depth terminates at level_0"
```

## Manifest Operations

```yaml
operations:
  create:
    input: "Previous level manifest + specifications"
    output: "New manifest with items populated"
    
  validate:
    input: "Manifest"
    output: "Validation report"
    checks:
      - schema_valid
      - counts_match
      - traces_valid
      - coverage_complete
      - artifacts_exist
      
  diff:
    input: "Two manifests (old, new)"
    output: "Changes (added, removed, modified)"
    
  trace:
    input: "Item id"
    output: "Full trace tree to level 0"
```

## Per-Level Category Structure

Each level's manifest + traces defines a **free category on the dependency graph**.

This makes the "F: Level N → Level N+1 is a functor" claim precise:

```yaml
level_as_category:
  definition: |
    For each level N, define category C_N:
      Objects: items in level-N.manifest.yaml
      Morphisms: dependency/trace edges (x → y if y.traces includes x)
      Identity: id_x for each item x
      Composition: path composition (if x → y → z, then x → z)
      
  structure: "Free category on dependency graph"
  
  example: |
    Level 1 manifest has: Customer, Order, Product
    Level 1 traces: Customer → CustomerId, Order → OrderId, etc.
    
    C_1 = Free category where:
      Objects = {Customer, Order, Product}
      Morphisms = trace edges + identities + compositions
      
generation_as_functor:
  definition: |
    Generation step from Level N to N+1 is a functor F: C_N → C_{N+1}
    
  requirements:
    identity_preservation: "F(id_x) = id_{F(x)}"
    composition_preservation: "F(g ∘ f) = F(g) ∘ F(f)"
    
  enforcement: |
    - traces_valid: all references exist → edges preserved
    - completeness: |output| == |expected| → objects preserved
    - dependency lifting: if N has x → y, then N+1 has F(x) → F(y)
    
  validation_check: |
    For each trace edge (source, target) in level N+1:
      Verify source traces back to level N
      Verify edge structure is preserved through F
```

This gives the functor pipeline mathematical content:

```
Level 0 ──F₀→ Level 1 ──F₁→ Level 2 ──F₂→ ... ──F₁₀→ Level 11

Where each Fᵢ is a functor between free categories on trace graphs.
```
