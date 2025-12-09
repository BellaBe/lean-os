---
name: standards-validator
description: |
  Validate all standards for completeness, consistency, and categorical law compliance.
  Gate skill for standards layer - must pass before proceeding to maps layer.
  Checks that all categorical structures are well-formed and laws hold.
  Input: All standards/*.std.yaml files
  Output: standards/versions.yaml, standards/validation-report.yaml
---

# Standards Validator

Validate standards and gate to maps layer.

## Purpose

Final validation before maps layer:
1. Completeness validation (all required standards defined)
2. Consistency validation (no contradictions)
3. Categorical law validation (mathematical correctness)
4. Reference integrity (all cross-references resolve)
5. Version tracking and gate decision

## Input

All standards files:
```
standards/
├── categories/
│   ├── domain.std.yaml
│   ├── storage.std.yaml
│   ├── external.std.yaml
│   └── http.std.yaml
├── security/
│   ├── authentication.std.yaml
│   ├── authorization.std.yaml
│   ├── sanitization.std.yaml
│   └── tenant-isolation.std.yaml
├── observability/
│   ├── metrics.std.yaml
│   ├── tracing.std.yaml
│   └── logging.std.yaml
├── caching/
│   ├── cache.std.yaml
│   └── invalidation.std.yaml
├── transactions/
│   ├── transaction.std.yaml
│   └── saga.std.yaml
├── configuration/
│   ├── config.std.yaml
│   └── feature-flags.std.yaml
└── api-versioning/
    ├── versioning.std.yaml
    └── deprecation.std.yaml
```

## Output

```
standards/
├── versions.yaml          # Version tracking
└── validation-report.yaml # Validation results
```

## Validation Categories

### 1. Completeness Validation

```yaml
completeness_checks:
  # Category standards
  categories:
    required:
      - domain.std.yaml
      - storage.std.yaml
    optional:
      - external.std.yaml
      - http.std.yaml
    checks:
      - every_category_has_objects
      - every_category_has_morphisms
      - every_category_has_identity
      - every_category_has_composition
      
  # Security standards
  security:
    required:
      - authentication.std.yaml
      - authorization.std.yaml
    optional:
      - sanitization.std.yaml
      - tenant-isolation.std.yaml
    checks:
      - auth_strategy_defined
      - authz_model_complete
      - sanitization_rules_present
      
  # Observability standards
  observability:
    required:
      - metrics.std.yaml
    optional:
      - tracing.std.yaml
      - logging.std.yaml
    checks:
      - metrics_cover_all_morphisms
      - tracing_propagation_defined
      - logging_levels_specified
      
  # Other standards
  caching:
    required: [cache.std.yaml]
    checks:
      - cache_adjunction_complete
      - invalidation_strategies_defined
      
  transactions:
    required: [transaction.std.yaml]
    optional: [saga.std.yaml]
    checks:
      - transaction_monad_defined
      - saga_compensations_complete
      
  configuration:
    required: [config.std.yaml]
    optional: [feature-flags.std.yaml]
    checks:
      - all_config_fields_typed
      - secrets_identified
      
  api_versioning:
    required: []
    optional: [versioning.std.yaml, deprecation.std.yaml]
    checks:
      - version_strategy_defined
      - migration_paths_complete
```

### 2. Consistency Validation

```yaml
consistency_checks:
  # No contradictions between standards
  cross_standard:
    - name: auth_before_authz
      check: "Authentication must precede authorization in middleware chain"
      standards: [authentication.std.yaml, authorization.std.yaml]
      
    - name: sanitize_before_business
      check: "Sanitization must occur before business logic"
      standards: [sanitization.std.yaml, domain.std.yaml]
      
    - name: transaction_covers_writes
      check: "All write operations have transaction boundaries"
      standards: [transaction.std.yaml, storage.std.yaml]
      
    - name: cache_invalidation_matches_writes
      check: "Every cached read has invalidation on corresponding write"
      standards: [cache.std.yaml, invalidation.std.yaml, storage.std.yaml]
      
  # Type consistency
  type_consistency:
    - name: morphism_domains_codomains_exist
      check: "All morphism domain/codomain types are defined"
      
    - name: functor_maps_valid
      check: "Functor object_map and morphism_map reference existing items"
      
    - name: adjunction_functors_compatible
      check: "Adjunction left and right functors have compatible source/target"
```

### 3. Categorical Law Validation

```yaml
categorical_law_checks:
  # Category laws
  category:
    - name: identity_exists
      law: "∀ object A, ∃ id_A: A → A"
      check: "Every declared object has identity morphism"
      
    - name: composition_closed
      law: "∀ f: A → B, g: B → C, ∃ g∘f: A → C"
      check: "Composition of declared morphisms is defined"
      
    - name: composition_associative
      law: "(h ∘ g) ∘ f = h ∘ (g ∘ f)"
      check: "Verify associativity in declared compositions"
      
    - name: identity_laws
      law: "id ∘ f = f = f ∘ id"
      check: "Identity composes correctly"
      
  # Functor laws
  functor:
    - name: preserves_identity
      law: "F(id_A) = id_F(A)"
      check: "Functor maps identity to identity"
      
    - name: preserves_composition
      law: "F(g ∘ f) = F(g) ∘ F(f)"
      check: "Functor preserves morphism composition"
      
  # Adjunction laws
  adjunction:
    - name: unit_exists
      law: "∃ η: Id → R∘L"
      check: "Unit natural transformation defined"
      
    - name: counit_exists
      law: "∃ ε: L∘R → Id"
      check: "Counit natural transformation defined"
      
    - name: left_triangle
      law: "(ε∘L) ∘ (L∘η) = id_L"
      check: "Left triangle identity holds"
      
    - name: right_triangle
      law: "(R∘ε) ∘ (η∘R) = id_R"
      check: "Right triangle identity holds"
      
  # Monad laws
  monad:
    - name: left_identity
      law: "pure(a) >>= f ≡ f(a)"
      check: "Pure followed by bind equals function application"
      
    - name: right_identity
      law: "m >>= pure ≡ m"
      check: "Bind with pure is identity"
      
    - name: associativity
      law: "(m >>= f) >>= g ≡ m >>= (x → f(x) >>= g)"
      check: "Bind is associative"
      
  # Natural transformation laws
  natural_transformation:
    - name: naturality_square
      law: "α_B ∘ F(f) = G(f) ∘ α_A for all f: A → B"
      check: "Naturality squares commute"
```

### 4. Reference Integrity

```yaml
reference_checks:
  # Cross-file references
  cross_file:
    - name: category_references
      check: "All category references point to defined categories"
      
    - name: functor_sources_targets
      check: "Functor source/target categories exist"
      
    - name: morphism_type_refs
      check: "Domain/codomain types are defined"
      
    - name: specification_types
      check: "Types reference specification types (requirements.adt)"
      
  # Internal references
  internal:
    - name: no_undefined_objects
      check: "All referenced objects are declared"
      
    - name: no_undefined_morphisms
      check: "All referenced morphisms are declared"
      
    - name: no_circular_dependencies
      check: "No circular references between standards"
```

## Validation Process

```yaml
validation_process:
  steps:
    - name: parse_all_standards
      action: "Load and parse all .std.yaml files"
      on_error: report_parse_errors
      
    - name: build_reference_graph
      action: "Build graph of all cross-references"
      
    - name: check_completeness
      action: "Run completeness checks"
      blocking: true
      
    - name: check_consistency
      action: "Run consistency checks"
      blocking: true
      
    - name: check_categorical_laws
      action: "Verify all categorical laws"
      blocking: true
      
    - name: check_references
      action: "Verify all references resolve"
      blocking: true
      
    - name: generate_report
      action: "Create validation-report.yaml"
      
    - name: gate_decision
      action: "Decide pass/fail"
```

## Output Schemas

### validation-report.yaml

```yaml
# standards/validation-report.yaml

validation_report:
  timestamp: "2024-01-15T10:30:00Z"
  standards_version: "1.0.0"
  specification_version: "1.0.0"
  
  summary:
    status: pass  # Or: fail
    total_checks: 156
    passed: 154
    failed: 0
    warnings: 2
    
  checks:
    completeness:
      status: pass
      details:
        - check: categories_required
          status: pass
        - check: security_required
          status: pass
        # ...
        
    consistency:
      status: pass
      details:
        - check: auth_before_authz
          status: pass
        # ...
        
    categorical_laws:
      status: pass
      details:
        - category: Domain
          checks:
            - identity_exists: pass
            - composition_associative: pass
        - functor: Repository
          checks:
            - preserves_identity: pass
            - preserves_composition: pass
        - adjunction: "Free ⊣ Repository"
          checks:
            - unit_exists: pass
            - counit_exists: pass
            - left_triangle: pass
            - right_triangle: pass
        # ...
        
    references:
      status: pass
      details:
        - cross_file_refs: pass
        - internal_refs: pass
        
  warnings:
    - file: observability/tracing.std.yaml
      message: "Sampling rate 0.1 may miss important traces"
      suggestion: "Consider increasing for staging environment"
      
    - file: caching/cache.std.yaml
      message: "No cache warming strategy defined"
      suggestion: "Add warming for frequently accessed data"
      
  errors: []  # Empty if status is pass
  
  gate_decision:
    result: proceed
    next_phase: maps_layer
    conditions_met:
      - all_completeness_passed
      - all_consistency_passed
      - all_laws_verified
      - all_references_resolved
```

### versions.yaml

```yaml
# standards/versions.yaml

version: "1.0.0"
created_at: "2024-01-15T10:30:00Z"
specification_version: "1.0.0"

files:
  - path: categories/domain.std.yaml
    hash: "sha256:abc123..."
    status: valid
    
  - path: categories/storage.std.yaml
    hash: "sha256:def456..."
    status: valid
    
  # ... all files

dependencies:
  specifications:
    version: "1.0.0"
    files:
      - requirements.adt
      - architecture.categorical
      
changes_from_previous:
  added:
    - security/tenant-isolation.std.yaml
  modified:
    - caching/cache.std.yaml
  removed: []
  
breaking_changes: false

compatibility:
  backward: true
  forward: false  # New features not in old version
```

## Error Handling

```yaml
error_handling:
  blocking_errors:
    - missing_required_standard
    - categorical_law_violation
    - undefined_reference
    - type_mismatch
    
  warnings:
    - missing_optional_standard
    - suboptimal_configuration
    - unused_definition
    
  on_blocking_error:
    action: fail_gate
    report: detailed_error_with_location
    suggestions: auto_generated_fixes
    
  on_warning:
    action: log_and_continue
    report: in_validation_report
```

## Gate Decision

```yaml
gate_decision:
  pass_criteria:
    - all_required_standards_present
    - no_blocking_errors
    - all_categorical_laws_verified
    - all_references_resolved
    
  fail_reasons:
    - missing: "Required standard X not found"
    - law_violation: "Functor Y does not preserve composition"
    - reference_error: "Type Z referenced but not defined"
    
  on_pass:
    output:
      - versions.yaml
      - validation-report.yaml
    next: maps_layer
    
  on_fail:
    output:
      - validation-report.yaml (with errors)
    action: halt_pipeline
    human_intervention: required
```

## Next Phase

On successful validation:

```
Standards Validator (complete)
         │
         ▼
┌─────────────────────┐
│   maps-architect    │ ← Next orchestrator
└─────────────────────┘
```
