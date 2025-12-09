---
name: maps-validator
description: |
  Validate all maps for completeness, categorical correspondence, and target consistency.
  Gate skill for maps layer - must pass before proceeding to proofs layer.
  Checks that maps preserve categorical structure and generate valid code.
  Input: All maps/*.map.yaml files
  Output: maps/versions.yaml, maps/validation-report.yaml
---

# Maps Validator

Validate maps and gate to proofs layer.

## Purpose

Final validation before proofs layer:
1. Completeness validation (all standards covered)
2. Categorical correspondence (structure preserved)
3. Target consistency (all targets have same patterns)
4. Code generation validation (templates valid)
5. Version tracking and gate decision

## Input

All map files:
```
maps/
├── primitives/
│   ├── types.map.yaml
│   └── identifiers.map.yaml
├── kleisli/
│   ├── effects.map.yaml
│   └── interpreters.map.yaml
├── adjunctions/
│   ├── repository.map.yaml
│   ├── cache.map.yaml
│   └── external.map.yaml
├── functors/
│   ├── http.map.yaml
│   ├── storage.map.yaml
│   └── external.map.yaml
├── transformations/
│   ├── middleware.map.yaml
│   ├── auth.map.yaml
│   └── observability.map.yaml
├── monads/
│   ├── io.map.yaml
│   ├── either.map.yaml
│   ├── reader.map.yaml
│   └── transaction.map.yaml
└── modules/
    ├── services.map.yaml
    ├── repositories.map.yaml
    └── handlers.map.yaml
```

## Output

```
maps/
├── versions.yaml          # Version tracking
└── validation-report.yaml # Validation results
```

## Validation Categories

### 1. Completeness Validation

```yaml
completeness_checks:
  # Coverage of standards
  standards_coverage:
    categories:
      required: [domain, storage, http]
      optional: [external]
      checks:
        - every_category_has_functor_map
        - every_adjunction_has_implementation
        
    security:
      required: [authentication, authorization]
      checks:
        - auth_transformation_mapped
        - middleware_chain_complete
        
    observability:
      checks:
        - metrics_transformation_mapped
        - tracing_transformation_mapped
        
    caching:
      checks:
        - cache_adjunction_mapped
        - invalidation_patterns_defined
        
    transactions:
      checks:
        - transaction_monad_mapped
        - saga_pattern_if_required
        
  # Coverage of specifications
  specification_coverage:
    types:
      - every_adt_type_has_primitive_mapping
      - every_identifier_has_newtype
      
    morphisms:
      - every_morphism_has_kleisli_mapping
      - every_effect_has_interpreter
      
    services:
      - every_service_has_module_mapping
      - every_repository_has_implementation
      - every_handler_has_endpoint
```

### 2. Categorical Correspondence

```yaml
categorical_checks:
  # Functor laws
  functor_laws:
    - name: identity_preserved
      check: "F(id_A) maps to identity implementation"
      for: [http, storage, external]
      
    - name: composition_preserved
      check: "F(g ∘ f) = F(g) ∘ F(f) in implementation"
      for: [http, storage, external]
      
  # Adjunction laws
  adjunction_laws:
    - name: unit_counit_exist
      check: "Both η and ε have implementations"
      for: [repository, cache]
      
    - name: triangle_identities
      check: "Implementation respects (ε∘L)∘(L∘η) = id"
      for: [repository, cache]
      
  # Monad laws
  monad_laws:
    - name: pure_bind_defined
      check: "Both pure and bind have implementations"
      for: [io, either, reader, transaction]
      
    - name: left_identity
      check: "pure(a) >>= f ≡ f(a) holds"
      for: [io, either, reader, transaction]
      
    - name: right_identity
      check: "m >>= pure ≡ m holds"
      for: [io, either, reader, transaction]
      
    - name: associativity
      check: "(m >>= f) >>= g ≡ m >>= (x → f(x) >>= g)"
      for: [io, either, reader, transaction]
      
  # Natural transformation laws
  transformation_laws:
    - name: naturality
      check: "α_B ∘ F(f) = G(f) ∘ α_A"
      for: [auth, validation, metrics, tracing]
      
    - name: composition_natural
      check: "Composed transformations are natural"
      for: [middleware_chain]
```

### 3. Target Consistency

```yaml
target_consistency:
  # All targets implement same abstract pattern
  abstract_pattern:
    - name: same_signatures
      check: "All targets have equivalent type signatures"
      
    - name: same_semantics
      check: "All targets implement same behavior"
      
  # Cross-target checks
  cross_target:
    - name: no_missing_targets
      check: "If python mapped, typescript also mapped (for required)"
      
    - name: template_variables_match
      check: "All template variables have values"
      
  # Per-target validation
  per_target:
    python:
      - syntax_valid
      - imports_resolvable
      - type_hints_present
      
    typescript:
      - syntax_valid
      - types_complete
      - imports_resolvable
      
    go:
      - syntax_valid
      - types_complete
      - package_structure_valid
```

### 4. Code Generation Validation

```yaml
code_generation:
  # Template validation
  templates:
    - name: variables_defined
      check: "All {variable} placeholders have mappings"
      
    - name: syntax_valid
      check: "Generated code parses correctly"
      
    - name: imports_complete
      check: "All imports are specified"
      
  # Structure validation
  structure:
    - name: module_paths_valid
      check: "All file paths are valid"
      
    - name: no_circular_imports
      check: "Import graph is acyclic"
      
    - name: naming_consistent
      check: "Names follow conventions"
      
  # Semantic validation
  semantic:
    - name: types_match
      check: "Input/output types align"
      
    - name: effects_handled
      check: "All effects have handlers"
      
    - name: errors_propagated
      check: "Error types flow correctly"
```

### 5. Reference Integrity

```yaml
reference_checks:
  # Cross-map references
  cross_map:
    - primitives_referenced_correctly
    - kleisli_uses_valid_effects
    - modules_reference_valid_functors
    
  # Standards references
  standards:
    - all_standard_refs_exist
    - functor_source_target_match
    
  # Specification references
  specifications:
    - all_type_refs_exist
    - all_morphism_refs_exist
```

## Validation Process

```yaml
validation_process:
  steps:
    - name: parse_all_maps
      action: "Load and parse all .map.yaml files"
      on_error: report_parse_errors
      
    - name: build_reference_graph
      action: "Build graph of cross-references"
      
    - name: check_completeness
      action: "Verify all required maps present"
      blocking: true
      
    - name: check_categorical_laws
      action: "Verify categorical structure preserved"
      blocking: true
      
    - name: check_target_consistency
      action: "Verify all targets consistent"
      blocking: true
      
    - name: validate_code_generation
      action: "Test code generation templates"
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
# maps/validation-report.yaml

validation_report:
  timestamp: "2024-01-15T12:00:00Z"
  maps_version: "1.0.0"
  standards_version: "1.0.0"
  specification_version: "1.0.0"
  
  summary:
    status: pass
    total_checks: 248
    passed: 245
    failed: 0
    warnings: 3
    
  checks:
    completeness:
      status: pass
      details:
        - check: standards_coverage
          status: pass
          covered: [domain, storage, http, security, observability, caching]
        - check: specification_coverage
          status: pass
          types_mapped: 24
          morphisms_mapped: 48
          
    categorical_correspondence:
      status: pass
      details:
        - category: functor_laws
          checks:
            - "HTTP functor: identity preserved ✓"
            - "HTTP functor: composition preserved ✓"
            - "Storage functor: identity preserved ✓"
            - "Storage functor: composition preserved ✓"
        - category: adjunction_laws
          checks:
            - "Repository: unit exists ✓"
            - "Repository: counit exists ✓"
            - "Repository: left triangle ✓"
            - "Repository: right triangle ✓"
            - "Cache: unit exists ✓"
            - "Cache: counit exists ✓"
        - category: monad_laws
          checks:
            - "IO: pure defined ✓"
            - "IO: bind defined ✓"
            - "Either: laws implementable ✓"
            - "Transaction: laws implementable ✓"
        - category: transformation_laws
          checks:
            - "Auth: naturality ✓"
            - "Metrics: naturality ✓"
            
    target_consistency:
      status: pass
      targets:
        - python: complete
        - typescript: complete
        - go: partial  # Optional
      details:
        - all_abstracts_have_python: true
        - all_abstracts_have_typescript: true
        
    code_generation:
      status: pass
      templates_valid: 42
      syntax_errors: 0
      
    references:
      status: pass
      cross_map_refs: valid
      standards_refs: valid
      specification_refs: valid
      
  warnings:
    - map: modules/services.map.yaml
      message: "Some services have no external dependencies"
      suggestion: "Verify these are pure domain services"
      
    - map: kleisli/effects.map.yaml
      message: "Go target missing for composed effects"
      suggestion: "Add Go implementation if Go target needed"
      
    - map: adjunctions/cache.map.yaml
      message: "TTL values not parameterized"
      suggestion: "Consider making TTL configurable"
      
  errors: []
  
  gate_decision:
    result: proceed
    next_phase: proofs_layer
    conditions_met:
      - all_completeness_passed
      - all_categorical_laws_verified
      - all_targets_consistent
      - code_generation_valid
```

### versions.yaml

```yaml
# maps/versions.yaml

version: "1.0.0"
created_at: "2024-01-15T12:00:00Z"
specification_version: "1.0.0"
standards_version: "1.0.0"

files:
  - path: primitives/types.map.yaml
    hash: "sha256:abc123..."
    status: valid
    
  - path: primitives/identifiers.map.yaml
    hash: "sha256:def456..."
    status: valid
    
  # ... all files

targets:
  - name: python
    version: "3.11+"
    coverage: complete
    
  - name: typescript
    version: "5.0+"
    coverage: complete
    
  - name: go
    version: "1.21+"
    coverage: partial

dependencies:
  standards:
    version: "1.0.0"
  specifications:
    version: "1.0.0"
    
changes_from_previous:
  added: []
  modified: []
  removed: []
  
breaking_changes: false
```

## Error Handling

```yaml
error_handling:
  blocking_errors:
    - missing_required_map
    - categorical_law_violation
    - template_syntax_error
    - undefined_reference
    - type_mismatch
    
  warnings:
    - missing_optional_target
    - suboptimal_pattern
    - unused_mapping
    
  on_blocking_error:
    action: fail_gate
    report: detailed_error_with_location
    suggestions: auto_generated_fixes
    human_intervention: required
    
  on_warning:
    action: log_and_continue
    report: in_validation_report
```

## Gate Decision

```yaml
gate_decision:
  pass_criteria:
    - all_required_maps_present
    - all_categorical_laws_verified
    - all_targets_consistent
    - code_generation_valid
    - all_references_resolved
    
  fail_reasons:
    - missing: "Required map X not found"
    - law_violation: "Functor Y doesn't preserve composition"
    - template_error: "Template Z has syntax error"
    - reference_error: "Type W referenced but not defined"
    
  on_pass:
    output:
      - versions.yaml
      - validation-report.yaml
    next: proofs_layer
    
  on_fail:
    output:
      - validation-report.yaml (with errors)
    action: halt_pipeline
    human_intervention: required
```

## Next Phase

On successful validation:

```
Maps Validator (complete)
         │
         ▼
┌─────────────────────┐
│  proofs-architect   │ ← Next orchestrator
└─────────────────────┘
```
