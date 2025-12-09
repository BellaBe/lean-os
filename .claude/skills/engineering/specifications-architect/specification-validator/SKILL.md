---
name: specification-validator
description: Validate specification completeness and consistency. Final skill in specification pipeline. Checks all files for cross-references, missing elements, contradictions. Outputs versions.yaml and validation-report.yaml. Gate for proceeding to standards layer.
---

# Specification Validator

Validate that all specification files are complete, consistent, and ready for the standards layer. This is the gate between specification and implementation.

## Input

All specification files:
- `artifacts/engineering/v{X}/specifications/domain-concepts.yaml`
- `artifacts/engineering/v{X}/specifications/requirements.adt`
- `artifacts/engineering/v{X}/specifications/constraints.yaml`
- `artifacts/engineering/v{X}/specifications/services.spec.yaml`
- `artifacts/engineering/v{X}/specifications/state-machines.yaml`
- `artifacts/engineering/v{X}/specifications/architecture.categorical`
- `artifacts/engineering/v{X}/specifications/types.curry-howard`

## Output

Generate:

**`artifacts/engineering/v{X}/specifications/versions.yaml`**
```yaml
version: "1.0.0"
specification_version: X
created_at: "ISO timestamp"
updated_at: "ISO timestamp"

files:
  - name: domain-concepts.yaml
    hash: "sha256"
    status: valid | invalid | warning
  - name: requirements.adt
    hash: "sha256"
    status: valid | invalid | warning
  # ... all files

dependencies:
  - from: requirements.adt
    to: domain-concepts.yaml
    type: derives_from
  - from: services.spec.yaml
    to: requirements.adt
    type: references

compatibility:
  breaking_changes: []
  migrations_required: []
```

**`artifacts/engineering/v{X}/specifications/validation-report.yaml`**
```yaml
version: "1.0"
timestamp: "ISO timestamp"
overall_status: pass | fail | warning

summary:
  total_checks: 50
  passed: 48
  failed: 0
  warnings: 2

checks:
  - category: completeness
    checks:
      - name: check_name
        status: pass | fail | warning
        message: "Description"
        
  - category: consistency
    checks: []
    
  - category: references
    checks: []
    
  - category: categorical
    checks: []

errors: []
warnings: []
recommendations: []
```

## Validation Categories

### 1. Completeness Checks

**Domain Concepts**
```yaml
checks:
  - name: entities_have_identity
    rule: "Every entity has identity field"
    check: "∀e ∈ entities. e.identity ≠ null"
    
  - name: relationships_complete
    rule: "Relationships reference defined entities"
    check: "∀r ∈ relationships. r.from ∈ entities ∧ r.to ∈ entities"
    
  - name: operations_have_types
    rule: "Operations have input/output types"
    check: "∀op ∈ operations. op.input ≠ null ∧ op.output ≠ null"
    
  - name: external_deps_have_operations
    rule: "External dependencies list operations"
    check: "∀d ∈ external_deps. |d.operations| > 0"
```

**Requirements ADT**
```yaml
checks:
  - name: no_undefined_type_refs
    rule: "All type references resolve"
    check: "∀ref ∈ type_refs. ref ∈ defined_types"
    
  - name: products_have_factors
    rule: "Products have at least one factor"
    check: "∀p ∈ products. |p.factors| ≥ 1"
    
  - name: coproducts_have_variants
    rule: "Coproducts have at least two variants"
    check: "∀c ∈ coproducts. |c.variants| ≥ 2"
    
  - name: identifiers_wrap_primitives
    rule: "Identifier types wrap valid primitives"
    check: "∀id ∈ identifiers. id.wraps ∈ {uuid, string, int}"
```

**Services Spec**
```yaml
checks:
  - name: morphisms_have_domain_codomain
    rule: "Morphisms specify domain and codomain"
    check: "∀m ∈ morphisms. m.domain ≠ null ∧ m.codomain ≠ null"
    
  - name: effects_classified
    rule: "IO morphisms have effect classification"
    check: "∀m ∈ morphisms. m.layer = external → m.effects ≠ null"
    
  - name: resilience_for_external
    rule: "External morphisms have resilience"
    check: "∀m ∈ morphisms. m.layer = external → m.resilience ≠ null"
    
  - name: compositions_type_check
    rule: "Composition chains have matching types"
    check: "∀c ∈ compositions. ∀i. c[i].codomain = c[i+1].domain"
```

### 2. Consistency Checks

**Cross-File Consistency**
```yaml
checks:
  - name: adt_matches_domain
    rule: "ADT types derive from domain entities"
    check: "∀t ∈ products. t.derives_from ∈ domain.entities ∪ domain.value_objects"
    
  - name: morphisms_match_operations
    rule: "Morphisms correspond to domain operations"
    check: "∀op ∈ domain.operations. ∃m ∈ morphisms. m.name ≈ op.name"
    
  - name: constraints_reference_types
    rule: "Constraints reference defined types"
    check: "∀c ∈ constraints. c.scope ∈ defined_types"
    
  - name: state_machines_match_entities
    rule: "State machines correspond to lifecycle entities"
    check: "∀sm ∈ state_machines. sm.entity ∈ {e | e.lifecycle = true}"
```

**Categorical Consistency**
```yaml
checks:
  - name: functors_have_valid_source_target
    rule: "Functors reference defined categories"
    check: "∀f ∈ functors. f.source ∈ categories ∧ f.target ∈ categories"
    
  - name: adjunctions_have_functors
    rule: "Adjunctions reference defined functors"
    check: "∀a ∈ adjunctions. a.left ∈ functors ∧ a.right ∈ functors"
    
  - name: monads_are_endofunctors
    rule: "Monads are endofunctors"
    check: "∀m ∈ monads. m.functor.source = m.functor.target"
```

### 3. Reference Integrity Checks

```yaml
checks:
  - name: no_dangling_refs
    rule: "All references resolve to definitions"
    check: |
      ∀file ∈ files.
        ∀ref ∈ file.references.
          ∃def ∈ all_definitions.
            ref.target = def.name
    
  - name: no_circular_ownership
    rule: "Ownership relationships are acyclic"
    check: "¬∃cycle ∈ ownership_graph"
    
  - name: module_deps_acyclic
    rule: "Module dependencies form DAG"
    check: "¬∃cycle ∈ module_dependency_graph"
```

### 4. Categorical Law Checks

```yaml
checks:
  - name: identity_morphisms_exist
    rule: "Every object has identity morphism"
    check: "∀obj ∈ category.objects. ∃id_obj ∈ morphisms"
    
  - name: composition_closed
    rule: "Composable morphisms have composition"
    check: |
      ∀f: A → B, g: B → C.
        ∃(g∘f): A → C
    
  - name: kleisli_category_valid
    rule: "Kleisli morphisms form category"
    check: |
      ∀m ∈ kleisli_morphisms.
        m.kleisli_category ∈ {IO, Either, IO_Either, Pure}
```

### 5. Proof Obligation Completeness

```yaml
checks:
  - name: constraints_have_proofs
    rule: "All constraints have proof obligations"
    check: |
      ∀c ∈ constraints.
        ∃po ∈ proof_obligations.
          po.source = c.name
    
  - name: categorical_laws_have_proofs
    rule: "Categorical laws have proof obligations"
    check: |
      ∀law ∈ categorical_laws.
        ∃po ∈ proof_obligations.
          po.name = law.name
    
  - name: types_are_inhabited
    rule: "Dependent types have inhabitants"
    check: |
      ∀dt ∈ dependent_types.
        ∃inh ∈ type_inhabitants.
          inh.type = dt.name
```

## Validation Process

```
1. Parse all specification files
   ↓
2. Build reference graph
   ↓
3. Run completeness checks
   ↓
4. Run consistency checks
   ↓
5. Run reference integrity checks
   ↓
6. Run categorical law checks
   ↓
7. Run proof obligation checks
   ↓
8. Generate validation report
   ↓
9. Generate versions.yaml
   ↓
10. Gate decision: pass/fail
```

## Error Handling

**Blocking Errors (fail validation)**
- Missing required fields
- Undefined type references
- Circular dependencies
- Missing proof obligations for laws

**Warnings (pass with notes)**
- Unused types
- Empty collections
- Missing optional fields
- Complexity warnings

## Recommendations

Generate actionable recommendations:

```yaml
recommendations:
  - category: performance
    issue: "Large number of morphisms in single module"
    suggestion: "Consider splitting module into submodules"
    affected: [analysis_module]
    
  - category: completeness
    issue: "Entity without CRUD operations"
    suggestion: "Add standard CRUD morphisms"
    affected: [Settings]
    
  - category: resilience
    issue: "External dependency without circuit breaker"
    suggestion: "Add circuit breaker configuration"
    affected: [custom_api_call]
```

## Version Tracking

**Semantic Versioning**
- MAJOR: Breaking changes to types or morphisms
- MINOR: New types, morphisms, or modules
- PATCH: Documentation, constraints, clarifications

**Breaking Change Detection**
```yaml
breaking_changes:
  - type: type_removed
    affected: TypeName
    
  - type: field_removed
    affected: TypeName.field
    
  - type: morphism_signature_changed
    affected: morphism_name
    old_signature: "A → B"
    new_signature: "A → C"
```

## Gate Decision

```yaml
gate:
  decision: pass | fail
  
  pass_criteria:
    - all_completeness_checks: pass
    - all_consistency_checks: pass
    - all_reference_checks: pass
    - all_categorical_checks: pass
    - proof_coverage: "> 95%"
    
  fail_reasons: []
  
  next_phase: standards  # If pass
```

## Validation Checklist

Before approving, verify:

- [ ] All files parse without errors
- [ ] No undefined references
- [ ] No circular dependencies
- [ ] Types are inhabited
- [ ] Categorical laws are complete
- [ ] Proof obligations cover constraints
- [ ] Version is properly incremented

## Output to Standards Layer

On pass, the specification is ready for:
- **standardization-definer** → extract universal properties
- Map generation → implementation strategies
- Proof generation → Lean 4 verification
