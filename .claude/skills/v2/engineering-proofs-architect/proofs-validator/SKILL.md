---
name: proofs-validator
description: |
  Validate all proofs compile and certificates are complete. Gate skill for proofs layer.
  Must pass before proceeding to code layer. Checks Lean compilation, sorry absence,
  certificate completeness, and coverage.
  Input: All proofs/lean/*.lean files, proofs/certificates/*.cert.yaml
  Output: proofs/versions.yaml, proofs/validation-report.yaml
---

# Proofs Validator

Validate proofs and gate to code layer.

## Purpose

Final validation before code layer:
1. All Lean files compile without error
2. No `sorry` or `admit` in proofs
3. All required theorems proven
4. Certificates match proofs
5. Coverage meets threshold

## Input

```
proofs/
├── lean/
│   ├── LeanOS.lean
│   ├── LeanOS/
│   │   ├── Basic.lean
│   │   ├── Category.lean
│   │   ├── Identity.lean
│   │   ├── Composition.lean
│   │   ├── Functor.lean
│   │   ├── Adjunction.lean
│   │   ├── Monad.lean
│   │   ├── NaturalTransformation.lean
│   │   └── Tactics.lean
│   ├── lakefile.lean
│   └── lean-toolchain
└── certificates/
    ├── identity.cert.yaml
    ├── composition.cert.yaml
    ├── functor.cert.yaml
    ├── adjunction.cert.yaml
    ├── monad.cert.yaml
    ├── naturality.cert.yaml
    └── manifest.yaml
```

## Output

```
proofs/
├── versions.yaml          # Version tracking
└── validation-report.yaml # Validation results
```

## Validation Categories

### 1. Compilation Validation

```yaml
compilation_checks:
  lean_build:
    command: "cd proofs/lean && lake build"
    expected: exit_code_0
    timeout: 600  # 10 minutes
    
  no_errors:
    check: "No compilation errors in output"
    
  mathlib_compatible:
    check: "Mathlib imports resolve correctly"
```

### 2. Proof Completeness

```yaml
completeness_checks:
  no_sorry:
    command: "grep -r 'sorry' proofs/lean/LeanOS/"
    expected: no_matches
    severity: blocking
    
  no_admit:
    command: "grep -r 'admit' proofs/lean/LeanOS/"
    expected: no_matches
    severity: blocking
    
  no_axiom_abuse:
    check: "Only expected axioms used"
    allowed_axioms:
      - Classical.choice  # For some mathlib theorems
      - propext           # Propositional extensionality
      - funext            # Function extensionality
      - Quot.sound        # Quotient soundness
```

### 3. Required Theorem Coverage

```yaml
required_theorems:
  # Identity laws
  identity:
    - domain_left_id
    - domain_right_id
    - http_left_id
    - http_right_id
    - storage_left_id
    - storage_right_id
    - kleisli_io_left_id
    - kleisli_io_right_id
    
  # Composition laws
  composition:
    - domain_assoc
    - http_assoc
    - storage_assoc
    - kleisli_io_assoc
    - io_comp_assoc
    - either_comp_assoc
    
  # Functor laws
  functor:
    - http_functor_id
    - http_functor_comp
    - storage_functor_id
    - storage_functor_comp
    - external_functor_id
    - external_functor_comp
    
  # Adjunction laws
  adjunction:
    - repository_adjunction_exists
    - repository_left_triangle
    - repository_right_triangle
    - cache_left_triangle
    - cache_right_triangle
    
  # Monad laws
  monad:
    - io_left_identity
    - io_right_identity
    - io_associativity
    - either_left_identity
    - either_right_identity
    - either_associativity
    - reader_left_identity
    - reader_right_identity
    - reader_associativity
    - transaction_left_identity
    
  # Naturality
  naturality:
    - auth_naturality
    - metrics_naturality
    - tracing_naturality
    - logging_naturality
    - validation_naturality
```

### 4. Certificate Validation

```yaml
certificate_checks:
  # All certificates exist
  certificates_exist:
    required:
      - identity.cert.yaml
      - composition.cert.yaml
      - functor.cert.yaml
      - adjunction.cert.yaml
      - monad.cert.yaml
      - naturality.cert.yaml
      - manifest.yaml
      
  # Certificates match proofs
  certificates_match:
    check: "Each proven theorem has certificate entry"
    
  # Manifest complete
  manifest_complete:
    check: "Manifest references all certificate files"
    
  # Hashes valid
  hashes_valid:
    check: "Certificate hashes match proof file hashes"
```

### 5. Coverage Analysis

```yaml
coverage:
  minimum_threshold: 95%  # 95% of required theorems must be proven
  
  categories:
    identity:
      required: 8
      minimum: 8  # 100% required
      
    composition:
      required: 6
      minimum: 6  # 100% required
      
    functor:
      required: 6
      minimum: 6  # 100% required
      
    adjunction:
      required: 5
      minimum: 5  # 100% required
      
    monad:
      required: 10
      minimum: 9  # 90% allowed (Transaction may have partial)
      
    naturality:
      required: 5
      minimum: 5  # 100% required
```

## Validation Process

```yaml
validation_process:
  steps:
    - name: check_lean_toolchain
      action: "Verify Lean 4 version matches lean-toolchain"
      blocking: true
      
    - name: build_project
      action: "Run `lake build` in proofs/lean/"
      blocking: true
      
    - name: check_no_sorry
      action: "Scan for sorry/admit"
      blocking: true
      
    - name: extract_theorems
      action: "Parse Lean files for theorem declarations"
      
    - name: verify_coverage
      action: "Check all required theorems exist"
      blocking: true
      
    - name: validate_certificates
      action: "Verify certificate files match proofs"
      blocking: true
      
    - name: compute_hashes
      action: "Verify proof hashes match certificates"
      blocking: true
      
    - name: generate_report
      action: "Create validation-report.yaml"
      
    - name: gate_decision
      action: "Decide pass/fail"
```

## Output Schemas

### validation-report.yaml

```yaml
# proofs/validation-report.yaml

validation_report:
  timestamp: "2024-01-15T12:00:00Z"
  proofs_version: "1.0.0"
  maps_version: "1.0.0"
  standards_version: "1.0.0"
  specification_version: "1.0.0"
  
  lean:
    version: "4.3.0"
    mathlib: true
    build_time: "45.2s"
    
  summary:
    status: pass
    total_theorems: 50
    proven: 48
    partial: 2
    axioms: 0
    coverage: 96%
    
  checks:
    compilation:
      status: pass
      details:
        - "lake build: success"
        - "No compilation errors"
        - "Mathlib imports resolved"
        
    completeness:
      status: pass
      details:
        - "No sorry found"
        - "No admit found"
        - "Only allowed axioms used"
        
    coverage:
      status: pass
      by_category:
        identity:
          required: 8
          proven: 8
          coverage: 100%
          
        composition:
          required: 6
          proven: 6
          coverage: 100%
          
        functor:
          required: 6
          proven: 6
          coverage: 100%
          
        adjunction:
          required: 5
          proven: 5
          coverage: 100%
          
        monad:
          required: 10
          proven: 8
          partial: 2
          coverage: 80%
          note: "Transaction monad right_id/assoc are partial"
          
        naturality:
          required: 5
          proven: 5
          coverage: 100%
          
    certificates:
      status: pass
      details:
        - "All certificate files present"
        - "Manifest complete"
        - "Hashes match"
        
  warnings:
    - category: monad
      theorem: transaction_right_identity
      status: partial
      reason: "Requires IO-specific axioms"
      
    - category: monad
      theorem: transaction_associativity
      status: partial
      reason: "Requires IO-specific axioms"
      
  errors: []
  
  gate_decision:
    result: proceed
    next_phase: code_layer
    conditions_met:
      - all_required_compile
      - no_sorry_admit
      - coverage_above_threshold
      - certificates_valid
    notes:
      - "2 partial proofs accepted (Transaction monad)"
```

### versions.yaml

```yaml
# proofs/versions.yaml

version: "1.0.0"
created_at: "2024-01-15T12:00:00Z"
maps_version: "1.0.0"
standards_version: "1.0.0"
specification_version: "1.0.0"

lean:
  version: "4.3.0"
  mathlib_commit: "abc123..."
  
files:
  - path: lean/LeanOS/Identity.lean
    hash: "sha256:abc123..."
    theorems: 8
    
  - path: lean/LeanOS/Composition.lean
    hash: "sha256:def456..."
    theorems: 6
    
  - path: lean/LeanOS/Functor.lean
    hash: "sha256:ghi789..."
    theorems: 8
    
  - path: lean/LeanOS/Adjunction.lean
    hash: "sha256:jkl012..."
    theorems: 6
    
  - path: lean/LeanOS/Monad.lean
    hash: "sha256:mno345..."
    theorems: 12
    
  - path: lean/LeanOS/NaturalTransformation.lean
    hash: "sha256:pqr678..."
    theorems: 10

certificates:
  - path: certificates/manifest.yaml
    hash: "sha256:stu901..."
    
dependencies:
  maps: "1.0.0"
  standards: "1.0.0"
  specifications: "1.0.0"
  
proof_stats:
  total_lines: 2847
  total_theorems: 50
  proven: 48
  partial: 2
  axioms: 0
```

## Error Handling

```yaml
error_handling:
  blocking_errors:
    - compilation_failure
    - sorry_found
    - admit_found
    - required_theorem_missing
    - certificate_mismatch
    
  warnings:
    - partial_proof
    - unused_theorem
    - slow_proof (> 60s)
    
  on_blocking_error:
    action: fail_gate
    report: detailed_error
    suggestions:
      - "Check Lean syntax"
      - "Verify mathlib version"
      - "Complete sorry proofs"
    human_intervention: required
    
  on_warning:
    action: log_and_continue
    include_in_report: true
```

## Gate Decision

```yaml
gate_decision:
  pass_criteria:
    - lean_compiles: true
    - no_sorry: true
    - no_admit: true
    - coverage_met: true (>= 95%)
    - certificates_valid: true
    
  fail_reasons:
    - compilation_error: "Lean build failed"
    - sorry_found: "Incomplete proofs with sorry"
    - coverage_low: "Coverage below threshold"
    - missing_certificate: "Certificate file missing"
    
  on_pass:
    output:
      - versions.yaml
      - validation-report.yaml
    next: code_layer
    
  on_fail:
    output:
      - validation-report.yaml (with errors)
    action: halt_pipeline
    human_intervention: required
```

## Runtime Verification

```yaml
runtime_verification:
  description: |
    Generate runtime checks that can verify properties
    without running Lean at runtime.
    
  generate:
    - property_tests
    - invariant_checks
    - composition_tests
    
  output:
    python: "proofs/runtime/verify.py"
    typescript: "proofs/runtime/verify.ts"
```

## Next Phase

On successful validation:

```
Proofs Validator (complete)
         │
         ▼
┌─────────────────────┐
│   code-architect    │ ← Next orchestrator
└─────────────────────┘
```
