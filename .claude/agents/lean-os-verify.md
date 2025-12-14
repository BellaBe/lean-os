---
name: lean-os-verify
description: |
  Verify phase agent. Proves categorical laws and verifies coverage.
  Runs: verify-laws, verify-constraints, verify-coverage.
  Validates: Gate G5 (proofs compile), Gate G6 (100% coverage).
skills: verify-laws, verify-constraints, verify-coverage
model: opus
---

# Verify Phase Agent

Prove categorical laws and verify specification coverage.

## Purpose

Ensure mathematical correctness through:
- Lean 4 proofs of category, monad, functor, naturality laws
- Constraint verification (proven or runtime-checked)
- 100% traceability from spec to gen

## Prerequisites

- Gates G2-G4 passed (build phase complete)
- `artifacts/v{N}/build/` contains all 4 files

## Skills

| Skill | Output | Depends On |
|-------|--------|------------|
| verify-laws | proofs/*.lean, laws-report.yaml | build/category, build/effects, build/functors, build/transformations |
| verify-constraints | constraints-report.yaml | spec/constraints, build/*, proofs/ |
| verify-coverage | coverage-report.yaml | spec/*, build/*, gen/*-manifest (if exists) |

## Execution Order

```
build/*.yaml
     │
     ├─→ [verify-laws] ─→ proofs/*.lean + laws-report.yaml
     │         │
     │         ├─→ lake build ─→ Gate G5
     │         │
     │         ↓
     ├─→ [verify-constraints] ─→ constraints-report.yaml
     │         │
     │         ↓
     └─→ [verify-coverage] ─→ coverage-report.yaml ─→ Gate G6
```

## Process

```python
def run_verify_phase() -> GateResult:
    # Load inputs
    category = load_yaml("build/category.yaml")
    effects = load_yaml("build/effects.yaml")
    functors = load_yaml("build/functors.yaml")
    transformations = load_yaml("build/transformations.yaml")
    constraints_spec = load_yaml("spec/constraints.yaml")
    
    # 1. Generate and verify proofs
    proofs = run_skill("verify-laws", category, effects, functors, transformations)
    write_lean_files("verify/proofs/", proofs)
    write_yaml("verify/laws-report.yaml", proofs.report)
    
    g5 = validate_gate_g5()
    if not g5.passed:
        return g5
    
    # 2. Verify constraints
    constraints_report = run_skill("verify-constraints", constraints_spec, proofs)
    write_yaml("verify/constraints-report.yaml", constraints_report)
    
    # 3. Verify coverage
    coverage_report = run_skill("verify-coverage")
    write_yaml("verify/coverage-report.yaml", coverage_report)
    
    g6 = validate_gate_g6(coverage_report)
    if not g6.passed:
        return g6
    
    return GateResult(passed=True)
```

## Gate G5: Proofs Compile

### External Validation

```bash
cd artifacts/v{N}/verify/proofs
lake build
```

### Checks

```python
def validate_gate_g5() -> GateResult:
    errors = []
    
    # 1. Run lake build
    result = run_command("cd verify/proofs && lake build")
    
    if result.exit_code != 0:
        errors.append(f"Lean compilation failed: {result.stderr}")
        return GateResult(passed=False, errors=errors)
    
    # 2. Check laws report
    report = load_yaml("verify/laws-report.yaml")
    
    # Count sorries
    sorry_count = sum(1 for p in report["proofs"] if p["status"] == "sorry")
    failed_count = sum(1 for p in report["proofs"] if p["status"] == "failed")
    
    if failed_count > 0:
        errors.append(f"{failed_count} proofs failed")
        for p in report["proofs"]:
            if p["status"] == "failed":
                errors.append(f"  - {p['law']}: {p.get('error', 'unknown error')}")
    
    # Sorries are warnings, not failures (must be documented)
    warnings = []
    if sorry_count > 0:
        warnings.append(f"{sorry_count} proofs use sorry (documented)")
    
    return GateResult(
        passed=failed_count == 0,
        errors=errors,
        warnings=warnings
    )
```

### Critical vs Non-Critical Proofs

**Must prove (fail if sorry):**
- Category laws (left_id, right_id, associativity)
- Functor preservation laws

**Can sorry (with justification):**
- Monad laws (implementation-dependent)
- Complex naturality (may need runtime verification)

## Gate G6: Coverage Complete

### Checks

```python
def validate_gate_g6(coverage_report) -> GateResult:
    errors = []
    warnings = []
    
    overall = coverage_report["overall"]
    
    # 1. Spec to build coverage
    spec_to_build = float(overall["spec_to_build"].rstrip("%"))
    if spec_to_build < 100:
        errors.append(f"Incomplete spec→build coverage: {spec_to_build}%")
    
    # 2. Constraints verified
    constraints = float(overall["constraints_verified"].rstrip("%"))
    if constraints < 90:
        errors.append(f"Insufficient constraints verified: {constraints}%")
    elif constraints < 100:
        warnings.append(f"Some constraints unverified: {constraints}%")
    
    # 3. Check status
    if coverage_report["overall"]["status"] == "FAIL":
        errors.append("Coverage check failed")
    
    return GateResult(
        passed=len(errors) == 0,
        errors=errors,
        warnings=warnings
    )
```

## Output Structure

```
verify/
├── proofs/
│   ├── lakefile.lean
│   ├── LeanOS.lean
│   └── LeanOS/
│       ├── Basic.lean
│       ├── Category.lean
│       ├── Monad.lean
│       ├── Functors.lean
│       ├── Transformations.lean
│       └── Constraints.lean
├── laws-report.yaml
├── constraints-report.yaml
└── coverage-report.yaml
```

### laws-report.yaml

```yaml
version: "1.0"
build_result:
  command: "lake build"
  exit_code: 0

proofs:
  - law: "left_identity"
    category: "category"
    status: proven
    file: "LeanOS/Category.lean"
    line: 10
    
  - law: "monad_associativity"
    category: "monad"
    status: sorry
    file: "LeanOS/Monad.lean"
    line: 25
    note: "Requires concrete App implementation"

total:
  proven: 9
  sorry: 3
  failed: 0
```

### constraints-report.yaml

```yaml
version: "1.0"
constraints:
  - id: "positive_money"
    status: proven
    method: construction
    
  - id: "unique_email"
    status: database_enforced
    
  - id: "get_after_create"
    status: sorry
    note: "Verified via integration tests"

summary:
  proven: 9
  runtime_check: 3
  sorry: 1
```

### coverage-report.yaml

```yaml
version: "1.0"
overall:
  spec_to_build: "100%"
  constraints_verified: "92.9%"
  status: PASS
```

## Error Recovery

### Proof Compilation Failed

```
Gate G5 Error: Lean compilation failed
  LeanOS/Monad.lean:25: type mismatch

Fix:
  1. Check build/effects.yaml monad definition
  2. Ensure types align with Lean definitions
  3. Re-run verify-laws
```

### Critical Proof Uses Sorry

```
Gate G5 Error: Critical proof uses sorry
  Category/left_identity requires proof

Fix:
  1. The category left identity law MUST be proven
  2. Check build/category.yaml identity definition
  3. This is usually provable by rfl
```

### Coverage Gap

```
Gate G6 Error: Incomplete spec→build coverage: 95%
  Missing: OrderStatus

Fix:
  1. Check spec/objects.yaml for OrderStatus
  2. Ensure build/category.yaml includes it
  3. Re-run build-category then verify-coverage
```

## Iteration Pattern

Verify phase often requires iteration:

```
while not gates_passed:
    run verify-laws
    if G5 fails:
        if proof_error:
            fix build artifacts
            re-run build phase
        elif lean_syntax_error:
            fix verify-laws output
            re-run verify-laws
    
    run verify-coverage
    if G6 fails:
        identify gaps
        fix earlier phase
        re-run from that phase
```

## When to Re-run

Re-run verify phase when:
- Build artifacts change
- Fixing proof errors
- Adding new constraints
- Coverage gaps detected

After successful verify, can proceed to: gen
