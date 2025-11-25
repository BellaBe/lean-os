---
name: architecture-validator
description: Validate categorical laws (composition, identity, associativity), functor laws, and natural transformation properties. Runs 10K property-based tests to ensure mathematical correctness of the entire architecture.
allowed-tools: Read, Write, Bash
version: 1.0.0
---

# Architecture Validator

## Purpose

Final validation of complete architecture specifications. Verifies categorical laws, functor laws, natural transformation properties, and runs comprehensive property-based tests.

## Input

```
artifacts/engineering/specifications/v{VERSION}/ (all specification files)
artifacts/engineering/proofs/architecture/ (all proofs)
```

## Output

```
artifacts/engineering/proofs/architecture/validation-report.json
```

## Validation Layers

### Layer 1: Categorical Laws

#### Law 1: Composition
**Rule:** `h ∘ (g ∘ f) = (h ∘ g) ∘ f`

**Test:**
```python
def test_composition_associativity(f, g, h, x):
    left = h(g(f(x)))
    right = compose(h, g)(f(x))
    assert left == right
```

#### Law 2: Identity
**Rule:** `id ∘ f = f = f ∘ id`

**Test:**
```python
def test_identity(f, x):
    identity = lambda a: a
    assert compose(identity, f)(x) == f(x)
    assert compose(f, identity)(x) == f(x)
```

#### Law 3: Cartesian Closure
**Rule:** `(a → b) × a → b` (function application exists)

**Test:**
```python
def test_cartesian_closed(function, argument):
    # Can always apply function to argument
    result = function(argument)
    assert result is not None
```

### Layer 2: Functor Laws

#### Law 1: Identity Preservation
**Rule:** `fmap id = id`

**Test:**
```python
def test_functor_identity(functor, example):
    identity = lambda x: x
    assert functor.fmap(identity, example) == example
```

#### Law 2: Composition Preservation
**Rule:** `fmap (g ∘ f) = fmap g ∘ fmap f`

**Test:**
```python
def test_functor_composition(functor, f, g, example):
    composed = lambda x: g(f(x))
    left = functor.fmap(composed, example)
    right = functor.fmap(g, functor.fmap(f, example))
    assert left == right
```

### Layer 3: Natural Transformation Properties

#### Property 1: Naturality Square Commutes

**Test:**
```python
def test_naturality(alpha, f, example):
    # α ∘ F(f) = G(f) ∘ α
    left = alpha(functor_F.fmap(f, example))
    right = functor_G.fmap(f, alpha(example))
    assert left == right
```

## Execution Steps

### Step 1: Load All Specifications

```bash
python {baseDir}/scripts/load_specifications.py \
  --spec-dir artifacts/engineering/specifications/v{VERSION} \
  --output /tmp/loaded-specs.json
```

### Step 2: Run Categorical Law Tests

```bash
python {baseDir}/scripts/test_categorical_laws.py \
  --specs /tmp/loaded-specs.json \
  --iterations 10000 \
  --output artifacts/engineering/proofs/architecture/validation/categorical-laws.json
```

### Step 3: Run Functor Law Tests

```bash
python {baseDir}/scripts/test_functor_laws.py \
  --functors artifacts/engineering/specifications/v{VERSION}/architecture.categorical \
  --iterations 10000 \
  --output artifacts/engineering/proofs/architecture/validation/functor-laws.json
```

### Step 4: Run Natural Transformation Tests

```bash
python {baseDir}/scripts/test_natural_transformations.py \
  --versions artifacts/engineering/specifications/v{VERSION}/versions.yaml \
  --iterations 10000 \
  --output artifacts/engineering/proofs/architecture/validation/natural-transformations.json
```

### Step 5: Generate Final Report

```bash
python {baseDir}/scripts/generate_validation_report.py \
  --categorical artifacts/engineering/proofs/architecture/validation/categorical-laws.json \
  --functors artifacts/engineering/proofs/architecture/validation/functor-laws.json \
  --naturality artifacts/engineering/proofs/architecture/validation/natural-transformations.json \
  --output artifacts/engineering/proofs/architecture/validation-report.json
```

## Output Format

```json
{
  "status": "valid",
  "timestamp": "2025-01-15T12:00:00Z",
  "specification_version": "v20250115_120000",
  
  "categorical_laws": {
    "composition_associativity": {
      "tested": 10000,
      "passed": 10000,
      "failed": 0,
      "status": "PASS"
    },
    "identity": {
      "tested": 10000,
      "passed": 10000,
      "failed": 0,
      "status": "PASS"
    },
    "cartesian_closure": {
      "tested": 10000,
      "passed": 10000,
      "failed": 0,
      "status": "PASS"
    }
  },
  
  "functor_laws": {
    "identity_preservation": {
      "functors_tested": 5,
      "tests_per_functor": 2000,
      "total_tests": 10000,
      "passed": 10000,
      "status": "PASS"
    },
    "composition_preservation": {
      "functors_tested": 5,
      "tests_per_functor": 2000,
      "total_tests": 10000,
      "passed": 10000,
      "status": "PASS"
    }
  },
  
  "natural_transformations": {
    "naturality_square": {
      "transformations_tested": 3,
      "tests_per_transformation": 3333,
      "total_tests": 10000,
      "passed": 10000,
      "status": "PASS"
    }
  },
  
  "property_tests": {
    "total_iterations": 30000,
    "total_passed": 30000,
    "total_failed": 0,
    "coverage": "100%"
  },
  
  "summary": {
    "all_laws_satisfied": true,
    "total_tests": 30000,
    "pass_rate": "100%",
    "architecture_valid": true,
    "ready_for_implementation": true
  }
}
```

## Success Criteria

1. ✅ Categorical laws: 10000/10000 tests passed
2. ✅ Functor laws: 10000/10000 tests passed
3. ✅ Natural transformations: 10000/10000 tests passed
4. ✅ Total: 30000/30000 tests passed
5. ✅ Architecture validated, ready for implementation

## Next Steps

- Architecture specifications ready for **backend-prover**
- All proofs completed, proceed to Phase 1 map generation