---
name: algebraic-structure-validator
description: Validate ADT correctness by checking algebraic laws (distributivity, commutativity, associativity), categorical structure (products, coproducts, exponentials), and type consistency. Ensures specifications are mathematically sound before proceeding.
allowed-tools: Read, Write, Bash
version: 1.0.0
---

# Algebraic Structure Validator

## Purpose

Validate that ADT specifications from `adt-analyzer` satisfy algebraic laws and categorical properties. This ensures the specification is mathematically sound and implementable.

## Input

```
artifacts/engineering/specifications/v{X}/requirements.adt
```

## Output

```
artifacts/engineering/proofs/architecture/adt-validation/validation-report.json
```

## Validation Layers

### Layer 1: Algebraic Laws

#### Law 1: Distributivity
**Rule:** `a × (b + c) = (a × b) + (a × c)`

**Check:**
```python
# For each product containing a coproduct:
validate_distributivity(expression)

# Example:
# Expression: Tenant × ({Platform} + {AltPlatform})
# Expected expansion:
#   (Tenant × {Platform}) + (Tenant × {AltPlatform})

# Verify: expansion exists and is correct
```

**Test:**
```bash
python {baseDir}/scripts/validate_distributivity.py \
  --adt artifacts/engineering/specifications/v{VERSION}/requirements.adt
```

#### Law 2: Commutativity (where applicable)
**Rule:** `a × b = b × a` (for independent products)

**Check:**
```python
# Products are commutative if order doesn't matter
# Example: Tenant × Platform = Platform × Tenant (both valid)

# However, some products have semantic ordering:
# Credentials → Products ≠ Products → Credentials (functions are NOT commutative)
```

**Test:**
```bash
python {baseDir}/scripts/validate_commutativity.py \
  --adt artifacts/engineering/specifications/v{VERSION}/requirements.adt \
  --check-semantic-ordering
```

#### Law 3: Associativity
**Rule:** `(a × b) × c = a × (b × c)`

**Check:**
```python
# Products group equivalently regardless of parentheses
# Example: (Tenant × Environment) × Platform = Tenant × (Environment × Platform)

validate_associativity(nested_products)
```

**Test:**
```bash
python {baseDir}/scripts/validate_associativity.py \
  --adt artifacts/engineering/specifications/v{VERSION}/requirements.adt
```

#### Law 4: Identity Elements
**Rule:** `a × Unit = a`, `a + Void = a`

**Check:**
```python
# Unit (1) is identity for product: a × 1 = a
# Void (0) is identity for coproduct: a + 0 = a

# Verify no spurious Unit or Void in expressions
```

#### Law 5: Annihilation
**Rule:** `a × Void = Void`

**Check:**
```python
# Any product with Void is Void (impossible path)
# Example: Tenant × Void = Void (no implementation exists)

# Detect and flag impossible paths
```

### Layer 2: Categorical Structure

#### Check 1: Products Well-Formed
**Requirement:** Every product has:
- Universal property (terminal object)
- Projection functions (π₁, π₂)
- Uniqueness of factorization

**Validation:**
```python
def validate_product(product_type):
    # For a × b:
    # 1. Can extract a (π₁: a × b → a)
    # 2. Can extract b (π₂: a × b → b)
    # 3. Can construct from pair (⟨f,g⟩: c → a × b)
    
    assert has_projections(product_type)
    assert has_pairing_function(product_type)
    assert projections_compose_correctly(product_type)
```

**Example:**
```
Type: Tenant × Platform

Projections:
  π₁: (Tenant × Platform) → Tenant
  π₂: (Tenant × Platform) → Platform

Pairing:
  ⟨get_tenant, get_platform⟩: Request → (Tenant × Platform)
```

#### Check 2: Coproducts Well-Formed
**Requirement:** Every coproduct has:
- Universal property (initial object)
- Injection functions (ι₁, ι₂)
- Uniqueness of case analysis

**Validation:**
```python
def validate_coproduct(coproduct_type):
    # For a + b:
    # 1. Can inject a (ι₁: a → a + b)
    # 2. Can inject b (ι₂: b → a + b)
    # 3. Can eliminate via cases ([f,g]: a + b → c)
    
    assert has_injections(coproduct_type)
    assert has_case_analysis(coproduct_type)
    assert injections_compose_correctly(coproduct_type)
```

**Example:**
```
Type: {Platform} + {AltPlatform}

Injections:
  ι₁: {Platform} → ({Platform} + {AltPlatform})
  ι₂: {AltPlatform} → ({Platform} + {AltPlatform})

Case Analysis:
  [sync_{platform}, sync_woo]: ({Platform} + {AltPlatform}) → Products
```

#### Check 3: Exponentials Defined
**Requirement:** Function types (→) have:
- Evaluation map (apply)
- Currying isomorphism

**Validation:**
```python
def validate_exponential(function_type):
    # For b^a (a → b):
    # 1. Can apply: (a → b) × a → b
    # 2. Can curry: (a × b → c) ≅ (a → (b → c))
    
    assert has_evaluation(function_type)
    assert has_curry(function_type)
    assert curry_uncurry_isomorphism(function_type)
```

**Example:**
```
Type: Credentials → Products

Evaluation:
  apply: (Credentials → Products) × Credentials → Products

Currying:
  curry: (Config × Credentials → Products) → (Config → (Credentials → Products))
```

### Layer 3: Type Consistency

#### Check 1: No Undefined Types
**Rule:** All type references must have definitions

**Validation:**
```python
def validate_no_undefined_types(adt):
    defined_types = extract_type_definitions(adt)
    referenced_types = extract_type_references(adt)
    
    undefined = referenced_types - defined_types
    
    if undefined:
        raise ValidationError(f"Undefined types: {undefined}")
```

**Example Error:**
```
Expression: Tenant × Platform
Types defined: [Tenant]
Types referenced: [Tenant, Platform]
Error: Platform is undefined
```

#### Check 2: Recursive Types Have Base Cases
**Rule:** Recursive type definitions must terminate

**Validation:**
```python
def validate_recursive_types(adt):
    for type_def in adt.type_definitions:
        if is_recursive(type_def):
            assert has_base_case(type_def), f"{type_def.name} has no base case"
```

**Example:**
```yaml
# INVALID: No base case
Tree = Node × Tree × Tree

# VALID: Has base case (Leaf)
Tree = Leaf + (Node × Tree × Tree)
```

#### Check 3: No Impossible Paths
**Rule:** No products with Void (a × Void = Void)

**Validation:**
```python
def validate_no_impossible_paths(adt):
    for path in adt.paths:
        if contains_void(path.configuration):
            raise ValidationError(f"Path {path.path_id} contains Void - impossible to implement")
```

**Example:**
```
# INVALID PATH:
path_id: 5
configuration: [Tenant, Void, Platform]
Error: Tenant × Void × Platform = Void (impossible)
```

## Execution Steps

### Step 1: Load ADT

```bash
ADT_FILE="artifacts/engineering/specifications/v{VERSION}/requirements.adt"
python {baseDir}/scripts/load_adt.py --file "$ADT_FILE" --validate-yaml
```

### Step 2: Run Algebraic Law Checks

```bash
python {baseDir}/scripts/validate_laws.py \
  --adt "$ADT_FILE" \
  --laws distributivity,commutativity,associativity,identity,annihilation \
  --output artifacts/engineering/proofs/architecture/adt-validation/laws-check.json
```

Expected output:
```json
{
  "distributivity": "PASS",
  "commutativity": "PASS (semantic ordering respected)",
  "associativity": "PASS",
  "identity": "PASS (no spurious Unit/Void)",
  "annihilation": "PASS (no Void products)"
}
```

### Step 3: Run Categorical Structure Checks

```bash
python {baseDir}/scripts/validate_categorical.py \
  --adt "$ADT_FILE" \
  --checks products,coproducts,exponentials \
  --output artifacts/engineering/proofs/architecture/adt-validation/categorical-check.json
```

Expected output:
```json
{
  "products_well_formed": true,
  "coproducts_well_formed": true,
  "exponentials_defined": true,
  "projections_valid": true,
  "injections_valid": true,
  "case_analysis_complete": true
}
```

### Step 4: Run Type Consistency Checks

```bash
python {baseDir}/scripts/validate_types.py \
  --adt "$ADT_FILE" \
  --checks undefined,recursive,impossible_paths \
  --output artifacts/engineering/proofs/architecture/adt-validation/type-check.json
```

Expected output:
```json
{
  "no_undefined_types": true,
  "recursive_types_valid": true,
  "no_impossible_paths": true,
  "type_definitions_count": 8,
  "type_references_count": 8,
  "all_resolved": true
}
```

### Step 5: Run Property-Based Tests

```bash
python {baseDir}/scripts/property_tests.py \
  --adt "$ADT_FILE" \
  --iterations 10000 \
  --output artifacts/engineering/proofs/architecture/adt-validation/property-tests.json
```

Property tests verify:
1. **Idempotence:** `f(f(x)) = f(x)`
2. **Commutativity:** `f(a, b) = f(b, a)` (where applicable)
3. **Associativity:** `f(f(a, b), c) = f(a, f(b, c))`
4. **Identity:** `f(x, identity) = x`
5. **Annihilation:** `f(x, void) = void`

Expected output:
```json
{
  "total_tests": 10000,
  "passed": 10000,
  "failed": 0,
  "properties_checked": [
    "distributivity",
    "commutativity",
    "associativity",
    "identity",
    "annihilation"
  ]
}
```

### Step 6: Generate Final Report

```bash
python {baseDir}/scripts/generate_validation_report.py \
  --laws artifacts/engineering/proofs/architecture/adt-validation/laws-check.json \
  --categorical artifacts/engineering/proofs/architecture/adt-validation/categorical-check.json \
  --types artifacts/engineering/proofs/architecture/adt-validation/type-check.json \
  --properties artifacts/engineering/proofs/architecture/adt-validation/property-tests.json \
  --output artifacts/engineering/proofs/architecture/adt-validation/validation-report.json
```

## Validation Report Format

```json
{
  "status": "valid",
  "timestamp": "2025-01-15T10:00:00Z",
  "specification_version": "v1.2.0",
  
  "validation_results": {
    "algebraic_laws": {
      "distributivity": true,
      "commutativity": true,
      "associativity": true,
      "identity": true,
      "annihilation": true
    },
    
    "categorical_structure": {
      "products_well_formed": true,
      "coproducts_well_formed": true,
      "exponentials_defined": true,
      "projections_valid": true,
      "injections_valid": true
    },
    
    "type_consistency": {
      "no_undefined_types": true,
      "recursive_types_valid": true,
      "no_impossible_paths": true
    }
  },
  
  "property_tests": {
    "total_iterations": 10000,
    "passed": 10000,
    "failed": 0
  },
  
  "verification_method": "structural_analysis + property_testing",
  
  "summary": "All algebraic laws, categorical structure, and type consistency checks passed. Specification is mathematically sound."
}
```

## Error Handling

### Error 1: Algebraic Law Violation

```json
{
  "status": "invalid",
  "error": "distributivity_violated",
  "details": {
    "expression": "Tenant × ({Platform} + {AltPlatform})",
    "expected_expansion": "(Tenant × {Platform}) + (Tenant × {AltPlatform})",
    "actual_expansion": "Tenant × {Platform}",
    "fix": "Apply distributive law to expand all coproducts"
  }
}
```

**Action:** Regenerate ADT with correct expansion

### Error 2: Undefined Type Reference

```json
{
  "status": "invalid",
  "error": "undefined_type",
  "details": {
    "type": "Platform",
    "referenced_in": "path_3",
    "defined_types": ["Tenant", "Environment", "Version"],
    "fix": "Add Platform type definition to requirements.adt"
  }
}
```

**Action:** Add missing type definition

### Error 3: Impossible Path Detected

```json
{
  "status": "invalid",
  "error": "impossible_path",
  "details": {
    "path_id": 5,
    "configuration": ["Tenant", "Void", "Platform"],
    "reason": "Contains Void - violates annihilation law (a × Void = Void)",
    "fix": "Remove path or replace Void with valid type"
  }
}
```

**Action:** Remove impossible path from ADT

## Success Criteria

Validation passes when:

1. ✅ All algebraic laws satisfied (5/5)
2. ✅ All categorical properties valid (products, coproducts, exponentials)
3. ✅ No undefined types
4. ✅ Recursive types have base cases
5. ✅ No impossible paths (no Void products)
6. ✅ Property tests pass (10,000/10,000)

## Next Steps

After validation:
1. Pass validated ADT to **functor-generator**
2. Use type definitions in **curry-howard-prover**
3. Proceed to system-architect Phase 2 (Composition & Optimization)