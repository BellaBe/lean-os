---
name: architecture-validator
description: Validate system architecture for categorical correctness. Use to verify composition, check for initial/terminal objects, validate functor laws, ensure cartesian closure. Prevents broken composition and structural errors.
---

# Architecture Validator

You are an expert in validating system architectures against categorical laws. Your role is to help users verify their systems satisfy mathematical correctness properties.

## Purpose

Validate system architecture satisfies category theory laws. Catch composition errors, missing identities, broken functor laws, and structural violations before deployment.

## Available Resources

- `scripts/validate.py` - Comprehensive validation engine for all categorical laws
- `examples/composition-validation.md` - Examples of fixing common violations

## Validation Checks

### 1. Category Laws

**Identity**: Every object has an identity morphism
```python
for service in services:
    assert exists(identity(service))
    assert compose(f, identity) == f
    assert compose(identity, f) == f
```

**Composition**: All service chains compose correctly
```python
for f: A → B, g: B → C:
    assert composable(f, g)  # Types align
    assert exists(compose(g, f))  # Composition exists
```

**Associativity**: Composition order doesn't matter
```python
for f: A → B, g: B → C, h: C → D:
    assert compose(h, compose(g, f)) == compose(compose(h, g), f)
```

### 2. Functor Laws

**Identity Preservation**: F(id) = id
```python
for functor F, object A:
    assert F(identity(A)) == identity(F(A))
```

**Composition Preservation**: F(g ∘ f) = F(g) ∘ F(f)
```python
for functor F, f: A → B, g: B → C:
    assert F(compose(g, f)) == compose(F(g), F(f))
```

### 3. Universal Constructions

**Products**: Must have projections satisfying universal property
```python
for product P of (A, B):
    assert exists(π₁: P → A)  # First projection
    assert exists(π₂: P → B)  # Second projection
    # Universal property: unique morphism from any object with maps to A, B
```

**Coproducts**: Must have injections satisfying universal property
```python
for coproduct C of (A, B):
    assert exists(ι₁: A → C)  # First injection
    assert exists(ι₂: B → C)  # Second injection
```

**Exponentials**: Must have eval and curry
```python
for exponential B^A:
    assert exists(eval: B^A × A → B)
    assert exists(curry: (C × A → B) → (C → B^A))
```

### 4. Cartesian Closure

**Terminal Object**: Universal target
```python
assert exists(terminal_object)
for object A:
    assert unique_morphism(A, terminal_object)
```

**Products Exist**: For all pairs
```python
for objects A, B:
    assert exists(product(A, B))
```

**Exponentials Exist**: Internal homs
```python
for objects A, B:
    assert exists(exponential(B, A))  # B^A
```

### 5. Type Safety

**Type Alignment**: All compositions type-check
```python
for f: A → B, g: C → D:
    if B == C:
        assert composable(f, g)
    else:
        assert not composable(f, g)
```

**No Orphan Services**: All services have source and target
```python
for service S:
    assert exists(source(S))
    assert exists(target(S))
```

## Validation Process

### Step 1: Parse Architecture

```python
from scripts.validate import parse_architecture

arch = parse_architecture("architecture.yaml")
# Extract services, compositions, types
```

### Step 2: Run Validation

```python
from scripts.validate import validate

report = validate(arch, checks=[
    'identity',
    'composition',
    'associativity',
    'functor_laws',
    'universal_constructions',
    'cartesian_closure'
])
```

### Step 3: Review Report

```python
if report.passed:
    print("✓ Architecture is categorically correct")
else:
    for violation in report.violations:
        print(f"✗ {violation.law}: {violation.description}")
        print(f"  Fix: {violation.suggested_fix}")
```

## Common Violations

### Violation: Missing Identity

```python
# ERROR: Service has no identity
ServiceA → ServiceB  # No identity for ServiceA

# FIX: Add identity service
identity(ServiceA): ServiceA → ServiceA
```

### Violation: Broken Composition

```python
# ERROR: Types don't align
ServiceA: Request → User
ServiceB: Product → Order
compose(ServiceB, ServiceA)  # User ≠ Product!

# FIX: Add adapter or fix types
Adapter: User → Product
compose(ServiceB, compose(Adapter, ServiceA))  # OK
```

### Violation: Functor Law Failure

```python
# ERROR: Functor doesn't preserve identity
F(identity(A)) ≠ identity(F(A))

# FIX: Correct functor implementation
class CorrectFunctor:
    def fmap(self, f):
        if is_identity(f):
            return identity  # Preserve identity
        return ...
```

### Violation: Missing Terminal Object

```python
# ERROR: No universal terminal service
# Multiple services with no common target

# FIX: Add unit service as terminal object
UnitService: * → Unit  # Terminal object
```

### Violation: Product Missing Projections

```python
# ERROR: Product exists but no projections
Product(ServiceA, ServiceB)  # No π₁, π₂

# FIX: Add projection services
π₁: Product(ServiceA, ServiceB) → ServiceA
π₂: Product(ServiceA, ServiceB) → ServiceB
```

## Integration

### With category-theory-foundation

Laws defined in category-theory-foundation, validated here:

```python
from category_theory_foundation import CATEGORY_LAWS

for law in CATEGORY_LAWS:
    assert validate_law(architecture, law)
```

### With functor-generator

Validate generated functors:

```python
from functor_generator import generate_functor
from architecture_validator import validate_functor

F = generate_functor(FunctorType.READER)
assert validate_functor(F)  # Checks identity + composition laws
```

### With free-category-constructor

Validate constructed categories:

```python
from free_category import construct_free_category
from architecture_validator import validate_category

cat = construct_free_category(graph)
assert validate_category(cat)  # Checks all category laws
```

## Validation Reports

Example report:

```
Architecture Validation Report
==============================

✓ Identity Law: PASSED (12/12 services have identity)
✓ Composition: PASSED (All 45 compositions type-check)
✓ Associativity: PASSED (Tested 23 chains)
✗ Functor Laws: FAILED (2 violations)
  - ReaderFunctor: Identity law violated
    Fix: Ensure F(id) returns identity morphism
  - MaybeFunctor: Composition law violated
    Fix: Check fmap implementation preserves composition
✓ Universal Constructions: PASSED
✓ Cartesian Closure: PASSED (Terminal object exists, products exist)

Score: 5/6 checks passed
Status: FAILED - Fix functor violations before deployment
```

## When to Use

✓ **Use architecture validator when:**
- Before deploying new architecture
- After refactoring service composition
- Integrating generated functors
- Building new categories
- Ensuring mathematical correctness
- CI/CD pipeline validation

✗ **Don't use when:**
- Architecture is trivial (single service)
- No composition or functors involved
- Prototyping (validate later)

## Best Practices

### 1. Validate Early and Often

```bash
# In CI/CD pipeline
python scripts/validate.py --arch architecture.yaml --strict
```

### 2. Fix Violations Immediately

Don't deploy architectures with violations - they will break at runtime.

### 3. Use Incremental Validation

```python
# Validate each component as added
validate_service(new_service)
validate_composition(service_a, service_b)
```

### 4. Generate Validation Tests

```python
# Auto-generate property tests from laws
for law in CATEGORY_LAWS:
    generate_test(architecture, law)
```

## Summary

Architecture validator ensures system architectures satisfy category theory laws, catching composition errors, missing identities, broken functor laws, and structural violations before they cause runtime failures.

For validation examples, see:
- [examples/composition-validation.md](examples/composition-validation.md)
- [examples/functor-validation.md](examples/functor-validation.md)
