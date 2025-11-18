---
name: natural-transformation-engine
description: Generate structure-preserving transformations between functorial strategies. Transforms Optional→Replicated, Sync→Async, Pure→Logged while guaranteeing naturality via parametric polymorphism.
---

# Natural Transformation Engine

You are an expert in natural transformations and functorial mappings. Your role is to help users transform between different functorial strategies while preserving naturality.

## Purpose

Generate natural transformations α: F ⇒ G that transform between functors while preserving structure. Naturality is guaranteed automatically through parametric polymorphism.

## Available Resources

- `scripts/natural_transformations.py` - Pre-built transformations between common functors
- `reference/composition.md` - Composition laws and interchange rules

## Core Concept

A **natural transformation** α: F ⇒ G is a family of morphisms:
- For each object A: α_A: F(A) → G(A)
- **Naturality condition**: For all f: A → B, the following square commutes:

```
F(A) --F(f)--> F(B)
 |              |
α_A            α_B
 |              |
 v              v
G(A) --G(f)--> G(B)
```

This means: `G(f) ∘ α_A = α_B ∘ F(f)`

## Common Transformations

### 1. Maybe → List (Optional → Replicated)

```python
def maybe_to_list(maybe_a: Maybe[A]) -> List[A]:
    """α: Maybe ⇒ List"""
    match maybe_a:
        case Nothing:
            return []
        case Just(x):
            return [x]
```

**Use**: Transform optional service to replicated (0 or 1 replica).

### 2. Identity → Future (Sync → Async)

```python
def identity_to_future(x: A) -> Future[A]:
    """α: Identity ⇒ Future"""
    return Future.pure(x)
```

**Use**: Convert synchronous operations to async without changing logic.

### 3. Identity → Writer (Pure → Logged)

```python
def identity_to_writer(x: A) -> Writer[A]:
    """α: Identity ⇒ Writer"""
    return Writer(x, [])  # Value with empty log
```

**Use**: Add logging/auditing to pure functions.

### 4. Either → Maybe (Error Handling → Optional)

```python
def either_to_maybe(either_a: Either[E, A]) -> Maybe[A]:
    """α: Either E ⇒ Maybe"""
    match either_a:
        case Left(_):
            return Nothing
        case Right(x):
            return Just(x)
```

**Use**: Simplify error handling when error details don't matter.

### 5. List → Maybe (Replicated → Optional)

```python
def list_to_maybe(list_a: List[A]) -> Maybe[A]:
    """α: List ⇒ Maybe (take first)"""
    return Just(list_a[0]) if list_a else Nothing
```

**Use**: Select single result from replicated service.

## Composition

### Vertical Composition (Sequential)

Transform through multiple functors sequentially:

```python
# α: F ⇒ G, β: G ⇒ H
# β ⋅ α: F ⇒ H
def vertical_compose(alpha, beta):
    """(β ⋅ α)_A = β_A ∘ α_A"""
    return lambda fa: beta(alpha(fa))
```

**Example**: `Identity → Writer → Future` (add logging, then make async)

### Horizontal Composition (Parallel)

Compose transformations across functor composition:

```python
# α: F ⇒ G, β: H ⇒ K
# β ∘ α: H∘F ⇒ K∘G
def horizontal_compose(alpha, beta):
    """Apply transformations at different levels"""
    return lambda hfa: beta(fmap(alpha)(hfa))
```

**Interchange Law**: `(β' ⋅ α') ∘ (β ⋅ α) = (β' ∘ β) ⋅ (α' ∘ α)`

See [reference/composition.md](reference/composition.md) for details.

## Automatic Naturality

Naturality is guaranteed by parametric polymorphism:

```python
def maybe_to_list(maybe_a: Maybe[A]) -> List[A]:
    # This implementation CANNOT access internals of A
    # Therefore naturality holds automatically
    match maybe_a:
        case Nothing:
            return []
        case Just(x):
            return [x]  # Can only move x, not inspect it
```

**Why**: The transformation can't "peek inside" values, so it must preserve all mappings.

## Validation

While naturality is automatic, validate the square commutes:

```python
from scripts.validate_naturality import validate_naturality

# Test: list.fmap(f) ∘ maybe_to_list = maybe_to_list ∘ maybe.fmap(f)
assert validate_naturality(
    alpha=maybe_to_list,
    functor_f=Maybe,
    functor_g=List,
    test_function=lambda x: x + 1,
    test_values=[Nothing, Just(5), Just(10)]
)
```

## Integration

### With functor-generator

Transform between any generated functors:

```python
from functor_generator import Maybe, List, Either

# Define transformation
alpha = maybe_to_list

# Use with functorial data
maybe_users: Maybe[User] = get_optional_user()
list_users: List[User] = alpha(maybe_users)
```

### With category-theory-foundation

Natural transformations form a category (see reference/composition.md).

## When to Use

✓ **Use natural transformations when:**
- Switching between functorial strategies (sync→async, optional→replicated)
- Migrating system architecture (change error handling, add logging)
- Composing multiple transformations systematically
- Need guaranteed structure preservation

✗ **Don't use when:**
- Transformation is specific to particular data types
- Need to inspect/modify internal structure
- One-off custom conversion suffices

## Best Practices

### 1. Rely on Parametric Polymorphism

```python
# GOOD: Parametrically polymorphic (automatic naturality)
def maybe_to_list(maybe_a: Maybe[A]) -> List[A]:
    match maybe_a:
        case Nothing: return []
        case Just(x): return [x]

# BAD: Type-specific (NOT natural)
def maybe_to_list_bad(maybe_a: Maybe[int]) -> List[int]:
    match maybe_a:
        case Nothing: return []
        case Just(x): return [x * 2]  # Inspects/modifies value!
```

### 2. Compose Transformations

```python
# Chain transformations
identity_to_logged_async = vertical_compose(
    identity_to_writer,  # Add logging
    writer_to_future     # Make async
)
```

### 3. Document Use Cases

```python
def either_to_maybe(either_a: Either[E, A]) -> Maybe[A]:
    """
    Transform Either to Maybe, discarding error details.

    Use when:
    - Error details don't matter for downstream processing
    - Simplifying error handling
    - Interfacing with systems expecting optional values
    """
    ...
```

## Summary

Natural transformations enable systematic migration between functorial strategies while guaranteeing structure preservation through parametric polymorphism. Use for architectural transformations, strategy switching, and composable system evolution.

For functor details, see [functor-generator](../functor-generator/skill.md).
For categorical laws, see [category-theory-foundation](../category-theory-foundation/skill.md).
