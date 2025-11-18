# Natural Transformation Composition

## Composition Operations

Natural transformations compose in two ways:

### 1. Vertical Composition (Sequential)

Given:
- α: F ⇒ G
- β: G ⇒ H

Vertical composition β ⋅ α: F ⇒ H is defined:

```
(β ⋅ α)_A = β_A ∘ α_A
```

**Diagram**:
```
F(A) --α_A--> G(A) --β_A--> H(A)

    =

F(A) -------β⋅α-------> H(A)
```

**Example**: Transform sync → logged → async
```python
sync_to_logged = identity_to_writer  # Identity ⇒ Writer
logged_to_async = writer_to_future   # Writer ⇒ Future

sync_to_async = vertical_compose(sync_to_logged, logged_to_async)
# Identity ⇒ Future
```

**Properties**:
- Associative: (γ ⋅ β) ⋅ α = γ ⋅ (β ⋅ α)
- Identity: id ⋅ α = α ⋅ id = α

### 2. Horizontal Composition (Parallel)

Given:
- α: F ⇒ G (inner functors)
- β: H ⇒ K (outer functors)

Horizontal composition β ∘ α: H∘F ⇒ K∘G is defined:

```
(β ∘ α)_A = β_G(A) ∘ H(α_A) = K(α_A) ∘ β_F(A)
```

**Diagram**:
```
H(F(A)) --H(α_A)--> H(G(A))
   |                   |
β_F(A)              β_G(A)
   |                   |
   v                   v
K(F(A)) --K(α_A)--> K(G(A))
```

Both paths are equal by naturality.

**Example**: Maybe[List[A]] → Either[List[A]]
```python
maybe_to_either = ...        # Maybe ⇒ Either
list_identity = ...          # List ⇒ List

# Transforms Maybe[List[A]] → Either[List[A]]
composed = horizontal_compose(list_identity, maybe_to_either)
```

## Interchange Law

The interchange law relates vertical and horizontal composition:

```
(β' ⋅ α') ∘ (β ⋅ α) = (β' ∘ β) ⋅ (α' ∘ α)
```

**Meaning**: Composing then applying is the same as applying then composing.

**Proof Sketch**:

Given transformations:
```
F --α--> G --α'--> G'
H --β--> K --β'--> K'
```

Left side (compose vertically first, then horizontally):
```
(β' ⋅ β) ∘ (α' ⋅ α) = β'_G' ∘ β_G ∘ α'_A ∘ α_A
```

Right side (compose horizontally first, then vertically):
```
(β' ∘ α') ⋅ (β ∘ α) = β'_G' ∘ α'_A ∘ β_G ∘ α_A
```

By naturality of α' with respect to β:
```
β_G ∘ α'_A = α'_B ∘ β_F
```

Therefore both sides equal, proving the interchange law.

**System Interpretation**: The order in which you apply transformations (parallel vs sequential) doesn't matter—the result is the same.

## Natural Transformation Category

Natural transformations between functors F, G: C → D form a category:

- **Objects**: Functors F, G, H, ...
- **Morphisms**: Natural transformations α: F ⇒ G
- **Composition**: Vertical composition (β ⋅ α)
- **Identity**: Identity natural transformation id_F: F ⇒ F

**Laws**:
1. **Associativity**: (γ ⋅ β) ⋅ α = γ ⋅ (β ⋅ α)
2. **Identity**: id_G ⋅ α = α = α ⋅ id_F

This forms the **functor category** [C, D].

## Practical Implications

### 1. Transformation Pipelines

Build complex transformations compositionally:

```python
# Pipeline: sync → logged → validated → async
pipeline = vertical_compose(
    vertical_compose(
        vertical_compose(
            identity_to_writer,
            writer_to_validated
        ),
        validated_to_future
    )
)
```

Or more readably:
```python
pipeline = compose_all([
    identity_to_writer,
    writer_to_validated,
    validated_to_future
])
```

### 2. Nested Functor Transformations

Transform nested functor stacks:

```python
# Maybe[Either[Error, User]] → List[Either[Error, User]]
maybe_either_to_list_either = horizontal_compose(
    identity_either,  # Either ⇒ Either (no-op)
    maybe_to_list,    # Maybe ⇒ List
    fmap_list         # fmap for List
)
```

### 3. Modular Architecture Evolution

Evolve architecture in independent dimensions:

```python
# Dimension 1: Error handling (Either → Maybe)
# Dimension 2: Concurrency (Identity → Future)

# Can apply in either order due to interchange law
approach1 = vertical_compose(
    horizontal_compose(either_to_maybe, identity_future),
    horizontal_compose(identity_maybe, identity_to_future)
)

approach2 = horizontal_compose(
    vertical_compose(either_to_maybe, identity_maybe),
    vertical_compose(identity_future, identity_to_future)
)

# approach1 == approach2 by interchange law
```

## Summary

- **Vertical composition** (β ⋅ α): Sequential transformations F → G → H
- **Horizontal composition** (β ∘ α): Parallel transformations at different levels
- **Interchange law**: Guarantees composition order doesn't matter
- Natural transformations form a **functor category** [C, D]

Use composition to build complex architectural transformations from simple, verified components.
