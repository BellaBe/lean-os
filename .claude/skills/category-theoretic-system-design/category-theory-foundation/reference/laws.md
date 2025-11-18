# Categorical Laws Reference

This document provides complete formal definitions of all categorical laws used in system design.

## Category Laws

A category C consists of:
- Objects: Ob(C)
- Morphisms: Hom(C)
- Composition: ∘
- Identity: id

### Law 1: Composition is a Binary Operation

For morphisms f: a → b and g: b → c, their composition g ∘ f: a → c exists.

**System interpretation:** If service f produces type B and service g accepts type B, they can compose.

**Validation:**
```python
def can_compose(f: Service[A, B], g: Service[B, C]) -> bool:
    return f.output_type == g.input_type
```

### Law 2: Associativity

For morphisms f: a → b, g: b → c, h: c → d:
```
(h ∘ g) ∘ f = h ∘ (g ∘ f)
```

**System interpretation:** Grouping of service composition doesn't matter.

**Validation:**
```python
def test_associativity(f, g, h, test_input):
    left = compose(compose(h, g), f)
    right = compose(h, compose(g, f))
    assert left(test_input) == right(test_input)
```

**Why it matters:** Allows refactoring service chains without changing behavior.

### Law 3: Identity

For every object a, there exists id_a: a → a such that:
```
f ∘ id_a = f
id_b ∘ f = f
```

**System interpretation:** Every service type needs a pass-through service.

**Implementation:**
```python
def identity(x: A) -> A:
    return x

# Verify
assert compose(f, identity) == f
assert compose(identity, f) == f
```

**Why it matters:** Identity is the unit of composition. Without it, composition algebra breaks.

## Functor Laws

A functor F: C → D consists of:
- Object mapping: F(a) for each object a
- Morphism mapping: F(f) for each morphism f

### Law 4: Identity Preservation

```
F(id_a) = id_F(a)
```

**System interpretation:** Transforming an identity service produces an identity service.

**Validation:**
```python
def test_functor_identity(F, test_type):
    original_id = identity
    transformed_id = F.fmap(original_id)

    # Both should be identity
    assert transformed_id(x) == x for all x
```

### Law 5: Composition Preservation

```
F(g ∘ f) = F(g) ∘ F(f)
```

**System interpretation:** Transforming a composed service equals composing transformed services.

**Validation:**
```python
def test_functor_composition(F, f, g, test_input):
    # Transform composition
    composed_then_transformed = F.fmap(compose(g, f))

    # Compose transformations
    transformed_then_composed = compose(
        F.fmap(g),
        F.fmap(f)
    )

    assert composed_then_transformed(test_input) == \
           transformed_then_composed(test_input)
```

**Why it matters:** Guarantees that system transformations preserve structure.

## Natural Transformation Laws

A natural transformation α: F → G between functors F, G: C → D consists of:
- Components: α_a: F(a) → G(a) for each object a

### Law 6: Naturality Condition

For every morphism f: a → b:
```
G(f) ∘ α_a = α_b ∘ F(f)
```

**Commutative diagram:**
```
F(a) ---F(f)---> F(b)
 |                |
α_a              α_b
 |                |
 v                v
G(a) ---G(f)---> G(b)
```

**System interpretation:** Order of transformation and operation doesn't matter.

**Validation:**
```python
def test_naturality(alpha, F, G, f, test_input):
    # Path 1: Transform then map
    path1 = G.fmap(f)(alpha(F(test_input)))

    # Path 2: Map then transform
    path2 = alpha(F.fmap(f)(F(test_input)))

    assert path1 == path2
```

**Why it matters:** Guarantees safe migration between system architectures.

## Product Laws

A product a × b with projections π₁: a × b → a, π₂: a × b → b satisfies:

### Law 7: Universal Property of Products

For any object c with morphisms f: c → a, g: c → b, there exists unique h: c → a × b such that:
```
π₁ ∘ h = f
π₂ ∘ h = g
```

**System interpretation:** Service with multiple outputs can be uniquely factored.

**Implementation:**
```python
def product_factorizer(f, g):
    """Generate unique morphism to product"""
    def h(x):
        return (f(x), g(x))
    return h

# Verify
assert compose(pi1, h) == f
assert compose(pi2, h) == g
```

## Coproduct Laws

A coproduct a + b with injections ι₁: a → a + b, ι₂: b → a + b satisfies:

### Law 8: Universal Property of Coproducts

For any object c with morphisms f: a → c, g: b → c, there exists unique h: a + b → c such that:
```
h ∘ ι₁ = f
h ∘ ι₂ = g
```

**System interpretation:** Service handling alternatives can be uniquely factored.

**Implementation:**
```python
def coproduct_factorizer(f, g):
    """Generate unique morphism from coproduct"""
    def h(either):
        match either:
            case Left(a): return f(a)
            case Right(b): return g(b)
    return h

# Verify
assert compose(h, iota1) == f
assert compose(h, iota2) == g
```

## Exponential Laws

An exponential b^a with evaluation eval: (b^a × a) → b satisfies:

### Law 9: Universal Property of Exponentials

For any object c with morphism g: c × a → b, there exists unique h: c → b^a such that:
```
eval ∘ (h × id) = g
```

**System interpretation:** Multi-argument service curries uniquely.

**Implementation:**
```python
def curry(g):
    """Generate unique morphism to exponential"""
    def h(c):
        def curried(a):
            return g(c, a)
        return curried
    return h

# Verify
def uncurry(h):
    def g(c, a):
        return h(c)(a)
    return g

assert uncurry(curry(g)) == g
```

## Monoidal Laws

### Law 10: Monoidal Product Associativity

```
(a × b) × c ≅ a × (b × c)
```

**Isomorphism:**
```python
def alpha(((x, y), z)):
    return (x, (y, z))

def alpha_inv((x, (y, z))):
    return ((x, y), z)
```

### Law 11: Monoidal Unit Laws

```
a × () ≅ a
() × a ≅ a
```

**Isomorphisms:**
```python
def rho((x, ())):
    return x

def rho_inv(x):
    return (x, ())

def lambda_(((, x)):
    return x

def lambda_inv(x):
    return ((), x)
```

## Cartesian Closed Category Requirements

A category is cartesian closed if it has:

### Law 12: Terminal Object

Object () with unique morphism from any object:
```
∀a. ∃! f: a → ()
```

### Law 13: Binary Products

For any objects a, b, product a × b exists with projections.

### Law 14: Exponentials

For any objects a, b, exponential b^a exists with evaluation.

**System check:**
```python
def is_cartesian_closed(category):
    has_terminal = check_terminal_object(category)
    has_products = check_all_products_exist(category)
    has_exponentials = check_all_exponentials_exist(category)
    return has_terminal and has_products and has_exponentials
```

## Semiring Laws (for ADTs)

Types form a semiring with:
- Addition: Coproduct (+)
- Multiplication: Product (×)
- Zero: Void (0)
- One: Unit (1)

### Law 15: Addition is Associative

```
(a + b) + c = a + (b + c)
```

### Law 16: Addition is Commutative

```
a + b = b + a
```

### Law 17: Multiplication is Associative

```
(a × b) × c = a × (b × c)
```

### Law 18: Multiplication is Commutative

```
a × b = b × a
```

### Law 19: Distributivity

```
a × (b + c) = a × b + a × c
(a + b) × c = a × c + b × c
```

**System application:**
```python
# Expand choices
Service × (PlatformA + PlatformB)
= (Service × PlatformA) + (Service × PlatformB)
# Result: Two specialized services
```

### Law 20: Zero Annihilates

```
a × 0 = 0
0 × a = 0
```

**System application:**
```python
# Impossible service
Service × Void = Void
# If any dependency is impossible, service is impossible
```

### Law 21: One is Identity

```
a × 1 = a
1 × a = a
```

## Interchange Law (2-Categories)

For natural transformations:

### Law 22: Vertical and Horizontal Composition

```
(β' ⋅ α') ∘ (β ⋅ α) = (β' ∘ β) ⋅ (α' ∘ α)
```

**System interpretation:** Order of composing transformations commutes.

## Summary Table

| Law | Category | Formula | System Meaning |
|-----|----------|---------|----------------|
| Associativity | Category | (h∘g)∘f = h∘(g∘f) | Service grouping flexible |
| Identity | Category | id∘f = f = f∘id | Pass-through exists |
| Functor Identity | Functor | F(id) = id | Transform preserves identity |
| Functor Composition | Functor | F(g∘f) = F(g)∘F(f) | Transform preserves composition |
| Naturality | Nat. Trans. | G(f)∘α = α∘F(f) | Migration order independent |
| Product Universal | Product | ∃! h: π₁∘h=f, π₂∘h=g | Unique factorization |
| Coproduct Universal | Coproduct | ∃! h: h∘ι₁=f, h∘ι₂=g | Unique case analysis |
| Exponential Universal | Exponential | ∃! h: eval∘(h×id)=g | Unique currying |
| Distributivity | Semiring | a×(b+c) = a×b+a×c | Choice expansion |

## Validation Checklist

Use this checklist to verify categorical correctness:

- [ ] All compositions type-check
- [ ] Associativity holds for all service chains
- [ ] Identity exists for every service type
- [ ] Functors preserve identity
- [ ] Functors preserve composition
- [ ] Natural transformations satisfy naturality
- [ ] Products have unique factorization
- [ ] Coproducts have unique case analysis
- [ ] Exponentials curry/uncurry correctly
- [ ] Distributive law applies correctly
- [ ] Terminal object exists
- [ ] All products exist
- [ ] All exponentials exist (cartesian closed)
