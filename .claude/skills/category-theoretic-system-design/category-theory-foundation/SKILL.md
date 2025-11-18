---
name: category-theory-foundation
description: Apply category theory principles to system design. Use when analyzing system architecture, verifying composition, checking mathematical properties, or proving system correctness. Includes composition laws, universal constructions, functors, and natural transformations.
---

# Category Theory Foundation

You are an expert in category theory, type theory, and formal methods. Your role is to help users apply rigorous mathematical principles to system architecture and software design.

## Purpose

Provide mathematical rigor for system architecture through category theory. Every system component is viewed as a morphism in a category, with composition, identity, and structure preservation guaranteed by categorical laws.

## Core Concepts

### Composition

The fundamental operation in category theory. Services compose like functions:

```
If f: A → B and g: B → C
Then g ∘ f: A → C
```

**Requirements:**
- Type alignment: Output of f must match input of g
- Associativity: (h ∘ g) ∘ f = h ∘ (g ∘ f)
- Identity: id ∘ f = f = f ∘ id

### Objects and Morphisms

- **Objects:** Types, data structures, service interfaces
- **Morphisms:** Functions, services, transformations
- **Categories:** Complete systems with composition

### Universal Constructions

Define objects by their relationships, not implementation:

**Products:** Combine multiple inputs
- Example: Service needs both Auth AND Catalog
- Property: Unique morphism from any candidate

**Coproducts:** Alternative choices
- Example: Payment via Stripe OR PayPal
- Property: Unique morphism to any candidate

**Exponentials:** Functions as objects
- Example: Config → Service (dependency injection)
- Property: Curry/uncurry isomorphism

## When to Use

### 1. Analyzing Service Composition

- Verify services can compose
- Check type alignment
- Validate associativity

**Example:**
```python
# Check if services compose
api_gateway: Request → ServiceCall
auth_service: ServiceCall → AuthResult

# Can they compose?
if api_gateway.output_type == auth_service.input_type:
    composed = compose(auth_service, api_gateway)
    # Result: Request → AuthResult
```

### 2. Proving System Correctness

- Show composition is well-defined
- Prove identity exists
- Verify structure preservation

**Example:**
```python
# Prove identity law
id_service = lambda x: x

assert compose(service, id_service) == service  # Right identity
assert compose(id_service, service) == service  # Left identity
```

### 3. Detecting Structural Issues

- Find broken compositions
- Identify missing identities
- Locate type mismatches

**Example:**
```python
# Find type mismatches
for f in services:
    for g in services:
        if f.output_type != g.input_type and user_wants_to_compose(f, g):
            warn(f"Cannot compose {f.name} with {g.name}: type mismatch")
```

### 4. Optimizing Architecture

- Apply categorical laws
- Simplify compositions
- Enable parallel execution

**Example:**
```python
# Use associativity to enable parallelism
# (h ∘ g) ∘ f = h ∘ (g ∘ f)
# Can compute g ∘ f in parallel with other operations
```

## Key Principles

### 1. Composition is Primary

Every system is built from composing smaller pieces. If composition breaks, the system breaks.

**Guideline:** Design for composition first, implementation second.

### 2. Types Define Possibilities

Type signatures determine what compositions are valid. Start with types, not implementations.

**Guideline:** Write type signatures before writing code. Let types guide design.

### 3. Laws Guarantee Correctness

Categorical laws aren't suggestions—they're requirements for mathematical correctness.

**Guideline:** Always validate category laws. Use property-based testing.

### 4. Structure Preservation

Transformations must preserve the categorical structure. Use functors and natural transformations.

**Guideline:** When transforming systems, verify functor laws and naturality conditions.

## Quick Reference

### Check Composition

```python
# Verify f: A → B composes with g: B → C
if output_type(f) == input_type(g):
    composed = compose(g, f)  # g ∘ f
    assert_associative(composed)
```

### Find Identity

```python
# Every type needs an identity morphism
def identity(x: A) -> A:
    return x

# Verify: id ∘ f = f = f ∘ id
assert compose(f, identity) == f
assert compose(identity, f) == f
```

### Validate Functor

```python
# Functor F must preserve structure
assert F(id) == id  # Identity preservation
assert F(g ∘ f) == F(g) ∘ F(f)  # Composition preservation
```

### Check Natural Transformation

```python
# Natural transformation α: F → G must satisfy naturality
# G(f) ∘ α_a = α_b ∘ F(f)
def verify_naturality(alpha, F, G, f, test_input):
    path1 = compose(G.fmap(f), alpha)(test_input)
    path2 = compose(alpha, F.fmap(f))(test_input)
    assert path1 == path2
```

## Detailed Resources

### Reference Documentation

- **[reference/laws.md](reference/laws.md)** - Complete categorical laws
  - Category laws (identity, associativity, composition)
  - Functor laws (identity preservation, composition preservation)
  - Natural transformation laws (naturality condition)
  - Universal properties (products, coproducts, exponentials)
  - Semiring laws for ADTs

- **[reference/proofs.md](reference/proofs.md)** - Proof techniques and examples
  - Equational reasoning
  - Pattern matching proofs
  - Diagram chasing
  - Universal property proofs
  - Parametricity arguments
  - Induction proofs

- **[examples/composition.md](examples/composition.md)** - Composition patterns
  - Service pipelines
  - Multi-argument services
  - Optional services
  - Error handling with Either
  - Async composition

## Common Patterns

### Pattern 1: Service Pipeline

```
Services: A → B → C → D
Verify: Associative composition
Result: Can regroup without changing behavior

Example:
  request_parser: Request → ParsedRequest
  validator: ParsedRequest → ValidRequest
  handler: ValidRequest → Response

  # All groupings equivalent:
  ((handler ∘ validator) ∘ parser) = (handler ∘ (validator ∘ parser))
```

### Pattern 2: Multi-Argument Service

```
Input: (Config, Request) → Response
Transform: Config → (Request → Response)
Result: Currying enables partial application

Example:
  def create_handler(config):
      def handler(request):
          return process(config, request)
      return handler

  # Pre-configure handlers
  prod_handler = create_handler(prod_config)
  dev_handler = create_handler(dev_config)
```

### Pattern 3: Optional Service

```
Type: Maybe Service
Functor: fmap :: (a → b) → Maybe a → Maybe b
Result: Transform whether service exists or not

Example:
  cache_service: Maybe (Key → Value)

  # Apply transformation even if cache doesn't exist
  enhanced_cache = fmap(add_ttl, cache_service)
  # If cache exists: adds TTL
  # If cache doesn't exist: remains Nothing
```

### Pattern 4: Error Handling with Either

```
Type: Either Error Success
Functor: fmap :: (a → b) → Either e a → Either e b
Result: Transform success case, preserve errors

Example:
  auth_result: Either AuthError User

  # Extract user permissions without handling error case
  permissions = fmap(get_permissions, auth_result)
  # Success: User → Permissions
  # Error: AuthError preserved
```

### Pattern 5: Async Composition

```
Type: Future a (Promise/Async)
Functor: fmap :: (a → b) → Future a → Future b
Result: Compose async operations

Example:
  fetch_user: Future User
  fetch_posts: User → Future (List Post)

  # Flat composition
  all_posts = fetch_user >>= fetch_posts
  # Automatically handles async waiting
```

## Integration with Other Skills

### With graph-parser
Parse system specifications into categorical structures:
```python
from graph_parser import parse_specification

graph = parse_specification("microservices.yaml")
# Graph becomes foundation for category construction
```

### With free-category-constructor
Build complete categories with verified laws:
```python
from free_category import construct_free_category

category = construct_free_category(graph)
# All category laws automatically satisfied
```

### With standardization-layer
Apply transformations as functors:
```python
from standardization_layer import apply_standardization

# Standardization is a functor F: Category → Category
standardized = apply_standardization(category, spec)
# Preserves composition and identity
```

## Error Prevention

### ❌ Don't:

1. **Compose services with mismatched types**
   ```python
   # BAD
   f: Request → JSON
   g: XML → Response
   compose(g, f)  # Type error! JSON ≠ XML
   ```

2. **Forget identity morphisms**
   ```python
   # BAD
   # No way to "do nothing" with a Request
   # Missing: id: Request → Request
   ```

3. **Ignore associativity**
   ```python
   # BAD
   # Assuming (f ∘ g) ∘ h is different from f ∘ (g ∘ h)
   # This breaks compositional reasoning
   ```

4. **Break structure when transforming**
   ```python
   # BAD
   def bad_functor(f):
       # Doesn't preserve composition
       # F(g ∘ f) ≠ F(g) ∘ F(f)
       pass
   ```

### ✓ Do:

1. **Verify types before composing**
   ```python
   # GOOD
   if f.output_type == g.input_type:
       composed = compose(g, f)
   else:
       raise TypeError(f"Cannot compose: {f.output_type} ≠ {g.input_type}")
   ```

2. **Provide identity for every service**
   ```python
   # GOOD
   def identity_request(req: Request) -> Request:
       return req

   def identity_response(resp: Response) -> Response:
       return resp
   ```

3. **Test associativity**
   ```python
   # GOOD
   from hypothesis import given

   @given(test_input)
   def test_associativity(x):
       left = compose(compose(h, g), f)(x)
       right = compose(h, compose(g, f))(x)
       assert left == right
   ```

4. **Preserve structure in transformations**
   ```python
   # GOOD
   class ProperFunctor:
       def fmap(self, f):
           # Verify laws
           assert self.fmap(identity) == identity
           assert self.fmap(compose(g, f)) == compose(self.fmap(g), self.fmap(f))
           # Then implement
           ...
   ```

## Practical Validation

### Quick Law Check

```python
def validate_category(category):
    """Verify all category laws"""

    # 1. Check composition is defined
    for f in category.morphisms:
        for g in category.morphisms:
            if f.target == g.source:
                assert category.has_composition(f, g)

    # 2. Check associativity (sample)
    for f, g, h in sample_composable_triples(category):
        left = compose(compose(h, g), f)
        right = compose(h, compose(g, f))
        assert left == right

    # 3. Check identities exist
    for obj in category.objects:
        assert category.has_identity(obj)

    # 4. Check identity law
    for f in category.morphisms:
        id_source = category.identity(f.source)
        id_target = category.identity(f.target)
        assert compose(f, id_source) == f
        assert compose(id_target, f) == f

    return True
```

### Functor Validation

```python
def validate_functor(F, category_C, category_D):
    """Verify functor laws"""

    # 1. Check identity preservation
    for obj in category_C.objects:
        id_c = category_C.identity(obj)
        F_id = F.apply(id_c)
        id_Fc = category_D.identity(F.map_object(obj))
        assert F_id == id_Fc

    # 2. Check composition preservation (sample)
    for f, g in sample_composable_pairs(category_C):
        F_gf = F.apply(compose(g, f))
        Fg_Ff = compose(F.apply(g), F.apply(f))
        assert F_gf == Fg_Ff

    return True
```

## Learning Path

For users new to category theory:

1. **Start with composition** - Understand how functions/services compose
2. **Learn identity** - Recognize the importance of "do nothing" operations
3. **Study associativity** - See why grouping doesn't matter
4. **Explore functors** - Understand structure-preserving transformations
5. **Master natural transformations** - Learn safe system migrations

For experienced users:

1. **Apply universal properties** - Use products, coproducts, exponentials
2. **Construct adjunctions** - Find left and right adjoints
3. **Build monads** - Understand computation patterns
4. **Study 2-categories** - Work with transformations of transformations

## Summary

Category theory provides a mathematical foundation for system architecture that guarantees correctness through:

- **Composition** - Building complex systems from simple parts
- **Identity** - Having neutral elements for all types
- **Associativity** - Enabling flexible regrouping
- **Functors** - Preserving structure across transformations
- **Natural Transformations** - Enabling safe migrations

Use this skill whenever you need mathematical certainty about system behavior, composition safety, or structural correctness.

Remember: Category theory isn't just abstract mathematics—it's a practical tool for building correct, composable, maintainable systems.
