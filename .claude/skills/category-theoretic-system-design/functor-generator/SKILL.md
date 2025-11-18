---
name: functor-generator
description: Generate structure-preserving transformations between system architectures. Use for multi-tenant, versioning, environment transformation, or any situation requiring systematic transformation while preserving composition and identity.
---

# Functor Generator

You are an expert in category theory, functors, and structure-preserving transformations. Your role is to help users generate functors that transform system architectures while maintaining mathematical correctness through functor laws.

## Purpose

Generate structure-preserving transformations (functors) between system architectures. Every transformation must preserve:
1. **Identity**: F(id) = id
2. **Composition**: F(g ∘ f) = F(g) ∘ F(f)

These laws guarantee that transformations don't break system structure.

## Available Resources

- `scripts/functor_generator.py` - Functor generators for all common types
- `scripts/validate_functor.py` - Automated functor law validation
- `examples/multi-tenant-reader.md` - Complete multi-tenant example

## Core Concept

A **functor** F: C → D is a structure-preserving transformation that:
- Maps objects: For each object A in C, produces F(A) in D
- Maps morphisms: For each f: A → B in C, produces F(f): F(A) → F(B) in D
- Preserves identity: F(id_A) = id_F(A)
- Preserves composition: F(g ∘ f) = F(g) ∘ F(f)

## Common Functor Types

### 1. Reader Functor (Config → Service)

**Use Case**: Multi-tenant systems, environment-specific configuration

**Type Signature**:
```
Reader r a = r → a
```

**Transformation**:
```
Service → (Config → Service)
```

**Example**:
```python
# Original service
def process_payment(amount: Money) -> Result:
    # Uses hardcoded API key
    return stripe.charge(amount, api_key="hardcoded")

# Reader functor transformation
def process_payment_reader(config: Config):
    def process(amount: Money) -> Result:
        # Uses config
        return stripe.charge(amount, api_key=config.stripe_key)
    return process

# Usage
prod_payment = process_payment_reader(prod_config)
dev_payment = process_payment_reader(dev_config)
```

**fmap Implementation**:
```python
def fmap(f):
    """(a → b) → Reader r a → Reader r b"""
    def transform(reader):
        def new_reader(config):
            return f(reader(config))
        return new_reader
    return transform
```

**Validation**:
```python
# Identity: fmap id = id
assert fmap(identity)(reader) == identity(reader)

# Composition: fmap (g ∘ f) = fmap g ∘ fmap f
assert fmap(compose(g, f))(reader) == compose(fmap(g), fmap(f))(reader)
```

### 2. Maybe Functor (Optional Service)

**Use Case**: Feature flags, graceful degradation, optional components

**Type Signature**:
```
Maybe a = Nothing | Just a
```

**Transformation**:
```
Service → Maybe Service
```

**Example**:
```python
# Original service
def get_recommendations(user: User) -> List[Product]:
    # Always attempts to get recommendations
    return ai_service.recommend(user)

# Maybe functor transformation
def get_recommendations_maybe(user: User) -> Maybe[List[Product]]:
    if feature_flags.ai_enabled:
        try:
            return Just(ai_service.recommend(user))
        except:
            return Nothing
    else:
        return Nothing

# Handle None case
result = get_recommendations_maybe(user)
match result:
    case Just(products):
        display(products)
    case Nothing:
        display(fallback_recommendations)
```

**fmap Implementation**:
```python
def fmap(f):
    """(a → b) → Maybe a → Maybe b"""
    def transform(maybe):
        match maybe:
            case Nothing:
                return Nothing
            case Just(value):
                return Just(f(value))
    return transform
```

### 3. List Functor (Replicated Service)

**Use Case**: Load balancing, redundancy, parallel processing

**Type Signature**:
```
List a = [] | [a, a, ...]
```

**Transformation**:
```
Service → List Service
```

**Example**:
```python
# Original service
def query_database(sql: str) -> Result:
    return primary_db.query(sql)

# List functor transformation
def query_databases(sql: str) -> List[Result]:
    replicas = [primary_db, replica1_db, replica2_db]
    return [db.query(sql) for db in replicas]

# Use with redundancy
results = query_databases("SELECT ...")
# Pick first successful result
for result in results:
    if result.is_success:
        return result
```

**fmap Implementation**:
```python
def fmap(f):
    """(a → b) → List a → List b"""
    def transform(list_a):
        return [f(x) for x in list_a]
    return transform
```

### 4. Either Functor (Error Handling)

**Use Case**: Explicit error handling, result types

**Type Signature**:
```
Either e a = Left e | Right a
```

**Transformation**:
```
Service → Either Error Service
```

**Example**:
```python
# Original service (throws exceptions)
def authenticate(token: str) -> User:
    if not validate_token(token):
        raise AuthError("Invalid token")
    return get_user(token)

# Either functor transformation
def authenticate_either(token: str) -> Either[AuthError, User]:
    if not validate_token(token):
        return Left(AuthError("Invalid token"))
    try:
        return Right(get_user(token))
    except Exception as e:
        return Left(AuthError(str(e)))

# Usage
result = authenticate_either(token)
match result:
    case Left(error):
        log_error(error)
        return unauthorized_response
    case Right(user):
        return process_request(user)
```

**fmap Implementation**:
```python
def fmap(f):
    """(a → b) → Either e a → Either e b"""
    def transform(either):
        match either:
            case Left(error):
                return Left(error)
            case Right(value):
                return Right(f(value))
    return transform
```

### 5. State Functor (Stateful Service)

**Use Case**: Session management, transaction state, workflow state

**Type Signature**:
```
State s a = s → (a, s)
```

**Transformation**:
```
Service → (State → (Service, State))
```

**Example**:
```python
# Original service
def process_order(order: Order) -> Receipt:
    # Modifies global state
    return create_receipt(order)

# State functor transformation
def process_order_state(order: Order):
    def run(state: AppState):
        receipt = create_receipt(order)
        new_state = state.with_order(order)
        return (receipt, new_state)
    return run

# Usage
initial_state = AppState()
(receipt, final_state) = process_order_state(order)(initial_state)
```

**fmap Implementation**:
```python
def fmap(f):
    """(a → b) → State s a → State s b"""
    def transform(state_a):
        def new_state(s):
            (a, s_new) = state_a(s)
            return (f(a), s_new)
        return new_state
    return transform
```

### 6. Future/Promise Functor (Async Service)

**Use Case**: Asynchronous operations, non-blocking I/O

**Type Signature**:
```
Future a = Async computation yielding a
```

**Transformation**:
```
Service → Future Service
```

**Example**:
```python
# Original service (blocking)
def fetch_user(user_id: str) -> User:
    return database.get(user_id)

# Future functor transformation
async def fetch_user_async(user_id: str) -> User:
    return await database.get_async(user_id)

# fmap for Future
def fmap(f):
    """(a → b) → Future a → Future b"""
    async def transform(future_a):
        a = await future_a
        return f(a)
    return transform

# Usage
user_future = fetch_user_async("123")
email_future = fmap(lambda u: u.email)(user_future)
```

## Functor Generation Process

### Step 1: Identify Transformation Need

Determine what kind of transformation you need:
- **Multi-tenant?** → Reader functor
- **Optional?** → Maybe functor
- **Replicated?** → List functor
- **Error handling?** → Either functor
- **Stateful?** → State functor
- **Async?** → Future functor

### Step 2: Define Type Constructor

Define how your functor wraps values:

```python
class MyFunctor:
    def __init__(self, value):
        self.value = value

    def pure(value):
        """Lift a value into the functor"""
        return MyFunctor(value)
```

### Step 3: Implement fmap

Define how to apply functions to wrapped values:

```python
def fmap(self, f):
    """Apply function to wrapped value"""
    return MyFunctor(f(self.value))
```

### Step 4: Validate Functor Laws

Prove or test that functor laws hold:

```python
from validate_functor import validate_functor_laws

# Test identity law
assert validate_identity_law(MyFunctor)

# Test composition law
assert validate_composition_law(MyFunctor)
```

## Functor Law Validation

### Law 1: Identity Preservation

```
F(id) = id

For all x: fmap(identity)(F(x)) = identity(F(x)) = F(x)
```

**Test**:
```python
def test_identity_law(functor_class):
    def identity(x):
        return x

    test_values = [1, "hello", [1,2,3], {"key": "value"}]

    for value in test_values:
        # Wrap value
        fx = functor_class.pure(value)

        # Apply identity via fmap
        result1 = functor_class.fmap(identity)(fx)

        # Direct identity
        result2 = identity(fx)

        assert result1 == result2, f"Identity law failed for {value}"

    return True
```

### Law 2: Composition Preservation

```
F(g ∘ f) = F(g) ∘ F(f)

For all f, g: fmap(g ∘ f) = fmap(g) ∘ fmap(f)
```

**Test**:
```python
def test_composition_law(functor_class):
    def f(x):
        return x + 1

    def g(x):
        return x * 2

    def compose(g, f):
        return lambda x: g(f(x))

    test_values = [1, 5, 10, 100]

    for value in test_values:
        fx = functor_class.pure(value)

        # Path 1: fmap(g ∘ f)
        composed = compose(g, f)
        result1 = functor_class.fmap(composed)(fx)

        # Path 2: fmap(g) ∘ fmap(f)
        result2 = functor_class.fmap(g)(functor_class.fmap(f)(fx))

        assert result1 == result2, f"Composition law failed for {value}"

    return True
```

## Functor Composition

Functors themselves compose:

```python
# Compose Maybe and List functors
MaybeList = compose_functors(Maybe, List)

# Example
result: Maybe[List[User]] = MaybeList.pure([user1, user2])

# fmap applies through both layers
emails: Maybe[List[str]] = MaybeList.fmap(lambda u: u.email)(result)
```

## Natural Transformations

Transform between functors while preserving structure:

```python
# Natural transformation: Maybe → List
def maybe_to_list(maybe_a):
    """α: Maybe a → List a"""
    match maybe_a:
        case Nothing:
            return []
        case Just(x):
            return [x]

# Naturality condition must hold:
# list.fmap(f) ∘ maybe_to_list = maybe_to_list ∘ maybe.fmap(f)
```

## Code Generation

The functor generator can produce:

### 1. Functor Class

```python
def generate_functor_class(name, type_constructor):
    """Generate complete functor class"""
    code = f'''
class {name}Functor:
    def __init__(self, value):
        self.value = {type_constructor}(value)

    @staticmethod
    def pure(value):
        return {name}Functor(value)

    def fmap(self, f):
        # Type-specific fmap implementation
        ...
    '''
    return code
```

### 2. Validation Tests

```python
def generate_tests(functor_name):
    """Generate functor law tests"""
    code = f'''
def test_{functor_name}_identity():
    assert validate_identity_law({functor_name}Functor)

def test_{functor_name}_composition():
    assert validate_composition_law({functor_name}Functor)
    '''
    return code
```

### 3. Usage Examples

```python
def generate_usage_example(functor_name, use_case):
    """Generate usage documentation"""
    ...
```

## Integration with Other Skills

### With free-category-constructor

Functors map between categories:

```python
# Source category
source_cat = construct_free_category(source_graph)

# Target category
target_cat = construct_free_category(target_graph)

# Functor between them
F = generate_functor(source_cat, target_cat, mapping)

# Verify functor laws
validate_functor(F, source_cat, target_cat)
```

### With standardization-layer

Standardization is a functor:

```python
# Standardization functor
F_std = StandardizationFunctor(spec)

# Verify it preserves structure
assert F_std.fmap(id) == id
assert F_std.fmap(compose(g, f)) == compose(F_std.fmap(g), F_std.fmap(f))
```

### With adt-analyzer

Each ADT path gets a functor:

```python
# ADT expansion produces paths
paths = expand_adt(Service)

# Generate functor for each path
functors = [generate_functor(path) for path in paths]

# Verify all functors
for f in functors:
    validate_functor_laws(f)
```

## When to Use

✓ **Use functor generator when:**
- Transforming system architecture systematically
- Need multi-tenant or multi-environment support
- Implementing optional features (Maybe)
- Adding error handling (Either)
- Making services asynchronous (Future)
- Need to preserve compositional structure

✗ **Don't use when:**
- Transformation doesn't need to preserve structure
- One-off custom transformation
- Performance is critical and overhead unacceptable

## Best Practices

### 1. Always Validate Laws

```python
# Generate functor
my_functor = generate_reader_functor(config_type)

# ALWAYS validate
assert validate_identity_law(my_functor)
assert validate_composition_law(my_functor)
```

### 2. Use Type Annotations

```python
from typing import TypeVar, Callable, Generic

A = TypeVar('A')
B = TypeVar('B')

class ReaderFunctor(Generic[A]):
    def fmap(self, f: Callable[[A], B]) -> 'ReaderFunctor[B]':
        ...
```

### 3. Provide Pure/Return

Every functor should have a way to lift values:

```python
class MyFunctor:
    @staticmethod
    def pure(value):
        """Lift a value into the functor"""
        return MyFunctor(value)
```

### 4. Document Use Cases

```python
class ReaderFunctor:
    """
    Reader functor for dependency injection.

    Use cases:
    - Multi-tenant configuration
    - Environment-specific settings
    - Dependency injection

    Example:
        prod = my_service(prod_config)
        dev = my_service(dev_config)
    """
    ...
```

## Common Patterns

### Pattern 1: Functor Stack

Stack multiple functors:

```python
# Maybe[List[Either[Error, User]]]
MaybeListEither = Maybe(List(Either))

# Single fmap applies through all layers
result = MaybeListEither.fmap(process_user)(data)
```

### Pattern 2: Bifunctor

Map over two type parameters:

```python
class Either:
    def bimap(self, f_left, f_right):
        """Map both error and success"""
        match self:
            case Left(e):
                return Left(f_left(e))
            case Right(x):
                return Right(f_right(x))
```

### Pattern 3: Contravariant Functor

Map in reverse direction:

```python
class Predicate:
    def contramap(self, f):
        """(b → a) → Predicate a → Predicate b"""
        return Predicate(lambda b: self.test(f(b)))
```

## Error Handling

### Invalid Functor

If functor laws don't hold, raise error:

```python
class InvalidFunctorError(Exception):
    def __init__(self, law, details):
        self.law = law
        self.details = details
        super().__init__(f"Functor law '{law}' violated: {details}")

if not validate_identity_law(F):
    raise InvalidFunctorError("Identity", "F(id) ≠ id")
```

## Summary

Functor generators create structure-preserving transformations that:
- Preserve composition and identity
- Enable systematic architecture transformation
- Provide mathematical guarantees
- Support common patterns (Reader, Maybe, List, Either, State, Future)

Use this skill whenever you need to transform system architecture while maintaining structural correctness.
