---
name: curry-howard-prover
description: Prove system requirements by generating typed implementations. Use when verifying correctness, validating requirements, or ensuring impossible states are unrepresentable. Implementation = Proof.
---

# Curry-Howard Prover

You are an expert in the Curry-Howard correspondence and type-theoretic proofs. Your role is to help users prove system correctness by translating requirements into types.

## Purpose

Prove system requirements through type checking. If code compiles, the requirement is proven. Impossible states become unrepresentable types.

## Available Resources

- `scripts/curry_howard_prover.py` - Implementation of common proofs and phantom types
- `examples/modus-ponens.md` - Basic logical inference examples
- `examples/ex-falso.md` - Handling impossible states

## Core Concept

**Curry-Howard Correspondence**: Propositions are types, proofs are programs.

| Logic | Type Theory | Python |
|-------|-------------|--------|
| A ⇒ B | A → B | Callable[[A], B] |
| A ∧ B | A × B | Tuple[A, B] |
| A ∨ B | A + B | Union[A, B] |
| True | Unit (1) | None |
| False | Void (0) | Never |
| Proof of A | Term of type A | value: A |

## Process

### 1. Parse Requirement as Logical Statement

```
"If user has valid credentials and service is available,
 then user can access protected resource"
```

Translate to logic:
```
(HasCredentials ∧ ServiceAvailable) ⇒ CanAccessResource
```

### 2. Convert to Type Signature

```python
def prove_access(
    credentials: Credentials,
    service: Service
) -> ProtectedResource:
    """Type signature = Theorem statement"""
    ...
```

### 3. Implement = Prove

```python
def prove_access(
    credentials: Credentials,
    service: Service
) -> ProtectedResource:
    """Implementation = Constructive proof"""
    authenticated = service.authenticate(credentials)
    return service.get_resource(authenticated)
```

If this type-checks, the theorem is proven. ∎

## Common Logical Rules

### Modus Ponens: ((A ⇒ B) ∧ A) ⇒ B

```python
def modus_ponens(
    implication: Callable[[A], B],
    premise: A
) -> B:
    """If A implies B, and we have A, then we have B"""
    return implication(premise)
```

See [examples/modus-ponens.md](examples/modus-ponens.md)

### Ex Falso Quodlibet: False ⇒ A

```python
def absurd(impossible: Never) -> Any:
    """From impossibility, anything follows (but never executes)"""
    # Never has no values, so this line is unreachable
    raise RuntimeError("Unreachable")
```

See [examples/ex-falso.md](examples/ex-falso.md)

### Conjunction Introduction: A ⇒ B ⇒ (A ∧ B)

```python
def pair(a: A, b: B) -> Tuple[A, B]:
    """Prove A and B by providing both"""
    return (a, b)
```

### Conjunction Elimination: (A ∧ B) ⇒ A

```python
def fst(pair: Tuple[A, B]) -> A:
    """From A and B, extract A"""
    return pair[0]
```

### Disjunction Introduction: A ⇒ (A ∨ B)

```python
def left(a: A) -> Union[A, B]:
    """Prove A or B by providing A"""
    return a
```

### Case Analysis: (A ∨ B) ⇒ ((A ⇒ C) ⇒ (B ⇒ C) ⇒ C)

```python
def case_analysis(
    either: Union[A, B],
    handle_a: Callable[[A], C],
    handle_b: Callable[[B], C]
) -> C:
    """From A or B, prove C by handling both cases"""
    match either:
        case a if isinstance(a, type(handle_a.__annotations__['return'])):
            return handle_a(a)
        case b:
            return handle_b(b)
```

## Impossible States

Make impossible states unrepresentable:

```python
from typing import Never

class EmptyList:
    """Empty list has no head"""
    def head(self) -> Never:
        """Cannot get head of empty list - proven by types"""
        raise ValueError("Empty list has no head")

class NonEmptyList:
    """Non-empty list always has head"""
    def __init__(self, head: A, tail: List[A]):
        self._head = head
        self._tail = tail

    def head(self) -> A:
        """Proven to always succeed"""
        return self._head
```

Type system prevents calling `head()` on empty list at compile time.

## System Requirements as Theorems

### Requirement: "Multi-tenant service isolation"

**Theorem**: Tenant A cannot access Tenant B's data

```python
class TenantData(Generic[T]):
    """Data tagged with tenant type"""
    _data: Any
    _tenant: Type[T]

    def access(self, credentials: T) -> Any:
        """Can only access with matching tenant credentials"""
        # Type system enforces tenant matches
        return self._data

# Proof by types:
tenant_a_data: TenantData[TenantA] = ...
tenant_b_creds: TenantB = ...

# This won't compile - type mismatch proves isolation
# tenant_a_data.access(tenant_b_creds)  # Type error!
```

### Requirement: "Payment requires authentication"

**Theorem**: Cannot process payment without authentication

```python
class Authenticated:
    """Phantom type proving authentication"""
    pass

class Unauthenticated:
    """Phantom type proving no authentication"""
    pass

class Session(Generic[S]):
    _session_id: str
    _state: Type[S]

    def authenticate(self, credentials: Credentials) -> 'Session[Authenticated]':
        """Transition to authenticated session"""
        if verify(credentials):
            return Session[Authenticated]()
        raise AuthError()

    def process_payment(
        self: 'Session[Authenticated]',  # Requires authenticated
        amount: Money
    ) -> Receipt:
        """Can only be called on authenticated session"""
        return charge(amount)

# Proof by types:
session: Session[Unauthenticated] = Session()

# This won't compile - must authenticate first
# session.process_payment(100)  # Type error!

auth_session = session.authenticate(creds)
auth_session.process_payment(100)  # OK - proven authenticated
```

## Dependent Types (Limited in Python)

Encode value dependencies in types:

```python
class Vec(Generic[N, A]):
    """Vector of length N containing type A"""
    def __init__(self, length: N, elements: List[A]):
        assert len(elements) == length
        self._elements = elements

    def head(self) -> A:
        """Safe because N > 0 (if using proper dependent types)"""
        return self._elements[0]

# With proper dependent types:
# empty_vec: Vec[0, int] = Vec(0, [])
# empty_vec.head()  # Type error - length 0 has no head
```

## Integration

### With functor-generator

Functors preserve proofs:

```python
# Theorem: If A implies B, then F(A) implies F(B)
def fmap_preserves_proof(
    proof: Callable[[A], B],
    fa: F[A]
) -> F[B]:
    """Functor preserves implications"""
    return fa.fmap(proof)
```

### With natural-transformation-engine

Natural transformations are proof transformations:

```python
# Theorem: α: F ⇒ G transforms proofs in F to proofs in G
def transform_proof(alpha: NaturalTransformation, proof_in_f: F[A]) -> G[A]:
    """Transform proof from one context to another"""
    return alpha(proof_in_f)
```

### With category-theory-foundation

Category laws are provable theorems (see reference/category-laws-as-types.md).

## Validation

Type checker validates proofs automatically:

```python
from scripts.curry_howard_prover import validate_proof

# Define theorem as type
theorem: Type = Callable[[Credentials, Service], Resource]

# Define proof as implementation
def proof(creds: Credentials, svc: Service) -> Resource:
    return svc.access(creds)

# Validate proof matches theorem
assert validate_proof(theorem, proof)  # Type-checks = proven
```

## When to Use

✓ **Use Curry-Howard prover when:**
- Verifying system requirements formally
- Ensuring impossible states are unrepresentable
- Proving security properties (isolation, authentication)
- Validating business logic correctness
- Need compile-time guarantees

✗ **Don't use when:**
- Runtime properties need verification (use property testing)
- Performance-critical code (type complexity overhead)
- Proofs require full dependent types (Python limited)

## Best Practices

### 1. Make Illegal States Unrepresentable

```python
# BAD: Can create invalid state
class Order:
    items: List[Item]  # Could be empty!

# GOOD: Types prevent invalid states
class EmptyCart: pass
class NonEmptyCart:
    items: NonEmpty[List[Item]]  # Proven non-empty
```

### 2. Use Phantom Types for Proofs

```python
class Validated: pass
class Unvalidated: pass

class Input(Generic[S]):
    def validate(self: 'Input[Unvalidated]') -> 'Input[Validated]':
        ...

    def process(self: 'Input[Validated]') -> Result:
        """Only accepts validated input - proven by types"""
        ...
```

### 3. Encode Preconditions in Types

```python
def divide(a: float, b: NonZero[float]) -> float:
    """Type proves b ≠ 0, so division is safe"""
    return a / b
```

## Summary

Curry-Howard correspondence enables proving system correctness through types. Requirements become theorems, implementations become proofs. If code compiles, requirements are mathematically verified.

For examples, see:
- [examples/modus-ponens.md](examples/modus-ponens.md) - Basic logical inference
- [examples/ex-falso.md](examples/ex-falso.md) - Impossible states
