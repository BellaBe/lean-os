# Modus Ponens - Implementation as Proof

## Logical Statement
((A ⇒ B) ∧ A) ⇒ B

In words: "If A implies B, and A is true, then B must be true."

## Translation to Types
```python
def modus_ponens(
    implication: Callable[[A], B],
    premise: A
) -> B:
    """
    Type signature proves the theorem
    Implementation provides constructive proof
    """
    return implication(premise)
```

## Curry-Howard Correspondence

| Logic | Types | Python |
|-------|-------|--------|
| A ⇒ B | A → B | Callable[[A], B] |
| A ∧ B | A × B | Tuple[A, B] |
| Modus Ponens | ((A → B), A) → B | def modus_ponens(...) |

## System Application

**Theorem:** "If we have a service from A to B, and we have an A, then we can produce a B"
```python
def apply_service(
    service: Service[A, B],
    input_value: A
) -> B:
    """
    Modus ponens for services

    If service transforms A → B, and we have A,
    then we can produce B
    """
    return service.run(input_value)
```

**Proof:** The implementation type-checks, therefore the theorem holds. ∎

## Verification
```python
# Test the proof
service = lambda x: x * 2  # Service[int, int]
input_val = 21

result = modus_ponens(service, input_val)
assert result == 42
```

The fact that this compiles and runs proves the theorem is valid.
