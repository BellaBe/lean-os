# Ex Falso Quodlibet - From Falsehood, Anything

## Logical Statement
False ⇒ A  (for any A)

In words: "From a false premise, anything follows."

## Translation to Types
```python
from typing import Never

def absurd(impossible: Never) -> Any:
    """
    Takes an impossible value, produces any type

    This function can never actually execute,
    because Never has no values
    """
    # This line never runs
    raise RuntimeError("Unreachable")
```

## Curry-Howard Correspondence

| Logic | Types | Python |
|-------|-------|--------|
| False | Void/Never | Never |
| True | Unit | None |
| False ⇒ A | Void → A | Never → Any |

## System Application

**Theorem:** "If a service dependency is impossible, the service itself is impossible"
```python
def impossible_service(
    impossible_dep: Never
) -> ServiceResult:
    """
    Service that requires impossible dependency

    This proves: Service × Void = Void
    """
    # Can never be called
    ...
```

**Proof:** Since Never has no values, this function can never be called. The type system prevents impossible states. ∎

## Practical Use
```python
def safe_division(a: float, b: float) -> float | Never:
    """
    Division that makes impossibility explicit
    """
    if b == 0:
        # Signal impossible case via type
        raise ValueError("Division by zero")
    return a / b

# Type checker knows division by zero is impossible
result: float = safe_division(10, 2)  # OK
impossible: float = safe_division(10, 0)  # Type error caught!
```

## Verification

The type system itself verifies this theorem. If code compiles, impossible states are unreachable.
```python
# This won't compile
never_value: Never = ...  # Cannot construct Never
result = absurd(never_value)  # Therefore this never executes
```

The inability to construct Never proves ex falso quodlibet.
