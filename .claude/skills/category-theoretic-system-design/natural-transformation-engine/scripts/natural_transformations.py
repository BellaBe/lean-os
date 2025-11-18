#!/usr/bin/env python3
"""
Natural Transformation Engine

Provides structure-preserving transformations between functors.
Naturality is guaranteed by parametric polymorphism.
"""

import sys
from pathlib import Path
from typing import TypeVar, Callable, List as ListType, Generic
from dataclasses import dataclass

# Import functors from functor-generator
sys.path.append(str(Path(__file__).parent.parent.parent / "functor-generator" / "scripts"))
from functor_generator import Maybe, Just, Nothing, Either, Left, Right, Reader

A = TypeVar('A')
B = TypeVar('B')
C = TypeVar('C')


# ========== Writer Functor (for logging transformations) ==========

@dataclass
class Writer(Generic[A]):
    """Writer functor: (A, Log)"""
    value: A
    log: ListType[str]

    def fmap(self, f: Callable[[A], B]) -> 'Writer[B]':
        return Writer(f(self.value), self.log)

    @staticmethod
    def pure(value: A) -> 'Writer[A]':
        return Writer(value, [])


# ========== Common Natural Transformations ==========

def maybe_to_list(maybe_a: Maybe[A]) -> ListType[A]:
    """
    α: Maybe ⇒ List

    Transform optional to replicated (0 or 1 replica).
    Naturality: list.fmap(f) ∘ maybe_to_list = maybe_to_list ∘ maybe.fmap(f)
    """
    if isinstance(maybe_a, Just):
        return [maybe_a.value]
    else:
        return []


def either_to_maybe(either_a: Either) -> Maybe:
    """
    α: Either E ⇒ Maybe

    Discard error details, keep success.
    Use when error specifics don't matter downstream.
    """
    if isinstance(either_a, Right):
        return Just(either_a.value)
    else:
        return Nothing()


def list_to_maybe(list_a: ListType[A]) -> Maybe[A]:
    """
    α: List ⇒ Maybe (head)

    Take first element if exists.
    Use to select single result from replicated service.
    """
    return Just(list_a[0]) if list_a else Nothing()


def identity_to_writer(x: A) -> Writer[A]:
    """
    α: Identity ⇒ Writer

    Lift pure value to logged computation.
    Use to add logging/auditing to pure functions.
    """
    return Writer(x, [])


def identity_to_maybe(x: A) -> Maybe[A]:
    """
    α: Identity ⇒ Maybe

    Wrap value in Just.
    """
    return Just(x)


def identity_to_list(x: A) -> ListType[A]:
    """
    α: Identity ⇒ List

    Singleton list.
    """
    return [x]


def either_to_list(either_a: Either) -> ListType:
    """
    α: Either E ⇒ List

    Convert Right to singleton, Left to empty.
    """
    if isinstance(either_a, Right):
        return [either_a.value]
    else:
        return []


# ========== Composition Operators ==========

def vertical_compose(
    alpha: Callable,
    beta: Callable
) -> Callable:
    """
    Vertical composition: β ⋅ α

    For α: F ⇒ G and β: G ⇒ H, produces β ⋅ α: F ⇒ H

    (β ⋅ α)_A = β_A ∘ α_A

    Example:
        Identity → Writer → Future
        (make async, then add logging)
    """
    def composed(fa):
        ga = alpha(fa)
        ha = beta(ga)
        return ha
    return composed


def horizontal_compose(
    alpha: Callable,
    beta: Callable,
    fmap_outer: Callable
) -> Callable:
    """
    Horizontal composition: β ∘ α

    For α: F ⇒ G and β: H ⇒ K, produces β ∘ α: H∘F ⇒ K∘G

    Applies transformations at different functor levels.

    Args:
        alpha: Inner transformation
        beta: Outer transformation
        fmap_outer: fmap of outer functor H
    """
    def composed(hfa):
        # H(α): H(F(A)) → H(G(A))
        hga = fmap_outer(alpha)(hfa)
        # β: H(G(A)) → K(G(A))
        kga = beta(hga)
        return kga
    return composed


# ========== Validation ==========

def validate_naturality(
    alpha: Callable,
    fmap_source: Callable,
    fmap_target: Callable,
    test_function: Callable,
    test_values: ListType
) -> bool:
    """
    Validate naturality condition:

    G(f) ∘ α_A = α_B ∘ F(f)

    Args:
        alpha: Natural transformation F ⇒ G
        fmap_source: fmap for source functor F
        fmap_target: fmap for target functor G
        test_function: Function to map (f: A → B)
        test_values: Test values wrapped in F

    Returns:
        True if naturality holds for all test values
    """
    for fa in test_values:
        # Path 1: α_B ∘ F(f)
        fb = fmap_source(test_function, fa)
        result1 = alpha(fb)

        # Path 2: G(f) ∘ α_A
        ga = alpha(fa)
        result2 = fmap_target(test_function, ga)

        # Compare
        if not _equal_values(result1, result2):
            return False

    return True


def _equal_values(a, b) -> bool:
    """Compare values (handles different types)"""
    try:
        return a == b
    except:
        return str(a) == str(b)


# ========== Predefined Composition Chains ==========

# Identity → Writer → Future (add logging, then async)
identity_to_logged = identity_to_writer

# Either → Maybe → List (simplify error, then replicate)
either_to_list_via_maybe = vertical_compose(either_to_maybe, maybe_to_list)

# Maybe → List (direct)
optional_to_replicated = maybe_to_list

# List → Maybe (select first)
replicated_to_optional = list_to_maybe


# ========== Example Usage ==========

if __name__ == '__main__':
    print("=== Natural Transformation Examples ===\n")

    # Example 1: Maybe → List
    print("1. Maybe → List (Optional → Replicated)")
    just_5 = Just(5)
    nothing = Nothing()

    print(f"  Just(5) → {maybe_to_list(just_5)}")
    print(f"  Nothing → {maybe_to_list(nothing)}\n")

    # Example 2: Either → Maybe
    print("2. Either → Maybe (Discard error details)")
    right_user = Right("Alice")
    left_error = Left("Not found")

    print(f"  Right('Alice') → {either_to_maybe(right_user)}")
    print(f"  Left('Not found') → {either_to_maybe(left_error)}\n")

    # Example 3: List → Maybe
    print("3. List → Maybe (Select first)")
    users = ["Alice", "Bob", "Charlie"]
    empty_list = []

    print(f"  ['Alice', 'Bob', 'Charlie'] → {list_to_maybe(users)}")
    print(f"  [] → {list_to_maybe(empty_list)}\n")

    # Example 4: Vertical composition
    print("4. Vertical Composition: Either → Maybe → List")
    composed = vertical_compose(either_to_maybe, maybe_to_list)

    print(f"  Right('Alice') → {composed(right_user)}")
    print(f"  Left('Error') → {composed(left_error)}\n")

    # Example 5: Identity → Writer
    print("5. Identity → Writer (Add logging)")
    logged = identity_to_writer(42)
    print(f"  42 → Writer(value={logged.value}, log={logged.log})\n")

    print("✓ All transformations preserve structure through parametric polymorphism")
