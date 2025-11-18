#!/usr/bin/env python3
"""
Functor Generator

Generates structure-preserving functors for common patterns:
- Reader (Config → Service)
- Maybe (Optional Service)
- List (Replicated Service)
- Either (Error handling)
- State (Stateful Service)
- Future (Async Service)
"""

from typing import TypeVar, Generic, Callable, List as ListType, Optional
from dataclasses import dataclass
from enum import Enum


A = TypeVar('A')
B = TypeVar('B')
C = TypeVar('C')
R = TypeVar('R')  # Reader environment
S = TypeVar('S')  # State
E = TypeVar('E')  # Error type


class FunctorType(Enum):
    READER = "reader"
    MAYBE = "maybe"
    LIST = "list"
    EITHER = "either"
    STATE = "state"
    FUTURE = "future"


# ========== Reader Functor ==========

class Reader(Generic[R, A]):
    """
    Reader functor: R → A

    Use for dependency injection, multi-tenant, environment config.
    """

    def __init__(self, run: Callable[[R], A]):
        self.run = run

    @staticmethod
    def pure(value: A) -> 'Reader[R, A]':
        """Lift a value into Reader"""
        return Reader(lambda _: value)

    def fmap(self, f: Callable[[A], B]) -> 'Reader[R, B]':
        """(A → B) → Reader R A → Reader R B"""
        return Reader(lambda r: f(self.run(r)))

    def apply_config(self, config: R) -> A:
        """Run the reader with a configuration"""
        return self.run(config)


def generate_reader_functor(base_service: Callable, config_type: str) -> type:
    """
    Generate Reader functor for a service.

    Args:
        base_service: Original service function
        config_type: Type of configuration

    Returns:
        Reader functor class
    """
    class GeneratedReaderFunctor(Reader):
        def __init__(self, service_fn):
            super().__init__(service_fn)

    return GeneratedReaderFunctor


# ========== Maybe Functor ==========

class Maybe(Generic[A]):
    """
    Maybe functor: 1 + A

    Use for optional features, feature flags, graceful degradation.
    """
    pass


class Just(Maybe[A]):
    """Just a value"""
    def __init__(self, value: A):
        self.value = value

    def __eq__(self, other):
        return isinstance(other, Just) and self.value == other.value

    def __repr__(self):
        return f"Just({self.value})"


class Nothing(Maybe[A]):
    """No value"""
    def __eq__(self, other):
        return isinstance(other, Nothing)

    def __repr__(self):
        return "Nothing"


def maybe_fmap(f: Callable[[A], B]) -> Callable[[Maybe[A]], Maybe[B]]:
    """(A → B) → Maybe A → Maybe B"""
    def transform(maybe_a: Maybe[A]) -> Maybe[B]:
        if isinstance(maybe_a, Just):
            return Just(f(maybe_a.value))
        else:
            return Nothing()
    return transform


def generate_maybe_functor(base_service: Callable, condition: Callable) -> Callable:
    """
    Generate Maybe functor for a service.

    Args:
        base_service: Original service
        condition: Function to determine if service should run

    Returns:
        Service wrapped in Maybe
    """
    def maybe_service(*args, **kwargs):
        if condition():
            try:
                result = base_service(*args, **kwargs)
                return Just(result)
            except:
                return Nothing()
        else:
            return Nothing()
    return maybe_service


# ========== List Functor ==========

def list_fmap(f: Callable[[A], B]) -> Callable[[ListType[A]], ListType[B]]:
    """(A → B) → List A → List B"""
    def transform(list_a: ListType[A]) -> ListType[B]:
        return [f(x) for x in list_a]
    return transform


def generate_list_functor(base_service: Callable, replicas: ListType) -> Callable:
    """
    Generate List functor for replicated services.

    Args:
        base_service: Original service
        replicas: List of service instances/configs

    Returns:
        Service that returns list of results
    """
    def list_service(*args, **kwargs):
        return [base_service(*args, config=replica, **kwargs) for replica in replicas]
    return list_service


# ========== Either Functor ==========

class Either(Generic[E, A]):
    """Either functor: E + A"""
    pass


class Left(Either[E, A]):
    """Left (error) case"""
    def __init__(self, value: E):
        self.value = value

    def __eq__(self, other):
        return isinstance(other, Left) and self.value == other.value

    def __repr__(self):
        return f"Left({self.value})"


class Right(Either[E, A]):
    """Right (success) case"""
    def __init__(self, value: A):
        self.value = value

    def __eq__(self, other):
        return isinstance(other, Right) and self.value == other.value

    def __repr__(self):
        return f"Right({self.value})"


def either_fmap(f: Callable[[A], B]) -> Callable[[Either[E, A]], Either[E, B]]:
    """(A → B) → Either E A → Either E B"""
    def transform(either_a: Either[E, A]) -> Either[E, B]:
        if isinstance(either_a, Right):
            return Right(f(either_a.value))
        else:
            return either_a  # Preserve Left
    return transform


def generate_either_functor(base_service: Callable, error_type: type) -> Callable:
    """
    Generate Either functor for error handling.

    Args:
        base_service: Original service (may raise exceptions)
        error_type: Type of errors to catch

    Returns:
        Service wrapped in Either
    """
    def either_service(*args, **kwargs):
        try:
            result = base_service(*args, **kwargs)
            return Right(result)
        except error_type as e:
            return Left(e)
        except Exception as e:
            return Left(error_type(str(e)))
    return either_service


# ========== State Functor ==========

class State(Generic[S, A]):
    """
    State functor: S → (A, S)

    Use for stateful computations, workflows.
    """

    def __init__(self, run: Callable[[S], tuple[A, S]]):
        self.run = run

    @staticmethod
    def pure(value: A) -> 'State[S, A]':
        """Lift value into State without changing state"""
        return State(lambda s: (value, s))

    def fmap(self, f: Callable[[A], B]) -> 'State[S, B]':
        """(A → B) → State S A → State S B"""
        def new_run(s):
            (a, s_new) = self.run(s)
            return (f(a), s_new)
        return State(new_run)


# ========== Functor Generator ==========

def generate_functor(
    functor_type: FunctorType,
    base_service: Callable,
    **kwargs
) -> Callable:
    """
    Main functor generator.

    Args:
        functor_type: Type of functor to generate
        base_service: Base service to transform
        **kwargs: Type-specific parameters

    Returns:
        Generated functor-wrapped service
    """
    if functor_type == FunctorType.READER:
        return generate_reader_functor(base_service, kwargs.get('config_type'))
    elif functor_type == FunctorType.MAYBE:
        return generate_maybe_functor(base_service, kwargs.get('condition'))
    elif functor_type == FunctorType.LIST:
        return generate_list_functor(base_service, kwargs.get('replicas'))
    elif functor_type == FunctorType.EITHER:
        return generate_either_functor(base_service, kwargs.get('error_type'))
    else:
        raise ValueError(f"Unsupported functor type: {functor_type}")


# ========== Example Usage ==========

if __name__ == '__main__':
    # Example: Reader functor for multi-tenant
    def greet(name: str, config) -> str:
        return f"{config.greeting}, {name}!"

    @dataclass
    class Config:
        greeting: str

    prod_config = Config(greeting="Hello")
    dev_config = Config(greeting="Hey")

    # Generate Reader functor
    greet_reader = Reader(lambda cfg: lambda name: greet(name, cfg))

    # Use with different configs
    prod_greet = greet_reader.apply_config(prod_config)
    dev_greet = greet_reader.apply_config(dev_config)

    print(prod_greet("Alice"))  # "Hello, Alice!"
    print(dev_greet("Bob"))     # "Hey, Bob!"

    # Example: Maybe functor for optional feature
    def expensive_analysis(data):
        # Expensive computation
        return sum(data) * 2

    maybe_analysis = generate_maybe_functor(
        expensive_analysis,
        condition=lambda: True  # Feature flag
    )

    result = maybe_analysis([1, 2, 3])
    print(result)  # Just(12)

    # Example: Either functor for error handling
    def divide(a: int, b: int) -> float:
        if b == 0:
            raise ValueError("Division by zero")
        return a / b

    safe_divide = generate_either_functor(divide, ValueError)

    print(safe_divide(10, 2))  # Right(5.0)
    print(safe_divide(10, 0))  # Left(ValueError(...))
