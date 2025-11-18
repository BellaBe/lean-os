from typing import Generic, TypeVar, Callable

A = TypeVar('A')
B = TypeVar('B')
R = TypeVar('R')  # Config/Environment type

class Reader(Generic[R, A]):
    """Reader functor for dependency injection / multi-tenant"""

    def __init__(self, run: Callable[[R], A]):
        self._run = run

    def fmap(self, f: Callable[[A], B]) -> 'Reader[R, B]':
        """Transform result while preserving configuration dependency"""
        return Reader(lambda config: f(self._run(config)))

    def run(self, config: R) -> A:
        """Execute with configuration"""
        return self._run(config)

    @staticmethod
    def pure(value: A) -> 'Reader[R, A]':
        """Lift value into Reader"""
        return Reader(lambda _: value)

