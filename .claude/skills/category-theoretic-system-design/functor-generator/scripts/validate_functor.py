#!/usr/bin/env python3
"""
Functor Law Validator

Validates that generated functors satisfy:
1. Identity preservation: F(id) = id
2. Composition preservation: F(g ∘ f) = F(g) ∘ F(f)
"""

import argparse
from typing import TypeVar, Callable, Generic, List
from dataclasses import dataclass

A = TypeVar('A')
B = TypeVar('B')
C = TypeVar('C')


@dataclass
class ValidationResult:
    passed: bool
    law: str
    details: str

    def __str__(self):
        status = "✓ PASS" if self.passed else "✗ FAIL"
        return f"{status}: {self.law}\n  {self.details}"


class FunctorValidator:
    """Validate functor laws"""

    def validate_identity(self, functor_class, test_values: List) -> ValidationResult:
        """
        Test: F(id) = id

        For all test values, verify that mapping identity function
        is the same as applying identity to the functor
        """
        def identity(x):
            return x

        failures = []

        for value in test_values:
            try:
                # Wrap in functor
                fa = self._wrap_value(functor_class, value)

                # Path 1: fmap id
                result1 = self._fmap(functor_class, identity, fa)

                # Path 2: id
                result2 = identity(fa)

                if not self._equal(result1, result2):
                    failures.append(f"Value {value}: fmap(id) != id")
            except Exception as e:
                failures.append(f"Value {value}: Exception - {str(e)}")

        if failures:
            return ValidationResult(
                passed=False,
                law="Identity (F(id) = id)",
                details="\n  ".join(failures)
            )

        return ValidationResult(
            passed=True,
            law="Identity (F(id) = id)",
            details=f"Passed for {len(test_values)} test values"
        )

    def validate_composition(
        self,
        functor_class,
        f: Callable,
        g: Callable,
        test_values: List
    ) -> ValidationResult:
        """
        Test: F(g ∘ f) = F(g) ∘ F(f)

        Verify composition is preserved
        """
        def compose(g, f):
            return lambda x: g(f(x))

        failures = []

        for value in test_values:
            try:
                # Wrap in functor
                fa = self._wrap_value(functor_class, value)

                # Path 1: fmap (g ∘ f)
                composed = compose(g, f)
                result1 = self._fmap(functor_class, composed, fa)

                # Path 2: fmap g ∘ fmap f
                fmap_f = self._fmap(functor_class, f, fa)
                result2 = self._fmap(functor_class, g, fmap_f)

                if not self._equal(result1, result2):
                    failures.append(f"Value {value}: fmap(g∘f) != fmap(g)∘fmap(f)")
            except Exception as e:
                failures.append(f"Value {value}: Exception - {str(e)}")

        if failures:
            return ValidationResult(
                passed=False,
                law="Composition (F(g∘f) = F(g)∘F(f))",
                details="\n  ".join(failures)
            )

        return ValidationResult(
            passed=True,
            law="Composition (F(g∘f) = F(g)∘F(f))",
            details=f"Passed for {len(test_values)} test values"
        )

    def validate_all_laws(
        self,
        functor_class,
        test_values: List = None
    ) -> List[ValidationResult]:
        """
        Validate all functor laws.

        Returns list of validation results.
        """
        if test_values is None:
            test_values = [1, 5, 10, "hello", [1,2,3]]

        results = []

        # Test identity law
        identity_result = self.validate_identity(functor_class, test_values)
        results.append(identity_result)

        # Test composition law with sample functions
        def f(x):
            if isinstance(x, int):
                return x + 1
            elif isinstance(x, str):
                return x + "!"
            elif isinstance(x, list):
                return x + [0]
            return x

        def g(x):
            if isinstance(x, int):
                return x * 2
            elif isinstance(x, str):
                return x.upper()
            elif isinstance(x, list):
                return len(x)
            return x

        composition_result = self.validate_composition(
            functor_class, f, g, test_values
        )
        results.append(composition_result)

        return results

    def _wrap_value(self, functor_class, value):
        """Wrap value in functor"""
        if hasattr(functor_class, 'pure'):
            return functor_class.pure(value)
        elif hasattr(functor_class, '__init__'):
            return functor_class(value)
        else:
            raise ValueError(f"Don't know how to wrap value in {functor_class}")

    def _fmap(self, functor_class, f, functor_value):
        """Apply fmap"""
        # Check if it's an instance with fmap method
        if hasattr(functor_value, 'fmap'):
            return functor_value.fmap(f)
        # Check if class has static fmap
        elif hasattr(functor_class, 'fmap'):
            return functor_class.fmap(f)(functor_value)
        else:
            raise ValueError(f"Don't know how to fmap for {functor_class}")

    def _equal(self, a, b) -> bool:
        """Compare functor values"""
        # Try direct equality
        try:
            return a == b
        except:
            pass

        # Try extracting and comparing values
        try:
            val_a = self._extract_value(a)
            val_b = self._extract_value(b)
            return val_a == val_b
        except:
            pass

        # Last resort: string comparison
        return str(a) == str(b)

    def _extract_value(self, functor_value):
        """Extract wrapped value"""
        if hasattr(functor_value, 'value'):
            return functor_value.value
        if hasattr(functor_value, 'run'):
            # Try to run with dummy config
            try:
                return functor_value.run(None)
            except:
                pass
        return functor_value


# ========== Specific Functor Validators ==========

def validate_maybe_functor():
    """Validate Maybe functor specifically"""
    from functor_generator import Maybe, Just, Nothing, maybe_fmap

    class MaybeFunctor:
        @staticmethod
        def pure(value):
            return Just(value)

        @staticmethod
        def fmap(f):
            return maybe_fmap(f)

    validator = FunctorValidator()
    results = validator.validate_all_laws(MaybeFunctor)

    print("=== Maybe Functor Validation ===")
    for result in results:
        print(result)
        print()

    return all(r.passed for r in results)


def validate_list_functor():
    """Validate List functor"""
    from functor_generator import list_fmap

    class ListFunctor:
        @staticmethod
        def pure(value):
            return [value]

        @staticmethod
        def fmap(f):
            return list_fmap(f)

    validator = FunctorValidator()
    results = validator.validate_all_laws(
        ListFunctor,
        test_values=[[1,2,3], [4,5], [], [10]]
    )

    print("=== List Functor Validation ===")
    for result in results:
        print(result)
        print()

    return all(r.passed for r in results)


def validate_either_functor():
    """Validate Either functor"""
    from functor_generator import Either, Left, Right, either_fmap

    class EitherFunctor:
        @staticmethod
        def pure(value):
            return Right(value)

        @staticmethod
        def fmap(f):
            return either_fmap(f)

    validator = FunctorValidator()
    results = validator.validate_all_laws(EitherFunctor)

    print("=== Either Functor Validation ===")
    for result in results:
        print(result)
        print()

    return all(r.passed for r in results)


def validate_reader_functor():
    """Validate Reader functor"""
    from functor_generator import Reader

    validator = FunctorValidator()

    # Test with Reader
    test_configs = [
        {"env": "prod"},
        {"env": "dev"},
        {"env": "test"}
    ]

    # Create readers that extract config values
    readers = [Reader(lambda cfg: cfg.get("env")) for _ in test_configs]

    # Custom validation for Reader
    def identity(x):
        return x

    def f(x):
        return x.upper() if isinstance(x, str) else x

    def g(x):
        return x + "!" if isinstance(x, str) else x

    def compose(g, f):
        return lambda x: g(f(x))

    print("=== Reader Functor Validation ===")

    # Test identity
    identity_passed = True
    for cfg in test_configs:
        reader = Reader.pure(cfg["env"])
        result1 = reader.fmap(identity).run(cfg)
        result2 = identity(reader.run(cfg))
        if result1 != result2:
            identity_passed = False
            print(f"✗ Identity failed for config {cfg}")

    if identity_passed:
        print("✓ Identity law passed")

    # Test composition
    composition_passed = True
    for cfg in test_configs:
        reader = Reader.pure(cfg["env"])
        result1 = reader.fmap(compose(g, f)).run(cfg)
        result2 = reader.fmap(f).fmap(g).run(cfg)
        if result1 != result2:
            composition_passed = False
            print(f"✗ Composition failed for config {cfg}")

    if composition_passed:
        print("✓ Composition law passed")

    print()
    return identity_passed and composition_passed


# ========== Main CLI ==========

def main():
    parser = argparse.ArgumentParser(description='Validate functor laws')
    parser.add_argument(
        '--functor',
        choices=['maybe', 'list', 'either', 'reader', 'all'],
        default='all',
        help='Functor type to validate'
    )

    args = parser.parse_args()

    results = {}

    if args.functor == 'maybe' or args.functor == 'all':
        results['maybe'] = validate_maybe_functor()

    if args.functor == 'list' or args.functor == 'all':
        results['list'] = validate_list_functor()

    if args.functor == 'either' or args.functor == 'all':
        results['either'] = validate_either_functor()

    if args.functor == 'reader' or args.functor == 'all':
        results['reader'] = validate_reader_functor()

    # Summary
    print("=" * 60)
    print("VALIDATION SUMMARY")
    print("=" * 60)
    for name, passed in results.items():
        status = "✓ PASS" if passed else "✗ FAIL"
        print(f"{name.capitalize()}: {status}")
    print()

    all_passed = all(results.values())
    if all_passed:
        print("✓ All functor laws validated successfully!")
        return 0
    else:
        print("✗ Some functor laws failed validation")
        return 1


if __name__ == '__main__':
    exit(main())
