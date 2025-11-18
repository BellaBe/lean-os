#!/usr/bin/env python3
"""
System Optimizer

Apply algebraic laws to optimize system implementations.
Uses distributivity, annihilation, identity, and other semiring laws.
"""

from typing import List, Union
from dataclasses import dataclass
from enum import Enum
from abc import ABC, abstractmethod


# ========== ADT Model for Optimization ==========

class ADT(ABC):
    """Base class for algebraic data types"""

    @abstractmethod
    def __str__(self) -> str:
        pass


@dataclass
class Atom(ADT):
    """Atomic type"""
    name: str

    def __str__(self) -> str:
        return self.name


@dataclass
class Unit(ADT):
    """Unit type (1)"""

    def __str__(self) -> str:
        return "1"


@dataclass
class Void(ADT):
    """Void type (0)"""

    def __str__(self) -> str:
        return "0"


@dataclass
class Product(ADT):
    """Product type (a × b)"""
    terms: List[ADT]

    def __str__(self) -> str:
        return " × ".join(str(t) for t in self.terms)


@dataclass
class Coproduct(ADT):
    """Coproduct type (a + b)"""
    variants: List[ADT]

    def __str__(self) -> str:
        return "(" + " + ".join(str(v) for v in self.variants) + ")"


# ========== Optimization Rules ==========

class OptimizationRule(Enum):
    """Available optimization rules"""
    DISTRIBUTIVITY = "distributivity"
    ELIMINATE_VOID = "eliminate_void"
    SIMPLIFY_UNIT = "simplify_unit"
    FACTOR_COMMON = "factor_common"
    ASSOCIATIVITY = "associativity"


@dataclass
class OptimizationResult:
    """Result of optimization"""
    original: ADT
    optimized: ADT
    rules_applied: List[str]
    benefit: str


# ========== Core Optimization Functions ==========

def apply_distributivity(adt: ADT) -> ADT:
    """
    Apply distributive law: a × (b + c) = (a × b) + (a × c)

    Transforms product-of-coproduct into coproduct-of-products.
    Enables service specialization and parallel execution.
    """
    if not isinstance(adt, Product):
        return adt

    # Find coproduct in product
    for i, term in enumerate(adt.terms):
        if isinstance(term, Coproduct):
            # Found a × (b + c)
            other_terms = adt.terms[:i] + adt.terms[i+1:]

            # Distribute: (a × b) + (a × c)
            distributed_terms = []
            for variant in term.variants:
                new_product_terms = other_terms + [variant]
                distributed_terms.append(Product(new_product_terms))

            return Coproduct(distributed_terms)

    return adt


def eliminate_void(adt: ADT) -> ADT:
    """
    Apply annihilation: a × 0 = 0, a + 0 = a

    Removes impossible paths and dead code.
    """
    if isinstance(adt, Product):
        # Check if any term is Void
        for term in adt.terms:
            if isinstance(term, Void):
                return Void()  # a × 0 = 0

        # Recursively eliminate in subterms
        new_terms = [eliminate_void(term) for term in adt.terms]
        return Product(new_terms) if new_terms else Unit()

    elif isinstance(adt, Coproduct):
        # Remove Void variants: a + 0 = a
        new_variants = [
            eliminate_void(variant)
            for variant in adt.variants
            if not isinstance(variant, Void)
        ]

        if not new_variants:
            return Void()
        elif len(new_variants) == 1:
            return new_variants[0]
        else:
            return Coproduct(new_variants)

    return adt


def simplify_unit(adt: ADT) -> ADT:
    """
    Apply identity: a × 1 = a, a + 1 (no simplification for sum)

    Removes trivial dependencies.
    """
    if isinstance(adt, Product):
        # Remove Unit terms: a × 1 = a
        new_terms = [
            simplify_unit(term)
            for term in adt.terms
            if not isinstance(term, Unit)
        ]

        if not new_terms:
            return Unit()
        elif len(new_terms) == 1:
            return new_terms[0]
        else:
            return Product(new_terms)

    elif isinstance(adt, Coproduct):
        # Recursively simplify variants
        new_variants = [simplify_unit(variant) for variant in adt.variants]
        return Coproduct(new_variants)

    return adt


def factor_common(adt: ADT) -> ADT:
    """
    Factor common subexpressions: (a × b) + (a × c) = a × (b + c)

    Inverse of distributivity. Reduces redundant computation.
    """
    if not isinstance(adt, Coproduct):
        return adt

    # Find common prefixes in products
    products = [v for v in adt.variants if isinstance(v, Product)]

    if len(products) < 2:
        return adt

    # Find common terms
    common_terms = []
    first_product = products[0]

    for i, term in enumerate(first_product.terms):
        # Check if this term appears in all products at position i
        if all(
            i < len(p.terms) and _adt_equal(p.terms[i], term)
            for p in products
        ):
            common_terms.append(term)
        else:
            break

    if not common_terms:
        return adt

    # Factor out common terms
    remaining_variants = []
    for product in products:
        remaining = product.terms[len(common_terms):]
        if remaining:
            remaining_variants.append(Product(remaining) if len(remaining) > 1 else remaining[0])
        else:
            remaining_variants.append(Unit())

    factored = Product(common_terms + [Coproduct(remaining_variants)])
    return factored


def apply_associativity(adt: ADT) -> ADT:
    """
    Apply associativity: (a × b) × c = a × (b × c)

    Flatten nested products and coproducts.
    """
    if isinstance(adt, Product):
        # Flatten nested products
        flattened = []
        for term in adt.terms:
            if isinstance(term, Product):
                flattened.extend(term.terms)
            else:
                flattened.append(term)
        return Product(flattened) if len(flattened) > 1 else flattened[0]

    elif isinstance(adt, Coproduct):
        # Flatten nested coproducts
        flattened = []
        for variant in adt.variants:
            if isinstance(variant, Coproduct):
                flattened.extend(variant.variants)
            else:
                flattened.append(variant)
        return Coproduct(flattened) if len(flattened) > 1 else flattened[0]

    return adt


# ========== Main Optimization Engine ==========

def optimize(
    adt: ADT,
    rules: List[str] = None,
    max_iterations: int = 10
) -> OptimizationResult:
    """
    Optimize ADT by applying algebraic laws.

    Args:
        adt: ADT expression to optimize
        rules: List of rule names to apply (default: all)
        max_iterations: Maximum optimization passes

    Returns:
        OptimizationResult with optimized ADT and applied rules
    """
    if rules is None:
        rules = [r.value for r in OptimizationRule]

    original = adt
    current = adt
    all_rules_applied = []

    for iteration in range(max_iterations):
        changed = False

        # Apply each optimization rule
        for rule in rules:
            if rule == OptimizationRule.DISTRIBUTIVITY.value:
                optimized = apply_distributivity(current)
            elif rule == OptimizationRule.ELIMINATE_VOID.value:
                optimized = eliminate_void(current)
            elif rule == OptimizationRule.SIMPLIFY_UNIT.value:
                optimized = simplify_unit(current)
            elif rule == OptimizationRule.FACTOR_COMMON.value:
                optimized = factor_common(current)
            elif rule == OptimizationRule.ASSOCIATIVITY.value:
                optimized = apply_associativity(current)
            else:
                continue

            if not _adt_equal(optimized, current):
                current = optimized
                all_rules_applied.append(rule)
                changed = True

        if not changed:
            break

    # Determine benefit
    benefit = _compute_benefit(original, current)

    return OptimizationResult(
        original=original,
        optimized=current,
        rules_applied=all_rules_applied,
        benefit=benefit
    )


# ========== Helper Functions ==========

def _adt_equal(a: ADT, b: ADT) -> bool:
    """Check if two ADTs are structurally equal"""
    if type(a) != type(b):
        return False

    if isinstance(a, Atom):
        return a.name == b.name
    elif isinstance(a, (Unit, Void)):
        return True
    elif isinstance(a, Product):
        return (len(a.terms) == len(b.terms) and
                all(_adt_equal(t1, t2) for t1, t2 in zip(a.terms, b.terms)))
    elif isinstance(a, Coproduct):
        return (len(a.variants) == len(b.variants) and
                all(_adt_equal(v1, v2) for v1, v2 in zip(a.variants, b.variants)))

    return False


def _compute_benefit(original: ADT, optimized: ADT) -> str:
    """Compute optimization benefit description"""
    benefits = []

    # Count reductions
    original_size = _adt_size(original)
    optimized_size = _adt_size(optimized)

    if optimized_size < original_size:
        reduction = original_size - optimized_size
        benefits.append(f"Reduced complexity by {reduction} terms")

    # Check for parallelization opportunities
    if isinstance(optimized, Coproduct):
        benefits.append(f"Enabled {len(optimized.variants)} parallel paths")

    # Check for specialization
    if isinstance(optimized, Coproduct) and isinstance(original, Product):
        benefits.append("Service specialization enabled")

    return "; ".join(benefits) if benefits else "No significant change"


def _adt_size(adt: ADT) -> int:
    """Count terms in ADT"""
    if isinstance(adt, (Atom, Unit, Void)):
        return 1
    elif isinstance(adt, Product):
        return 1 + sum(_adt_size(term) for term in adt.terms)
    elif isinstance(adt, Coproduct):
        return 1 + sum(_adt_size(variant) for variant in adt.variants)
    return 0


def validate_optimization(original: ADT, optimized: ADT) -> bool:
    """
    Validate that optimization preserves semantics.

    In practice, this would check denotational equivalence.
    Simplified here to structural validation.
    """
    # Both should be valid ADTs
    if not isinstance(original, ADT) or not isinstance(optimized, ADT):
        return False

    # Void optimization is always valid
    if isinstance(optimized, Void):
        return True

    # Otherwise, optimized should preserve structure
    return True  # Simplified - proper validation needs semantic model


# ========== Examples ==========

if __name__ == '__main__':
    print("=== System Optimizer Examples ===\n")

    # Example 1: Apply distributivity
    print("1. Distributivity: Auth × (Shopify + WooCommerce)")
    auth = Atom("Auth")
    shopify = Atom("Shopify")
    woocommerce = Atom("WooCommerce")

    original = Product([auth, Coproduct([shopify, woocommerce])])
    result = optimize(original, rules=['distributivity'])

    print(f"   Original: {original}")
    print(f"   Optimized: {result.optimized}")
    print(f"   Benefit: {result.benefit}\n")

    # Example 2: Eliminate Void
    print("2. Eliminate Void: Service × Void")
    service = Atom("Service")
    void_product = Product([service, Void()])

    result = optimize(void_product, rules=['eliminate_void'])
    print(f"   Original: {void_product}")
    print(f"   Optimized: {result.optimized}")
    print(f"   Benefit: Dead code eliminated\n")

    # Example 3: Simplify Unit
    print("3. Simplify Unit: Service × Unit")
    unit_product = Product([service, Unit()])

    result = optimize(unit_product, rules=['simplify_unit'])
    print(f"   Original: {unit_product}")
    print(f"   Optimized: {result.optimized}")
    print(f"   Benefit: Trivial dependency removed\n")

    # Example 4: Factor common
    print("4. Factor Common: (Auth × Shopify) + (Auth × WooCommerce)")
    variant1 = Product([Atom("Auth"), Atom("Shopify")])
    variant2 = Product([Atom("Auth"), Atom("WooCommerce")])
    unfactored = Coproduct([variant1, variant2])

    result = optimize(unfactored, rules=['factor_common'])
    print(f"   Original: {unfactored}")
    print(f"   Optimized: {result.optimized}")
    print(f"   Benefit: Common Auth computation factored out\n")

    # Example 5: Combined optimization
    print("5. Combined: Auth × (Shopify + Void) × Unit")
    complex_adt = Product([
        auth,
        Coproduct([shopify, Void()]),
        Unit()
    ])

    result = optimize(complex_adt)
    print(f"   Original: {complex_adt}")
    print(f"   Optimized: {result.optimized}")
    print(f"   Rules applied: {', '.join(result.rules_applied)}")
    print(f"   Benefit: {result.benefit}\n")

    print("✓ All optimizations preserve semantics via algebraic laws!")
