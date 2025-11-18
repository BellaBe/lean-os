#!/usr/bin/env python3
"""
Architecture Validator

Validate system architecture for categorical correctness.
Checks category laws, functor laws, and universal constructions.
"""

from dataclasses import dataclass
from typing import List, Dict, Set, Callable, Optional, Any
from enum import Enum


# ========== Architecture Model ==========

@dataclass
class Service:
    """Service (morphism) in architecture"""
    name: str
    source: str  # Source type
    target: str  # Target type
    implementation: Optional[Callable] = None

    def __str__(self):
        return f"{self.name}: {self.source} → {self.target}"


@dataclass
class Architecture:
    """System architecture as category"""
    services: List[Service]
    types: Set[str]
    identities: Dict[str, Service]  # Type → identity service
    compositions: List[tuple[Service, Service, Service]]  # (f, g, g∘f)


# ========== Validation Result ==========

class ViolationType(Enum):
    IDENTITY = "identity"
    COMPOSITION = "composition"
    ASSOCIATIVITY = "associativity"
    FUNCTOR_IDENTITY = "functor_identity"
    FUNCTOR_COMPOSITION = "functor_composition"
    PRODUCT = "product"
    TERMINAL = "terminal"
    TYPE_MISMATCH = "type_mismatch"


@dataclass
class Violation:
    """Validation violation"""
    law: str
    violation_type: ViolationType
    description: str
    suggested_fix: str
    severity: str  # "error", "warning"


@dataclass
class ValidationReport:
    """Validation report"""
    passed: bool
    total_checks: int
    passed_checks: int
    violations: List[Violation]

    def __str__(self):
        lines = ["Architecture Validation Report", "=" * 40, ""]

        # Summary
        status = "✓ PASSED" if self.passed else "✗ FAILED"
        lines.append(f"Status: {status}")
        lines.append(f"Score: {self.passed_checks}/{self.total_checks} checks passed")
        lines.append("")

        # Violations
        if self.violations:
            lines.append("Violations:")
            for v in self.violations:
                severity_symbol = "✗" if v.severity == "error" else "⚠"
                lines.append(f"{severity_symbol} {v.law}: {v.description}")
                lines.append(f"  Fix: {v.suggested_fix}")
                lines.append("")
        else:
            lines.append("✓ No violations found")

        return "\n".join(lines)


# ========== Validation Functions ==========

def validate_identity_law(arch: Architecture) -> List[Violation]:
    """
    Validate identity law: Every object has an identity morphism.

    For all A: exists id_A: A → A
    """
    violations = []

    for type_name in arch.types:
        if type_name not in arch.identities:
            violations.append(Violation(
                law="Identity Law",
                violation_type=ViolationType.IDENTITY,
                description=f"Type '{type_name}' has no identity service",
                suggested_fix=f"Add identity service: identity({type_name}): {type_name} → {type_name}",
                severity="error"
            ))

    return violations


def validate_composition(arch: Architecture) -> List[Violation]:
    """
    Validate composition: Services compose when types align.

    For f: A → B, g: B → C: must be able to compose g ∘ f
    """
    violations = []

    services_by_source = {}
    for service in arch.services:
        if service.source not in services_by_source:
            services_by_source[service.source] = []
        services_by_source[service.source].append(service)

    for service_f in arch.services:
        # Find services g where g.source == f.target
        target_type = service_f.target
        if target_type in services_by_source:
            for service_g in services_by_source[target_type]:
                # Check if composition exists
                composed = _find_composition(arch, service_f, service_g)
                if composed is None:
                    violations.append(Violation(
                        law="Composition",
                        violation_type=ViolationType.COMPOSITION,
                        description=f"Missing composition: {service_g.name} ∘ {service_f.name}",
                        suggested_fix=f"Add composed service: {service_f.source} → {service_g.target}",
                        severity="warning"
                    ))

    return violations


def validate_associativity(arch: Architecture) -> List[Violation]:
    """
    Validate associativity: (h ∘ g) ∘ f = h ∘ (g ∘ f)

    Composition grouping doesn't matter.
    """
    violations = []

    # Test associativity for chains of 3 services
    tested = 0
    for f in arch.services:
        for g in arch.services:
            if g.source != f.target:
                continue
            for h in arch.services:
                if h.source != g.target:
                    continue

                # Found chain f → g → h
                tested += 1

                # Path 1: (h ∘ g) ∘ f
                g_comp_f = _find_composition(arch, f, g)
                if g_comp_f:
                    h_comp_gf = _find_composition(arch, g_comp_f, h)

                # Path 2: h ∘ (g ∘ f)
                h_comp_g = _find_composition(arch, g, h)
                if h_comp_g:
                    hg_comp_f = _find_composition(arch, f, h_comp_g)

                # Both should exist and be equal (simplified check)
                if (g_comp_f and h_comp_g and h_comp_gf and hg_comp_f):
                    # Both paths exist - good
                    pass
                elif tested > 0:
                    violations.append(Violation(
                        law="Associativity",
                        violation_type=ViolationType.ASSOCIATIVITY,
                        description=f"Associativity may not hold for chain {f.name} → {g.name} → {h.name}",
                        suggested_fix="Ensure all compositions are properly defined",
                        severity="warning"
                    ))
                    break

    return violations


def validate_functor_laws(functor_class: Any, test_values: List) -> List[Violation]:
    """
    Validate functor laws:
    1. F(id) = id
    2. F(g ∘ f) = F(g) ∘ F(f)
    """
    violations = []

    # Import validation from functor-generator if available
    try:
        import sys
        from pathlib import Path
        sys.path.append(str(Path(__file__).parent.parent.parent / "functor-generator" / "scripts"))
        from validate_functor import FunctorValidator

        validator = FunctorValidator()
        results = validator.validate_all_laws(functor_class, test_values)

        for result in results:
            if not result.passed:
                violations.append(Violation(
                    law=result.law,
                    violation_type=ViolationType.FUNCTOR_IDENTITY if "Identity" in result.law else ViolationType.FUNCTOR_COMPOSITION,
                    description=result.details,
                    suggested_fix="Fix functor implementation to satisfy laws",
                    severity="error"
                ))
    except ImportError:
        pass

    return violations


def validate_terminal_object(arch: Architecture) -> List[Violation]:
    """
    Validate terminal object exists.

    Terminal object: For all A, exists unique f: A → Terminal
    """
    violations = []

    # Find candidates for terminal object
    # Terminal should have morphisms from all other objects
    terminal_candidates = []

    for service in arch.services:
        target = service.target
        # Check if all types have morphism to this target
        sources = {s.source for s in arch.services if s.target == target}
        if sources == arch.types or len(sources) == len(arch.types):
            terminal_candidates.append(target)

    if not terminal_candidates:
        violations.append(Violation(
            law="Terminal Object",
            violation_type=ViolationType.TERMINAL,
            description="No terminal object found",
            suggested_fix="Add Unit type with morphisms from all types",
            severity="warning"
        ))

    return violations


def validate_products(arch: Architecture) -> List[Violation]:
    """
    Validate products have projections.

    For product A × B, must have:
    - π₁: A × B → A
    - π₂: A × B → B
    """
    violations = []

    # Find product types (simplified - look for "×" in type name)
    product_types = [t for t in arch.types if "×" in t or " × " in t]

    for product_type in product_types:
        # Parse product components (simplified)
        if "×" in product_type:
            parts = product_type.split("×")
            if len(parts) == 2:
                type_a = parts[0].strip()
                type_b = parts[1].strip()

                # Check for projections
                has_proj1 = any(
                    s.source == product_type and s.target == type_a
                    for s in arch.services
                )
                has_proj2 = any(
                    s.source == product_type and s.target == type_b
                    for s in arch.services
                )

                if not has_proj1:
                    violations.append(Violation(
                        law="Product Projections",
                        violation_type=ViolationType.PRODUCT,
                        description=f"Product {product_type} missing first projection π₁",
                        suggested_fix=f"Add projection: π₁: {product_type} → {type_a}",
                        severity="error"
                    ))

                if not has_proj2:
                    violations.append(Violation(
                        law="Product Projections",
                        violation_type=ViolationType.PRODUCT,
                        description=f"Product {product_type} missing second projection π₂",
                        suggested_fix=f"Add projection: π₂: {product_type} → {type_b}",
                        severity="error"
                    ))

    return violations


# ========== Main Validation ==========

def validate(
    arch: Architecture,
    checks: List[str] = None
) -> ValidationReport:
    """
    Validate architecture against category laws.

    Args:
        arch: Architecture to validate
        checks: List of checks to run (default: all)

    Returns:
        ValidationReport with results
    """
    if checks is None:
        checks = [
            'identity',
            'composition',
            'associativity',
            'terminal',
            'products'
        ]

    all_violations = []

    # Run checks
    if 'identity' in checks:
        all_violations.extend(validate_identity_law(arch))

    if 'composition' in checks:
        all_violations.extend(validate_composition(arch))

    if 'associativity' in checks:
        all_violations.extend(validate_associativity(arch))

    if 'terminal' in checks:
        all_violations.extend(validate_terminal_object(arch))

    if 'products' in checks:
        all_violations.extend(validate_products(arch))

    # Count checks
    total_checks = len(checks)
    error_violations = [v for v in all_violations if v.severity == "error"]
    passed_checks = total_checks - len(set(v.violation_type for v in error_violations))

    return ValidationReport(
        passed=len(error_violations) == 0,
        total_checks=total_checks,
        passed_checks=passed_checks,
        violations=all_violations
    )


# ========== Helper Functions ==========

def _find_composition(
    arch: Architecture,
    f: Service,
    g: Service
) -> Optional[Service]:
    """Find composition g ∘ f if it exists"""
    for comp_f, comp_g, result in arch.compositions:
        if comp_f.name == f.name and comp_g.name == g.name:
            return result
    return None


# ========== Examples ==========

if __name__ == '__main__':
    print("=== Architecture Validator Examples ===\n")

    # Example 1: Valid architecture
    print("1. Valid Architecture")
    arch1 = Architecture(
        services=[
            Service("id_User", "User", "User"),
            Service("id_Product", "Product", "Product"),
            Service("getUserProfile", "User", "Profile"),
            Service("getRecommendations", "Profile", "ProductList"),
        ],
        types={"User", "Product", "Profile", "ProductList"},
        identities={
            "User": Service("id_User", "User", "User"),
            "Product": Service("id_Product", "Product", "Product"),
        },
        compositions=[]
    )

    report1 = validate(arch1)
    print(report1)
    print()

    # Example 2: Missing identity
    print("2. Missing Identity")
    arch2 = Architecture(
        services=[
            Service("getUserProfile", "User", "Profile"),
        ],
        types={"User", "Profile"},
        identities={},  # No identities!
        compositions=[]
    )

    report2 = validate(arch2)
    print(report2)
    print()

    # Example 3: Product without projections
    print("3. Product Without Projections")
    arch3 = Architecture(
        services=[
            Service("id_User × Product", "User × Product", "User × Product"),
        ],
        types={"User", "Product", "User × Product"},
        identities={"User × Product": Service("id_User × Product", "User × Product", "User × Product")},
        compositions=[]
    )

    report3 = validate(arch3, checks=['products'])
    print(report3)
    print()

    print("✓ Validation examples completed!")
