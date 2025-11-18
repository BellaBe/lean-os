#!/usr/bin/env python3
"""
Code Generator

Generate production-ready code from categorical specifications.
Outputs types, services, functors, and tests.
"""

from dataclasses import dataclass
from typing import List, Dict, Optional
from pathlib import Path
from enum import Enum


# ========== Specification Model ==========

class TargetLanguage(Enum):
    PYTHON = "python"
    TYPESCRIPT = "typescript"


@dataclass
class FieldSpec:
    """Field specification"""
    name: str
    type_name: str


@dataclass
class VariantSpec:
    """ADT variant specification"""
    name: str
    fields: List[FieldSpec]


@dataclass
class ADTSpec:
    """Algebraic Data Type specification"""
    name: str
    is_product: bool  # True for product, False for coproduct
    variants: List[VariantSpec]  # For coproduct
    fields: List[FieldSpec]  # For product


@dataclass
class FunctorSpec:
    """Functor specification"""
    name: str
    functor_type: str  # 'Reader', 'Maybe', 'List', etc.
    description: str


@dataclass
class GeneratedCode:
    """Generated code output"""
    files: Dict[str, str]  # filename -> content

    def write_to_directory(self, directory: Path):
        """Write generated files to directory"""
        directory = Path(directory)
        directory.mkdir(parents=True, exist_ok=True)

        for filename, content in self.files.items():
            filepath = directory / filename
            filepath.parent.mkdir(parents=True, exist_ok=True)
            filepath.write_text(content)


# ========== Code Generators ==========

def generate_python_types(adt: ADTSpec) -> str:
    """
    Generate Python types from ADT specification.

    Args:
        adt: ADT specification

    Returns:
        Python code as string
    """
    lines = [
        "from typing import Union",
        "from dataclasses import dataclass",
        "",
    ]

    if adt.is_product:
        # Product type (single dataclass)
        lines.append("@dataclass")
        lines.append(f"class {adt.name}:")
        if adt.fields:
            for field in adt.fields:
                lines.append(f"    {field.name}: {field.type_name}")
        else:
            lines.append("    pass")
    else:
        # Coproduct type (union of variants)
        variant_names = []
        for variant in adt.variants:
            lines.append("@dataclass")
            lines.append(f"class {variant.name}:")
            if variant.fields:
                for field in variant.fields:
                    lines.append(f"    {field.name}: {field.type_name}")
            else:
                lines.append("    pass")
            lines.append("")
            variant_names.append(variant.name)

        # Union type
        union = " | ".join(variant_names)
        lines.append(f"{adt.name} = Union[{', '.join(variant_names)}]")

    return "\n".join(lines)


def generate_python_functor(functor: FunctorSpec) -> str:
    """
    Generate Python functor implementation.

    Args:
        functor: Functor specification

    Returns:
        Python code as string
    """
    if functor.functor_type == "Reader":
        return """from typing import Generic, TypeVar, Callable

A = TypeVar('A')
B = TypeVar('B')
R = TypeVar('R')  # Config/Environment type

class Reader(Generic[R, A]):
    \"\"\"Reader functor for dependency injection / multi-tenant\"\"\"

    def __init__(self, run: Callable[[R], A]):
        self._run = run

    def fmap(self, f: Callable[[A], B]) -> 'Reader[R, B]':
        \"\"\"Transform result while preserving configuration dependency\"\"\"
        return Reader(lambda config: f(self._run(config)))

    def run(self, config: R) -> A:
        \"\"\"Execute with configuration\"\"\"
        return self._run(config)

    @staticmethod
    def pure(value: A) -> 'Reader[R, A]':
        \"\"\"Lift value into Reader\"\"\"
        return Reader(lambda _: value)
"""

    elif functor.functor_type == "Maybe":
        return """from typing import Generic, TypeVar, Callable, Optional

A = TypeVar('A')
B = TypeVar('B')

class Maybe(Generic[A]):
    \"\"\"Maybe functor for optional values\"\"\"

    def __init__(self, value: Optional[A]):
        self._value = value

    def fmap(self, f: Callable[[A], B]) -> 'Maybe[B]':
        \"\"\"Transform value if present\"\"\"
        if self._value is not None:
            return Maybe(f(self._value))
        return Maybe(None)

    def is_just(self) -> bool:
        return self._value is not None

    def get_or_else(self, default: A) -> A:
        return self._value if self._value is not None else default

    @staticmethod
    def pure(value: A) -> 'Maybe[A]':
        \"\"\"Lift value into Maybe\"\"\"
        return Maybe(value)
"""

    else:
        return f"# Functor type '{functor.functor_type}' not yet implemented\n"


def generate_python_tests(adt: ADTSpec, functor: Optional[FunctorSpec] = None) -> str:
    """
    Generate Python tests.

    Args:
        adt: ADT specification
        functor: Optional functor specification

    Returns:
        Python test code as string
    """
    lines = [
        "import pytest",
        "from hypothesis import given, strategies as st",
        "",
    ]

    # Type tests
    lines.append(f"def test_{adt.name.lower()}_creation():")
    lines.append(f"    \"\"\"Test {adt.name} type creation\"\"\"")
    if adt.is_product and adt.fields:
        # Create instance with sample data
        args = ", ".join(f"{field.name}={_sample_value(field.type_name)}" for field in adt.fields)
        lines.append(f"    instance = {adt.name}({args})")
        lines.append(f"    assert instance is not None")
    else:
        lines.append("    # Add specific tests for your types")
        lines.append("    pass")
    lines.append("")

    # Functor law tests
    if functor:
        lines.append(f"def test_{functor.name.lower()}_identity_law():")
        lines.append(f"    \"\"\"Verify F(id) = id for {functor.name}\"\"\"")
        lines.append("    def identity(x):")
        lines.append("        return x")
        lines.append("")
        lines.append("    @given(st.integers())")
        lines.append("    def check(value):")
        lines.append(f"        f = {functor.name}.pure(value)")
        lines.append("        assert f.fmap(identity).run(None) == identity(f.run(None))")
        lines.append("")
        lines.append("    check()")
        lines.append("")

        lines.append(f"def test_{functor.name.lower()}_composition_law():")
        lines.append(f"    \"\"\"Verify F(g ∘ f) = F(g) ∘ F(f) for {functor.name}\"\"\"")
        lines.append("    def f(x): return x + 1")
        lines.append("    def g(x): return x * 2")
        lines.append("")
        lines.append("    @given(st.integers())")
        lines.append("    def check(value):")
        lines.append(f"        functor = {functor.name}.pure(value)")
        lines.append("        composed = lambda x: g(f(x))")
        lines.append("        # F(g ∘ f)")
        lines.append("        result1 = functor.fmap(composed).run(None)")
        lines.append("        # F(g) ∘ F(f)")
        lines.append("        result2 = functor.fmap(f).fmap(g).run(None)")
        lines.append("        assert result1 == result2")
        lines.append("")
        lines.append("    check()")

    return "\n".join(lines)


def generate_natural_transformation(source: str, target: str) -> str:
    """
    Generate natural transformation code.

    Args:
        source: Source functor name
        target: Target functor name

    Returns:
        Python code as string
    """
    transformation_name = f"{source.lower()}_to_{target.lower()}"

    if source == "Maybe" and target == "List":
        return f"""from typing import Optional, List, TypeVar

A = TypeVar('A')

def {transformation_name}(maybe_value: Optional[A]) -> List[A]:
    \"\"\"
    Natural transformation: Maybe ⇒ List

    Transforms optional value to list (0 or 1 element).
    Naturality: list.fmap(f) ∘ {transformation_name} = {transformation_name} ∘ maybe.fmap(f)
    \"\"\"
    return [maybe_value] if maybe_value is not None else []
"""

    return f"""# Natural transformation {source} ⇒ {target}
# TODO: Implement transformation
"""


# ========== Main Generation ==========

def generate_code(
    adts: List[ADTSpec],
    functors: List[FunctorSpec] = None,
    transformations: List[tuple[str, str]] = None,
    language: TargetLanguage = TargetLanguage.PYTHON
) -> GeneratedCode:
    """
    Generate complete codebase from specifications.

    Args:
        adts: List of ADT specifications
        functors: List of functor specifications
        transformations: List of (source, target) transformation pairs
        language: Target programming language

    Returns:
        GeneratedCode with all files
    """
    functors = functors or []
    transformations = transformations or []

    files = {}

    if language == TargetLanguage.PYTHON:
        # Generate types
        types_code = []
        for adt in adts:
            types_code.append(generate_python_types(adt))
            types_code.append("")

        files["domain/types.py"] = "\n".join(types_code)

        # Generate functors
        if functors:
            functor_code = []
            for functor in functors:
                functor_code.append(generate_python_functor(functor))
                functor_code.append("")

            files["application/functors.py"] = "\n".join(functor_code)

        # Generate transformations
        if transformations:
            transform_code = []
            for source, target in transformations:
                transform_code.append(generate_natural_transformation(source, target))
                transform_code.append("")

            files["application/transformations.py"] = "\n".join(transform_code)

        # Generate tests
        test_code = []
        for adt in adts:
            functor = functors[0] if functors else None
            test_code.append(generate_python_tests(adt, functor))
            test_code.append("")

        files["tests/test_generated.py"] = "\n".join(test_code)

    return GeneratedCode(files=files)


# ========== Helper Functions ==========

def _sample_value(type_name: str) -> str:
    """Generate sample value for type"""
    type_map = {
        "str": '"example"',
        "int": "42",
        "float": "3.14",
        "bool": "True",
        "datetime": "datetime.now()",
        "UUID": "uuid.uuid4()",
    }
    return type_map.get(type_name, "None")


# ========== Examples ==========

if __name__ == '__main__':
    print("=== Code Generator Examples ===\n")

    # Example 1: Generate ADT types
    print("1. Generating types from ADT")
    merchant_state = ADTSpec(
        name="MerchantState",
        is_product=False,
        variants=[
            VariantSpec("Active", [FieldSpec("activated_at", "datetime")]),
            VariantSpec("Deactivated", [FieldSpec("reason", "str")]),
            VariantSpec("Trial", [FieldSpec("credits_remaining", "int")]),
        ],
        fields=[]
    )

    code = generate_code(
        adts=[merchant_state],
        functors=[],
        transformations=[]
    )

    print(code.files["domain/types.py"])
    print()

    # Example 2: Generate Reader functor
    print("2. Generating Reader functor")
    reader_functor = FunctorSpec(
        name="Reader",
        functor_type="Reader",
        description="Multi-tenant service functor"
    )

    code = generate_code(
        adts=[merchant_state],
        functors=[reader_functor],
        transformations=[]
    )

    print(code.files["application/functors.py"][:300] + "...")
    print()

    # Example 3: Generate natural transformation
    print("3. Generating natural transformation")
    code = generate_code(
        adts=[],
        functors=[],
        transformations=[("Maybe", "List")]
    )

    print(code.files["application/transformations.py"])
    print()

    # Example 4: Write to directory
    print("4. Writing generated code")
    output_dir = Path("generated_example")
    code = generate_code(
        adts=[merchant_state],
        functors=[reader_functor],
        transformations=[("Maybe", "List")]
    )
    code.write_to_directory(output_dir)
    print(f"✓ Code written to {output_dir}/")
    print(f"  Files: {list(code.files.keys())}")

    print("\n✓ Code generation examples completed!")
