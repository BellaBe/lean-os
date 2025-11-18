---
name: code-generator
description: Generate production-ready code from categorical specifications. Use when translating ADT specifications to Python/TypeScript. Generates services, types, composition functions, and tests. Follows onion architecture and best practices.
---

# Code Generator

You are an expert in generating production-ready code from categorical specifications. Your role is to translate mathematical structures into clean, type-safe implementations.

## Purpose

Generate production code from ADTs, functors, natural transformations, and category specifications. Output follows architectural best practices with complete type safety and tests.

## Available Resources

- `scripts/generate.py` - Code generation engine with template support
- `templates/` - Jinja2 templates for types, functors, and transformations
- `examples/` - Real-world code generation examples

## Generation Targets

### 1. ADT → Types

```python
# Input: Auth × (Shopify + WooCommerce)
# Output:
from typing import Union, Tuple
from dataclasses import dataclass

@dataclass
class Shopify:
    store_url: str
    api_key: str

@dataclass
class WooCommerce:
    site_url: str
    consumer_key: str
    consumer_secret: str

Platform = Union[Shopify, WooCommerce]

@dataclass
class AuthenticatedPlatform:
    auth: Auth
    platform: Platform
```

### 2. Functor → Service

```python
# Input: Reader functor for multi-tenant
# Output:
from typing import Generic, TypeVar, Callable

A = TypeVar('A')
B = TypeVar('B')

class TenantService(Generic[A]):
    """Multi-tenant service using Reader functor"""

    def __init__(self, f: Callable[[TenantConfig], A]):
        self._f = f

    def fmap(self, g: Callable[[A], B]) -> 'TenantService[B]':
        """Map function over service result"""
        return TenantService(lambda config: g(self._f(config)))

    def run(self, config: TenantConfig) -> A:
        """Execute service with tenant configuration"""
        return self._f(config)
```

### 3. Natural Transformation → Migration

```python
# Input: Maybe → List transformation
# Output:
from typing import Optional, List, TypeVar

A = TypeVar('A')

def migrate_optional_to_list(opt: Optional[A]) -> List[A]:
    """
    Natural transformation: Maybe ⇒ List

    Migrates optional feature to replicated deployment.
    Naturality: list.fmap(f) ∘ maybe_to_list = maybe_to_list ∘ maybe.fmap(f)
    """
    return [opt] if opt is not None else []
```

### 4. Composition → Pipeline

```python
# Input: ServiceA: Request → User, ServiceB: User → Profile
# Output:
def compose_services(
    service_a: Callable[[Request], User],
    service_b: Callable[[User], Profile]
) -> Callable[[Request], Profile]:
    """
    Compose services: ServiceB ∘ ServiceA

    Category law: Associative, has identity
    """
    def composed(request: Request) -> Profile:
        user = service_a(request)
        return service_b(user)
    return composed
```

## Code Generation Process

### Step 1: Parse Specification

```python
from scripts.generate import parse_spec

spec = parse_spec("specs/ecommerce-service.yaml")
# Extracts ADTs, functors, transformations
```

### Step 2: Generate Code

```python
from scripts.generate import generate_code

code = generate_code(
    spec,
    target_language='python',
    architecture='onion',
    include_tests=True
)
```

### Step 3: Write Files

```python
code.write_to_directory("generated/")
# Outputs:
# - types.py (ADT types)
# - services.py (service implementations)
# - functors.py (functor classes)
# - transformations.py (natural transformations)
# - tests/ (property-based tests)
```

## Architecture Patterns

### Onion Architecture

```
generated/
├── domain/
│   └── types.py          # ADT types (core)
├── application/
│   ├── services.py       # Business logic
│   └── functors.py       # Functor patterns
├── infrastructure/
│   ├── repositories.py   # Data access
│   └── api.py           # External APIs
└── tests/
    └── property_tests.py # Functor law tests
```

### Hexagonal Architecture

```
generated/
├── core/
│   ├── domain.py        # ADTs
│   └── ports.py         # Interfaces
├── adapters/
│   ├── inbound/
│   │   └── api.py       # REST endpoints
│   └── outbound/
│       └── database.py  # Persistence
└── tests/
```

## Templates

Templates use Jinja2 for consistent generation:

### Type Template (`templates/types.py.jinja`)

```jinja
from typing import Union
from dataclasses import dataclass

{% for adt in spec.adts %}
{% if adt.type == 'coproduct' %}
{%- for variant in adt.variants %}
@dataclass
class {{ variant.name }}:
    {% for field in variant.fields -%}
    {{ field.name }}: {{ field.type }}
    {% endfor %}
{% endfor %}
{{ adt.name }} = Union[{{ adt.variants | map(attribute='name') | join(', ') }}]
{% elif adt.type == 'product' %}
@dataclass
class {{ adt.name }}:
    {% for field in adt.fields -%}
    {{ field.name }}: {{ field.type }}
    {% endfor %}
{% endif %}
{% endfor %}
```

### Functor Template (`templates/functor.py.jinja`)

```jinja
from typing import Generic, TypeVar, Callable

A = TypeVar('A')
B = TypeVar('B')

class {{ functor.name }}(Generic[{% if functor.params %}{{ functor.params | join(', ') }}{% endif %}]):
    """{{ functor.description }}"""

    def __init__(self, {{ functor.init_params }}):
        {% for param in functor.init_params -%}
        self._{{ param }} = {{ param }}
        {% endfor %}

    def fmap(self, f: Callable[[A], B]) -> '{{ functor.name }}[B]':
        """{{ functor.fmap_doc }}"""
        {{ functor.fmap_impl | indent(8) }}
```

### Test Template (`templates/tests.py.jinja`)

```jinja
import pytest
from hypothesis import given, strategies as st

{% for functor in functors %}
def test_{{ functor.name }}_identity_law():
    """Verify F(id) = id for {{ functor.name }}"""
    def identity(x):
        return x

    @given(st.integers())
    def check(value):
        f = {{ functor.name }}.pure(value)
        assert f.fmap(identity) == identity(f)

    check()

def test_{{ functor.name }}_composition_law():
    """Verify F(g ∘ f) = F(g) ∘ F(f) for {{ functor.name }}"""
    def f(x): return x + 1
    def g(x): return x * 2

    @given(st.integers())
    def check(value):
        functor = {{ functor.name }}.pure(value)
        composed = lambda x: g(f(x))
        assert functor.fmap(composed) == functor.fmap(f).fmap(g)

    check()
{% endfor %}
```

## Best Practices

### 1. Type Safety

```python
# Generate strict types
@dataclass(frozen=True)  # Immutable
class User:
    id: UUID  # Not str - use proper types
    email: EmailStr  # Validated email
    created_at: datetime  # Not timestamp
```

### 2. Error Handling

```python
# Generate Either types for errors
from typing import Union

@dataclass
class Success(Generic[A]):
    value: A

@dataclass
class Error:
    message: str
    code: ErrorCode

Result = Union[Success[A], Error]
```

### 3. Documentation

```python
# Auto-generate docstrings
def get_user_profile(user_id: UUID) -> TenantService[Profile]:
    """
    Get user profile for tenant.

    Functor: Reader (multi-tenant)
    Source: User service specification

    Args:
        user_id: Unique user identifier

    Returns:
        TenantService that produces Profile when run with TenantConfig

    Category: User → Profile
    """
    ...
```

### 4. Property Tests

```python
# Generate tests from laws
@given(st.from_type(Request))
def test_composition_associativity(request: Request):
    """Verify (h ∘ g) ∘ f = h ∘ (g ∘ f)"""
    path1 = compose(compose(h, g), f)(request)
    path2 = compose(h, compose(g, f))(request)
    assert path1 == path2
```

## Integration

### With adt-analyzer

```python
from adt_analyzer import parse_to_adt
from code_generator import generate_types

adt = parse_to_adt("Service with auth and platform")
types_code = generate_types(adt, language='python')
```

### With functor-generator

```python
from functor_generator import generate_functor, FunctorType
from code_generator import generate_functor_code

functor = generate_functor(FunctorType.READER, base_service, config_type)
code = generate_functor_code(functor)
```

### With natural-transformation-engine

```python
from natural_transformations import maybe_to_list
from code_generator import generate_transformation

code = generate_transformation(maybe_to_list, 'python')
```

## When to Use

✓ **Use code generator when:**
- Translating specifications to implementation
- Need consistent, tested code
- Want type-safe implementations
- Generating microservices from ADTs
- Creating transformation pipelines

✗ **Don't use when:**
- Custom business logic required (generate skeleton, fill manually)
- Non-standard architectures
- Performance-critical custom implementations

## Output Example

From specification:
```yaml
service: EcommerceService
adt: Auth × (Shopify + WooCommerce)
functor: Reader
transformation: Maybe → List
```

Generates:
```
generated/
├── domain/
│   └── types.py              # Auth, Shopify, WooCommerce types
├── application/
│   ├── ecommerce_service.py  # Reader-based service
│   └── migrations.py         # Maybe → List transformation
└── tests/
    ├── test_types.py         # Type validation
    ├── test_functors.py      # Functor law tests
    └── test_integration.py   # End-to-end tests
```

## Summary

Code generator translates categorical specifications into production-ready, type-safe code with complete test coverage. Follows architectural best practices and generates from ADTs, functors, natural transformations, and compositions.
