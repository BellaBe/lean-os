---
name: entity-generator
description: |
  Generate domain entities and value objects from primitives maps. Creates Python
  dataclasses with proper type hints, validation, and domain invariants. Foundation
  for all other generated code.
  Input: maps/primitives/*.map.yaml, specifications/v{X}/requirements.adt
  Output: generated/python/src/{project}/domain/entities/*.py
---

# Entity Generator

Generate domain entities from type maps.

## Purpose

Transform primitive and composite type maps into domain entities:
1. Generate entity classes from product types
2. Generate enums from simple coproducts
3. Generate discriminated unions from complex coproducts
4. Generate identifier newtypes
5. Generate value objects with validation

## Input

- `maps/primitives/types.map.yaml` - Type mappings
- `maps/primitives/identifiers.map.yaml` - Identifier mappings
- `specifications/v{X}/requirements.adt` - Original ADT definitions

## Output

```
generated/python/src/{project}/domain/
├── __init__.py
├── entities/
│   ├── __init__.py
│   ├── merchant.py
│   ├── profile.py
│   └── analysis.py
├── value_objects/
│   ├── __init__.py
│   ├── identifiers.py
│   ├── money.py
│   └── email.py
└── events/
    └── __init__.py
```

## Generation Rules

### Product Types → Dataclasses

```yaml
# From types.map.yaml
product:
  Merchant:
    fields:
      - name: id
        type: MerchantId
      - name: shop_domain
        type: ShopDomain
      - name: subscription_tier
        type: SubscriptionTier
      - name: settings
        type: MerchantSettings
      - name: created_at
        type: DateTime
      - name: updated_at
        type: DateTime
```

Generated Python:

```python
# generated/python/src/{project}/domain/entities/merchant.py

from __future__ import annotations
from dataclasses import dataclass, field
from datetime import datetime
from typing import Optional

from ..value_objects.identifiers import MerchantId
from ..value_objects.shop import ShopDomain
from .subscription import SubscriptionTier
from .settings import MerchantSettings


@dataclass(frozen=True, slots=True)
class Merchant:
    """
    Merchant entity.
    
    Categorical interpretation:
    - Object in Domain category
    - Product type: MerchantId × ShopDomain × SubscriptionTier × ...
    
    Invariants:
    - id is immutable after creation
    - shop_domain is unique across merchants
    - updated_at >= created_at
    """
    
    id: MerchantId
    shop_domain: ShopDomain
    subscription_tier: SubscriptionTier
    settings: MerchantSettings
    created_at: datetime
    updated_at: datetime
    
    def __post_init__(self) -> None:
        """Validate domain invariants."""
        if self.updated_at < self.created_at:
            raise ValueError("updated_at cannot be before created_at")
    
    def with_updated(self, **changes) -> Merchant:
        """Create new Merchant with updated fields (immutable update)."""
        from dataclasses import replace
        return replace(self, updated_at=datetime.utcnow(), **changes)
```

### Simple Coproducts → Enums

```yaml
# From types.map.yaml
coproduct:
  SubscriptionTier:
    type: enum
    variants:
      - Free
      - Pro
      - Enterprise
```

Generated Python:

```python
# generated/python/src/{project}/domain/entities/subscription.py

from enum import Enum, auto


class SubscriptionTier(str, Enum):
    """
    Subscription tier enumeration.
    
    Categorical interpretation:
    - Coproduct: Free + Pro + Enterprise
    - Each variant is an injection into the sum type
    """
    
    FREE = "free"
    PRO = "pro"
    ENTERPRISE = "enterprise"
    
    @property
    def is_paid(self) -> bool:
        """Check if tier is a paid tier."""
        return self in (SubscriptionTier.PRO, SubscriptionTier.ENTERPRISE)
    
    @property
    def analysis_limit(self) -> int:
        """Get monthly analysis limit for tier."""
        limits = {
            SubscriptionTier.FREE: 10,
            SubscriptionTier.PRO: 100,
            SubscriptionTier.ENTERPRISE: 1000,
        }
        return limits[self]
```

### Complex Coproducts → Discriminated Unions

```yaml
# From types.map.yaml
coproduct:
  Result:
    type: discriminated_union
    type_params: [E, A]
    variants:
      - name: Success
        fields:
          - name: value
            type: A
      - name: Failure
        fields:
          - name: error
            type: E
```

Generated Python:

```python
# generated/python/src/{project}/domain/value_objects/result.py

from __future__ import annotations
from dataclasses import dataclass
from typing import TypeVar, Generic, Union, Callable

E = TypeVar("E")
A = TypeVar("A")
B = TypeVar("B")


@dataclass(frozen=True, slots=True)
class Success(Generic[A]):
    """Success case of Result."""
    value: A


@dataclass(frozen=True, slots=True)  
class Failure(Generic[E]):
    """Failure case of Result."""
    error: E


# Type alias for the discriminated union
Result = Union[Success[A], Failure[E]]


def is_success(result: Result[E, A]) -> bool:
    """Check if result is Success."""
    return isinstance(result, Success)


def is_failure(result: Result[E, A]) -> bool:
    """Check if result is Failure."""
    return isinstance(result, Failure)


def map_result(result: Result[E, A], f: Callable[[A], B]) -> Result[E, B]:
    """
    Map over success value.
    
    Categorical: Functor map for Result
    """
    match result:
        case Success(value):
            return Success(f(value))
        case Failure(error):
            return Failure(error)


def bind_result(result: Result[E, A], f: Callable[[A], Result[E, B]]) -> Result[E, B]:
    """
    Bind/flatMap for Result.
    
    Categorical: Kleisli composition
    Certificate: monad.cert.yaml#either_associativity
    """
    match result:
        case Success(value):
            return f(value)
        case Failure(error):
            return Failure(error)
```

### Identifiers → NewTypes

```yaml
# From identifiers.map.yaml
identifiers:
  MerchantId:
    base: UUID
    validation: uuid4
    
  ProfileId:
    base: UUID
    validation: uuid4
    
  AnalysisId:
    base: UUID
    validation: uuid4
```

Generated Python:

```python
# generated/python/src/{project}/domain/value_objects/identifiers.py

from __future__ import annotations
from typing import NewType
from uuid import UUID, uuid4


# Type-safe identifiers using NewType
# These are distinct types at type-check time
MerchantId = NewType("MerchantId", UUID)
ProfileId = NewType("ProfileId", UUID)
AnalysisId = NewType("AnalysisId", UUID)


def new_merchant_id() -> MerchantId:
    """Generate a new MerchantId."""
    return MerchantId(uuid4())


def new_profile_id() -> ProfileId:
    """Generate a new ProfileId."""
    return ProfileId(uuid4())


def new_analysis_id() -> AnalysisId:
    """Generate a new AnalysisId."""
    return AnalysisId(uuid4())


def merchant_id_from_str(s: str) -> MerchantId:
    """Parse MerchantId from string."""
    return MerchantId(UUID(s))


def profile_id_from_str(s: str) -> ProfileId:
    """Parse ProfileId from string."""
    return ProfileId(UUID(s))


def analysis_id_from_str(s: str) -> AnalysisId:
    """Parse AnalysisId from string."""
    return AnalysisId(UUID(s))
```

### Validated Value Objects

```yaml
# From types.map.yaml
domain_primitives:
  Email:
    base: String
    validation: email_pattern
    
  ShopDomain:
    base: String
    validation: shopify_domain_pattern
```

Generated Python:

```python
# generated/python/src/{project}/domain/value_objects/email.py

from __future__ import annotations
from dataclasses import dataclass
import re
from typing import ClassVar

from .result import Result, Success, Failure


@dataclass(frozen=True, slots=True)
class Email:
    """
    Validated email value object.
    
    Categorical interpretation:
    - Domain primitive with construction that may fail
    - Email = String { valid_email }
    """
    
    value: str
    
    EMAIL_PATTERN: ClassVar[re.Pattern] = re.compile(
        r"^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$"
    )
    
    def __post_init__(self) -> None:
        """Validate email format."""
        if not self.EMAIL_PATTERN.match(self.value):
            raise ValueError(f"Invalid email format: {self.value}")
    
    @classmethod
    def create(cls, value: str) -> Result[str, Email]:
        """
        Smart constructor - returns Result instead of raising.
        
        Categorical: Partial function lifted to total function via Either
        """
        try:
            return Success(cls(value))
        except ValueError as e:
            return Failure(str(e))
    
    def __str__(self) -> str:
        return self.value
```

## Template Structure

```python
# Base template for entities

from __future__ import annotations
from dataclasses import dataclass, field
from datetime import datetime
from typing import Optional, List
{% for import in imports %}
from {{ import.module }} import {{ import.names | join(", ") }}
{% endfor %}


@dataclass(frozen={{ frozen }}, slots=True)
class {{ entity_name }}:
    """
    {{ description }}
    
    Categorical interpretation:
    - Object in Domain category
    - {{ categorical_type }}
    
    {% if invariants %}
    Invariants:
    {% for inv in invariants %}
    - {{ inv }}
    {% endfor %}
    {% endif %}
    """
    
    {% for field in fields %}
    {{ field.name }}: {{ field.type }}{% if field.default %} = {{ field.default }}{% endif %}
    {% endfor %}
    
    {% if has_validation %}
    def __post_init__(self) -> None:
        """Validate domain invariants."""
        {% for validation in validations %}
        {{ validation }}
        {% endfor %}
    {% endif %}
    
    {% for method in methods %}
    {{ method }}
    {% endfor %}
```

## Generation Process

```yaml
process:
  steps:
    - name: load_type_maps
      action: "Parse types.map.yaml and identifiers.map.yaml"
      
    - name: resolve_dependencies
      action: "Build dependency graph between types"
      
    - name: topological_sort
      action: "Order types by dependency"
      
    - name: generate_identifiers
      action: "Generate identifier newtypes first"
      
    - name: generate_value_objects
      action: "Generate validated value objects"
      
    - name: generate_enums
      action: "Generate enum types"
      
    - name: generate_entities
      action: "Generate entity dataclasses"
      
    - name: generate_init_files
      action: "Create __init__.py with exports"
      
    - name: validate_syntax
      action: "Verify generated Python is valid"
```

## Validation Checks

```yaml
validation:
  syntax_valid:
    command: "python -m py_compile {file}"
    
  imports_resolve:
    check: "All type references resolve"
    
  no_circular_imports:
    check: "No circular import dependencies"
    
  types_valid:
    command: "mypy {file}"
    
  invariants_enforced:
    check: "All ADT constraints have validation"
```

## Next Skills

Output feeds into:
- `dto-generator`
- `repository-generator`
- `service-generator`
