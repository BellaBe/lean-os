---
name: gen-types
description: |
  Generate type definitions from build artifacts. Creates effects module FIRST
  (Result, App monad, errors), then domain types, API schemas, storage models.
  Outputs ACTUAL source files. Use when: generating types, creating models.
---

# Gen Types

Generate type definition files from categorical objects.

## CRITICAL RULES

### Rule 1: Generate ACTUAL FILES

```python
# WRONG - code in YAML
types_manifest:
  files:
    - path: "src/domain/user.py"
      content: "class User: ..."  # NO!

# RIGHT - actual file
create_file("gen/python/src/domain/user.py", code)
```

### Rule 2: Effects Module FIRST

The effects module is the FOUNDATION. Without it, morphisms cannot have correct signatures.

```
MANDATORY GENERATION ORDER:
1. src/domain/effects/         ← FIRST (Result, App, Errors)
2. src/domain/types/           ← SECOND (domain types)
3. src/api/schemas/            ← THIRD (if api enabled)
4. src/storage/models/         ← FOURTH (if persistence enabled)
5. src/storage/repositories/   ← FIFTH (repository interfaces)
```

### Rule 3: Validate Effects Exist

Before completing, MUST verify:
```bash
ls gen/python/src/domain/effects/__init__.py
ls gen/python/src/domain/effects/result.py
ls gen/python/src/domain/effects/app.py
ls gen/python/src/domain/effects/errors/__init__.py
```

If ANY missing → gen-types FAILED.

## Input

- `artifacts/v{N}/build/category.yaml`
- `artifacts/v{N}/build/effects.yaml` ← **REQUIRED**
- `artifacts/v{N}/build/functors.yaml`
- `artifacts/v{N}/targets.yaml`

## Output

- ACTUAL SOURCE FILES in `artifacts/v{N}/gen/{language}/src/`
- `artifacts/v{N}/gen/types-manifest.yaml`

## Generated Structure

```
gen/python/src/
├── __init__.py
├── domain/
│   ├── __init__.py
│   ├── effects/                    ← GENERATED FIRST
│   │   ├── __init__.py
│   │   ├── result.py               # Either/Result type
│   │   ├── app.py                  # App monad
│   │   └── errors/
│   │       ├── __init__.py         # AppError union
│   │       ├── base.py             # Base error classes
│   │       ├── auth.py             # AuthError variants
│   │       ├── user.py             # UserError variants
│   │       └── {module}.py         # Per-module errors
│   ├── types/
│   │   ├── __init__.py
│   │   ├── ids.py                  # UserId, OrderId (NewTypes)
│   │   ├── user.py                 # User, UserStatus
│   │   └── value_objects.py        # Email, Money
│   └── interfaces/                 ← Repository interfaces
│       ├── __init__.py
│       └── repositories.py         # Abstract repository protocols
├── api/                            # If F_api enabled
│   └── schemas/
│       ├── requests.py
│       └── responses.py
└── storage/                        # If F_persist enabled
    ├── models/
    │   └── user_model.py
    └── repositories/
        └── user_repository.py      # Concrete implementation
```

## Step 1: Generate Effects Module

### result.py - The Either Type

```python
# src/domain/effects/result.py
"""
Result type: Either[E, A] for typed error handling.

This is the FOUNDATION of categorical error handling.
All effectful operations return Result[E, A] instead of raising exceptions.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import TypeVar, Generic, Callable, Union, NoReturn

E = TypeVar("E")  # Error type
A = TypeVar("A")  # Success type
B = TypeVar("B")


@dataclass(frozen=True)
class Ok(Generic[A]):
    """Success case of Result."""
    value: A
    
    def is_ok(self) -> bool:
        return True
    
    def is_err(self) -> bool:
        return False


@dataclass(frozen=True)
class Err(Generic[E]):
    """Error case of Result."""
    error: E
    
    def is_ok(self) -> bool:
        return False
    
    def is_err(self) -> bool:
        return True


Result = Union[Ok[A], Err[E]]


def ok(value: A) -> Result[E, A]:
    """Construct success result."""
    return Ok(value)


def err(error: E) -> Result[E, A]:
    """Construct error result."""
    return Err(error)


def map_result(f: Callable[[A], B], result: Result[E, A]) -> Result[E, B]:
    """Apply function to success value (Functor map)."""
    match result:
        case Ok(value):
            return Ok(f(value))
        case Err(error):
            return Err(error)


def flat_map(f: Callable[[A], Result[E, B]], result: Result[E, A]) -> Result[E, B]:
    """Chain computations (Monad bind)."""
    match result:
        case Ok(value):
            return f(value)
        case Err(error):
            return Err(error)


def map_error(f: Callable[[E], E2], result: Result[E, A]) -> Result[E2, A]:
    """Transform error type."""
    match result:
        case Ok(value):
            return Ok(value)
        case Err(error):
            return Err(f(error))


def unwrap_or(default: A, result: Result[E, A]) -> A:
    """Get value or default."""
    match result:
        case Ok(value):
            return value
        case Err(_):
            return default


def unwrap(result: Result[E, A]) -> A:
    """Get value or raise. Use sparingly at boundaries."""
    match result:
        case Ok(value):
            return value
        case Err(error):
            raise ValueError(f"Called unwrap on Err: {error}")
```

### app.py - The App Monad

```python
# src/domain/effects/app.py
"""
App monad: Reader[Env, IO[Result[AppError, A]]]

This is the primary effect type for all domain operations.
Combines:
- Reader: Access to environment/dependencies
- IO: Side effects (async)
- Result: Typed error handling
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import TypeVar, Generic, Callable, Awaitable, TYPE_CHECKING

from .result import Result, Ok, Err, ok, err

if TYPE_CHECKING:
    from .errors import AppError
    from ..interfaces.repositories import Repositories

A = TypeVar("A")
B = TypeVar("B")


@dataclass
class Env:
    """
    Application environment.
    
    Injected at the edge (API handlers, CLI, tests).
    Contains all dependencies needed by domain operations.
    """
    repositories: "Repositories"
    config: "AppConfig"
    # Add other dependencies as needed


class App(Generic[A]):
    """
    App[A] = Env -> IO[Result[AppError, A]]
    
    The core effect monad. All domain operations return App[A].
    
    Usage:
        async def create_user(input: CreateUserInput) -> App[User]:
            return App(lambda env: _create_user_impl(env, input))
    """
    
    def __init__(
        self, 
        run: Callable[[Env], Awaitable[Result["AppError", A]]]
    ) -> None:
        self._run = run
    
    async def run(self, env: Env) -> Result["AppError", A]:
        """Execute the computation with environment."""
        return await self._run(env)
    
    # === Monad operations ===
    
    @classmethod
    def pure(cls, value: A) -> App[A]:
        """Lift pure value into App (return/unit)."""
        async def _run(env: Env) -> Result["AppError", A]:
            return ok(value)
        return cls(_run)
    
    @classmethod
    def fail(cls, error: "AppError") -> App[A]:
        """Create failed App."""
        async def _run(env: Env) -> Result["AppError", A]:
            return err(error)
        return cls(_run)
    
    def map(self, f: Callable[[A], B]) -> App[B]:
        """Apply function to success value (Functor)."""
        async def _run(env: Env) -> Result["AppError", B]:
            result = await self._run(env)
            match result:
                case Ok(value):
                    return ok(f(value))
                case Err(error):
                    return err(error)
        return App(_run)
    
    def flat_map(self, f: Callable[[A], App[B]]) -> App[B]:
        """Chain computations (Monad bind / >>=)."""
        async def _run(env: Env) -> Result["AppError", B]:
            result = await self._run(env)
            match result:
                case Ok(value):
                    return await f(value).run(env)
                case Err(error):
                    return err(error)
        return App(_run)
    
    def recover(
        self, 
        handler: Callable[["AppError"], App[A]]
    ) -> App[A]:
        """Handle errors (catch)."""
        async def _run(env: Env) -> Result["AppError", A]:
            result = await self._run(env)
            match result:
                case Ok(value):
                    return ok(value)
                case Err(error):
                    return await handler(error).run(env)
        return App(_run)
    
    # === Convenience ===
    
    def __rshift__(self, f: Callable[[A], App[B]]) -> App[B]:
        """Operator for flat_map: app >> f"""
        return self.flat_map(f)
    
    @classmethod
    def from_result(cls, result: Result["AppError", A]) -> App[A]:
        """Lift Result into App."""
        async def _run(env: Env) -> Result["AppError", A]:
            return result
        return cls(_run)
    
    @classmethod
    def from_io(
        cls, 
        io: Callable[[Env], Awaitable[A]]
    ) -> App[A]:
        """Lift IO operation into App (may raise)."""
        async def _run(env: Env) -> Result["AppError", A]:
            try:
                value = await io(env)
                return ok(value)
            except Exception as e:
                from .errors import InfraError
                return err(InfraError(str(e)))
        return cls(_run)


# === Kleisli composition ===

def kleisli_compose(
    f: Callable[[A], App[B]],
    g: Callable[[B], App[C]]
) -> Callable[[A], App[C]]:
    """
    Kleisli composition: f >=> g
    
    Compose two effectful functions.
    """
    def composed(a: A) -> App[C]:
        return f(a).flat_map(g)
    return composed


# Type alias for Kleisli arrows
KleisliArrow = Callable[[A], App[B]]
```

### errors/base.py - Base Error Types

```python
# src/domain/effects/errors/base.py
"""
Base error types.

All domain errors inherit from these bases.
"""
from dataclasses import dataclass
from typing import Optional


@dataclass(frozen=True)
class DomainError:
    """Base for all domain/business logic errors."""
    message: str
    code: str
    
    @property
    def http_status(self) -> int:
        return 400  # Default, override in subclasses


@dataclass(frozen=True)
class ValidationError(DomainError):
    """Input validation failed."""
    field: Optional[str] = None
    
    @property
    def http_status(self) -> int:
        return 400


@dataclass(frozen=True)
class NotFoundError(DomainError):
    """Entity not found."""
    entity_type: str
    entity_id: str
    
    @property
    def http_status(self) -> int:
        return 404


@dataclass(frozen=True)
class ConflictError(DomainError):
    """Conflict with existing state."""
    
    @property
    def http_status(self) -> int:
        return 409


@dataclass(frozen=True)
class AuthorizationError(DomainError):
    """Not authorized for operation."""
    required_permission: Optional[str] = None
    
    @property
    def http_status(self) -> int:
        return 403


@dataclass(frozen=True)
class InfraError(DomainError):
    """Infrastructure failure."""
    
    @property
    def http_status(self) -> int:
        return 503
```

### errors/{module}.py - Per-Module Errors

Generate from build/effects.yaml error_types:

```python
# src/domain/effects/errors/auth.py
"""Auth module errors. Generated from build/effects.yaml."""
from dataclasses import dataclass
from typing import Union, Optional
from datetime import datetime

from .base import DomainError


@dataclass(frozen=True)
class InvalidCredentials(DomainError):
    """Email or password incorrect."""
    message: str = "Invalid email or password"
    code: str = "auth/invalid_credentials"
    
    @property
    def http_status(self) -> int:
        return 401


@dataclass(frozen=True)
class AccountLocked(DomainError):
    """Too many failed login attempts."""
    locked_until: datetime
    message: str = "Account locked"
    code: str = "auth/account_locked"
    
    @property
    def http_status(self) -> int:
        return 403


@dataclass(frozen=True)
class TokenExpired(DomainError):
    """Access or refresh token expired."""
    message: str = "Session expired"
    code: str = "auth/token_expired"
    
    @property
    def http_status(self) -> int:
        return 401


# ... all variants from build/effects.yaml ...


# Union type for all auth errors
AuthError = Union[
    InvalidCredentials,
    AccountLocked,
    TokenExpired,
    # ... all variants
]
```

### errors/__init__.py - AppError Union

```python
# src/domain/effects/errors/__init__.py
"""
Application error types.

AppError is the union of all possible errors.
"""
from typing import Union

from .base import (
    DomainError,
    ValidationError,
    NotFoundError,
    ConflictError,
    AuthorizationError,
    InfraError,
)
from .auth import AuthError
from .user import UserError
from .org import OrgError
# ... import all module errors ...


# The complete error union
AppError = Union[
    ValidationError,
    AuthError,
    UserError,
    OrgError,
    # ... all error types from build/effects.yaml ...
    InfraError,
]


__all__ = [
    "AppError",
    "DomainError",
    "ValidationError",
    "NotFoundError",
    "ConflictError",
    "AuthorizationError",
    "InfraError",
    "AuthError",
    "UserError",
    "OrgError",
    # ... all exports
]
```

## Step 2: Generate Repository Interfaces

```python
# src/domain/interfaces/repositories.py
"""
Repository interfaces (protocols).

These are the abstract interfaces that domain operations depend on.
Concrete implementations are in src/storage/repositories/.
"""
from abc import ABC, abstractmethod
from typing import Optional, Protocol, TYPE_CHECKING

if TYPE_CHECKING:
    from ..types.user import User, UserId
    from ..types.ids import *
    from ..effects.result import Result
    from ..effects.errors import AppError


class UserRepository(Protocol):
    """Repository for User aggregate."""
    
    async def get_by_id(self, user_id: "UserId") -> Optional["User"]:
        """Find user by ID. Returns None if not found."""
        ...
    
    async def get_by_email(self, email: str) -> Optional["User"]:
        """Find user by email. Returns None if not found."""
        ...
    
    async def save(self, user: "User") -> "User":
        """Persist user (insert or update)."""
        ...
    
    async def delete(self, user_id: "UserId") -> bool:
        """Delete user. Returns True if deleted."""
        ...


# ... other repository protocols ...


@dataclass
class Repositories:
    """Container for all repositories. Injected via Env."""
    users: UserRepository
    # ... other repositories
```

## Step 3: Generate Domain Types

Generate from build/category.yaml objects:

```python
# src/domain/types/ids.py
"""Identifier types (NewTypes for type safety)."""
from typing import NewType
from uuid import UUID

UserId = NewType("UserId", UUID)
OrgId = NewType("OrgId", UUID)
# ... from build/category.yaml ...
```

```python
# src/domain/types/user.py
"""User aggregate and related types."""
from dataclasses import dataclass
from datetime import datetime
from enum import Enum
from typing import Optional

from .ids import UserId, OrgId


class UserStatus(Enum):
    """User account status."""
    PENDING = "pending"
    ACTIVE = "active"
    SUSPENDED = "suspended"


@dataclass(frozen=True)
class User:
    """
    User aggregate root.
    
    Immutable - changes create new instances.
    """
    id: UserId
    org_id: OrgId
    email: str
    status: UserStatus
    created_at: datetime
    
    # ... from build/category.yaml ...
```

## Step 4: Generate API Schemas (if enabled)

Only if targets.api.enabled:

```python
# src/api/schemas/responses.py
from pydantic import BaseModel
from ..domain.types.user import User


class UserResponse(BaseModel):
    """API response - maps from domain User."""
    id: str
    email: str
    status: str
    
    @classmethod
    def from_domain(cls, user: User) -> "UserResponse":
        return cls(
            id=str(user.id),
            email=user.email,
            status=user.status.value,
        )
```

## Step 5: Generate Storage (if enabled)

Only if targets.persistence.enabled:

```python
# src/storage/repositories/user_repository.py
"""Concrete UserRepository implementation."""
from typing import Optional
from sqlalchemy.ext.asyncio import AsyncSession

from ...domain.types.user import User, UserId
from ...domain.interfaces.repositories import UserRepository
from ..models.user_model import UserModel


class SqlUserRepository(UserRepository):
    """SQLAlchemy implementation of UserRepository."""
    
    def __init__(self, session: AsyncSession) -> None:
        self._session = session
    
    async def get_by_id(self, user_id: UserId) -> Optional[User]:
        result = await self._session.get(UserModel, user_id)
        return result.to_domain() if result else None
    
    async def save(self, user: User) -> User:
        model = UserModel.from_domain(user)
        self._session.add(model)
        await self._session.flush()
        return model.to_domain()
```

## Validation Checklist

MUST verify before completing:

```bash
# 1. Effects exist (MANDATORY)
test -f gen/python/src/domain/effects/__init__.py || exit 1
test -f gen/python/src/domain/effects/result.py || exit 1
test -f gen/python/src/domain/effects/app.py || exit 1
test -d gen/python/src/domain/effects/errors/ || exit 1

# 2. Imports work
cd gen/python
python -c "from src.domain.effects import App, AppError, Result, ok, err"
python -c "from src.domain.effects.result import Ok, Err, flat_map"
python -c "from src.domain.types import User, UserId"

# 3. Repository interfaces exist
python -c "from src.domain.interfaces.repositories import UserRepository"
```

## types-manifest.yaml

```yaml
version: "1.0"
language: python

# EFFECTS GENERATED FIRST
effects:
  - path: "src/domain/effects/__init__.py"
    exports: ["App", "AppError", "Result", "ok", "err"]
  - path: "src/domain/effects/result.py"
    exports: ["Result", "Ok", "Err", "ok", "err", "flat_map", "map_result"]
  - path: "src/domain/effects/app.py"
    exports: ["App", "Env", "kleisli_compose"]
  - path: "src/domain/effects/errors/__init__.py"
    exports: ["AppError", "DomainError", "ValidationError", "..."]
  - path: "src/domain/effects/errors/base.py"
    exports: ["DomainError", "ValidationError", "NotFoundError", "..."]
  - path: "src/domain/effects/errors/auth.py"
    exports: ["AuthError", "InvalidCredentials", "AccountLocked", "..."]
    traces_to: ["build/effects.yaml#error_types.AuthError"]
  # ... per module ...

# THEN DOMAIN TYPES
types:
  - path: "src/domain/types/ids.py"
    objects: ["UserId", "OrgId", "..."]
    traces_to: ["build/category.yaml#objects"]
  - path: "src/domain/types/user.py"
    objects: ["User", "UserStatus"]
    traces_to: ["build/category.yaml#objects.User"]

# THEN INTERFACES  
interfaces:
  - path: "src/domain/interfaces/repositories.py"
    protocols: ["UserRepository", "OrgRepository", "..."]

# THEN API (if enabled)
api_schemas:
  enabled: true
  files:
    - path: "src/api/schemas/responses.py"
      traces_to: ["build/functors.yaml#F_api"]

# THEN STORAGE (if enabled)
storage:
  enabled: true
  models:
    - path: "src/storage/models/user_model.py"
      traces_to: ["build/functors.yaml#F_persist"]
  repositories:
    - path: "src/storage/repositories/user_repository.py"
      implements: "UserRepository"

validation:
  effects_exist: true
  imports_work: true
  all_objects_generated: true
```

## Library Integration

This skill has prescriptive tooling in `.claude/lib/leanos/`.

### Claude Usage (Direct Python API)

Claude calls library functions directly — no subprocess/CLI needed:

```python
from leanos.codegen import (
    generate_result_py,
    generate_app_py,
    generate_errors_py,
    generate_types_module,
    EffectSpec,
    ErrorVariant,
    TypeSpec,
    FieldSpec,
    TypeKind,
    ModuleSpec,
)

# Generate effects/result.py
result_py = generate_result_py()
write_file("gen/python/src/domain/effects/result.py", result_py)

# Generate effects/app.py
app_py = generate_app_py(error_type="AppError")
write_file("gen/python/src/domain/effects/app.py", app_py)

# Generate effects/errors/__init__.py
spec = EffectSpec(
    module_name="errors",
    error_variants=[
        ErrorVariant(
            name="UserNotFound",
            fields={"user_id": "UserId"},
            message_template="User not found",
        ),
        ErrorVariant(
            name="UserAlreadyExists",
            fields={"email": "str"},
            message_template="User already exists",
        ),
    ],
    base_error_name="AppError",
)
errors_py = generate_errors_py(spec)
write_file("gen/python/src/domain/effects/errors/__init__.py", errors_py)

# Generate domain types
module_spec = ModuleSpec(
    name="user",
    types=[
        TypeSpec(
            name="User",
            kind=TypeKind.DATACLASS,
            fields=[
                FieldSpec(name="id", type="UserId"),
                FieldSpec(name="email", type="str"),
                FieldSpec(name="status", type="UserStatus"),
                FieldSpec(name="created_at", type="datetime"),
            ],
            docstring="User aggregate.",
            frozen=True,
        ),
        TypeSpec(
            name="UserStatus",
            kind=TypeKind.ENUM,
            enum_values=[
                ("PENDING", "pending"),
                ("ACTIVE", "active"),
                ("SUSPENDED", "suspended"),
            ],
            docstring="User account status.",
        ),
    ],
    imports=[(".ids", ["UserId"])],
)
user_py = generate_types_module(module_spec)
write_file("gen/python/src/domain/types/user.py", user_py)
```

### Human/CI Usage (CLI)

The CLI is for humans and CI pipelines, not for Claude:

```bash
# Generate effects module
leanos generate effects build/effects.yaml gen/python/src/domain/effects/

# Generate types
leanos generate types spec/types.yaml gen/python/src/domain/types/

# Validate effects module exists
leanos validate gen/
```

### Benefits of Library

1. **Valid Python by construction** — LibCST builds AST, not strings
2. **Deterministic output** — Same spec → same code
3. **Automated validation** — Library validates its own output
4. **Type safety** — Specs are typed dataclasses

## Do NOT

- **Skip effects** — They are MANDATORY, generated FIRST
- **Put code in YAML** — Create actual .py files
- **Use exceptions for errors** — Use Result[E, A]
- **Return plain types** — Effectful ops return App[A]
- **Couple to storage** — Domain depends on interfaces, not implementations
- **Forget __init__.py** — Required for Python imports
