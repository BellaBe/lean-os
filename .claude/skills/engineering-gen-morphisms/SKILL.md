---
name: gen-morphisms
description: |
  Generate morphism implementations from build artifacts. Creates domain operations
  using App monad, API handlers (via F_api), and compositions. All effectful
  operations return App[A]. Use when: implementing operations, creating endpoints.
---

# Gen Morphisms

Generate morphism implementation files with proper effect handling.

## CRITICAL RULES

### Rule 1: All Effectful Morphisms Return App[A]

```python
# WRONG - plain return type
async def create_user(input: CreateUserInput) -> User:
    ...

# WRONG - raise exceptions
async def create_user(input: CreateUserInput) -> User:
    if error:
        raise UserError(...)  # NO!

# RIGHT - return App[A]
def create_user(input: CreateUserInput) -> App[User]:
    async def _run(env: Env) -> Result[AppError, User]:
        ...
    return App(_run)
```

### Rule 2: Import Effects from gen-types Output

```python
# MUST import from domain/effects
from ..effects import App, Env
from ..effects.result import Result, ok, err
from ..effects.errors import AppError, UserError, UserNotFound
```

### Rule 3: Get Dependencies from Env

```python
# WRONG - dependency as parameter
async def create_user(input: CreateUserInput, repo: UserRepository) -> ...:
    ...

# RIGHT - get from Env
def create_user(input: CreateUserInput) -> App[User]:
    async def _run(env: Env) -> Result[AppError, User]:
        repo = env.repositories.users  # Get from environment
        ...
    return App(_run)
```

### Rule 4: Validate Signatures Against spec/morphisms.yaml

Every generated function must match its spec signature:
- Domain matches
- Codomain matches  
- Effects are handled via App

## Input

- `artifacts/v{N}/build/category.yaml` — Morphisms to implement
- `artifacts/v{N}/build/effects.yaml` — Effect definitions
- `artifacts/v{N}/build/functors.yaml` — API/storage mappings
- `artifacts/v{N}/build/transformations.yaml` — Cross-cutting concerns
- `artifacts/v{N}/gen/types-manifest.yaml` — Generated type locations

## Prerequisites

**gen-types MUST have completed** — effects module must exist:
```bash
test -f gen/python/src/domain/effects/app.py || exit 1
test -f gen/python/src/domain/effects/result.py || exit 1
```

## Output

- ACTUAL SOURCE FILES in `artifacts/v{N}/gen/{language}/src/`
- `artifacts/v{N}/gen/morphisms-manifest.yaml`

## Generated Structure

```
gen/python/src/
├── domain/
│   ├── operations/           # Generator morphisms
│   │   ├── __init__.py
│   │   ├── user_ops.py       # create_user, get_user
│   │   ├── auth_ops.py       # authenticate, refresh_token
│   │   └── pure.py           # Pure transformations
│   └── workflows/            # Derived morphisms (compositions)
│       ├── __init__.py
│       └── registration.py   # register_user = validate >=> create >=> welcome
├── api/                      # F_api functor application
│   ├── handlers/
│   │   ├── __init__.py
│   │   └── user_handlers.py  # Wraps domain ops for HTTP
│   └── routes.py
└── middleware/               # Transformations
    ├── __init__.py
    ├── auth.py
    └── error_handler.py      # AppError → HTTP response
```

## Domain Operations (Generator Morphisms)

These implement atomic operations from build/category.yaml.

### Pattern: Effectful Operation

```python
# src/domain/operations/user_ops.py
"""
User operations.

All operations return App[A] and get dependencies from Env.
"""
from datetime import datetime
from uuid import uuid4

from ..effects import App, Env
from ..effects.result import Result, ok, err
from ..effects.errors import (
    AppError,
    UserNotFound,
    UserAlreadyExists,
)
from ..types import User, UserId, CreateUserInput, UserStatus
from ..types.ids import UserId


def create_user(input: CreateUserInput) -> App[User]:
    """
    Create a new user.
    
    Spec: create_user: CreateUserInput → User
    Effects: [IO, Either[UserError, _]]
    Category: Domain → Domain
    """
    async def _run(env: Env) -> Result[AppError, User]:
        repo = env.repositories.users
        
        # Check email uniqueness
        existing = await repo.get_by_email(input.email)
        if existing is not None:
            return err(UserAlreadyExists(
                message=f"Email {input.email} already registered",
                code="user/email_exists",
            ))
        
        # Create user entity
        user = User(
            id=UserId(uuid4()),
            email=input.email,
            status=UserStatus.PENDING,
            created_at=datetime.utcnow(),
        )
        
        # Persist
        saved = await repo.save(user)
        return ok(saved)
    
    return App(_run)


def get_user(user_id: UserId) -> App[User]:
    """
    Get user by ID.
    
    Spec: get_user: UserId → User
    Effects: [IO, Either[UserError, _]]
    """
    async def _run(env: Env) -> Result[AppError, User]:
        repo = env.repositories.users
        
        user = await repo.get_by_id(user_id)
        if user is None:
            return err(UserNotFound(
                message=f"User {user_id} not found",
                code="user/not_found",
                entity_type="User",
                entity_id=str(user_id),
            ))
        
        return ok(user)
    
    return App(_run)


def update_user_status(user_id: UserId, new_status: UserStatus) -> App[User]:
    """
    Update user status.
    
    Spec: update_user_status: (UserId × UserStatus) → User
    Effects: [IO, Either[UserError, _]]
    """
    async def _run(env: Env) -> Result[AppError, User]:
        repo = env.repositories.users
        
        user = await repo.get_by_id(user_id)
        if user is None:
            return err(UserNotFound(
                message=f"User {user_id} not found",
                code="user/not_found",
                entity_type="User",
                entity_id=str(user_id),
            ))
        
        # Immutable update
        updated = User(
            id=user.id,
            email=user.email,
            status=new_status,
            created_at=user.created_at,
        )
        
        saved = await repo.save(updated)
        return ok(saved)
    
    return App(_run)
```

### Pattern: Pure Operation

Pure operations don't need App, return Result directly:

```python
# src/domain/operations/pure.py
"""
Pure operations (no IO effects).

These return Result directly since they don't need Env.
"""
import re
from ..effects.result import Result, ok, err
from ..effects.errors import ValidationError
from ..types import Email


EMAIL_REGEX = re.compile(r"^[\w.-]+@[\w.-]+\.\w+$")


def validate_email(raw: str) -> Result[ValidationError, Email]:
    """
    Validate and parse email.
    
    Spec: validate_email: String → Email
    Effects: [Either[ValidationError, _]]
    Pure: true
    """
    if not EMAIL_REGEX.match(raw):
        return err(ValidationError(
            message=f"Invalid email format: {raw}",
            code="validation/invalid_format",
            field="email",
        ))
    
    return ok(Email(value=raw))


def validate_password(raw: str) -> Result[ValidationError, str]:
    """
    Validate password strength.
    
    Spec: validate_password: String → String
    Effects: [Either[ValidationError, _]]
    Pure: true
    """
    errors = []
    if len(raw) < 12:
        errors.append("Password must be at least 12 characters")
    if not any(c.isupper() for c in raw):
        errors.append("Password must contain uppercase letter")
    if not any(c.isdigit() for c in raw):
        errors.append("Password must contain digit")
    
    if errors:
        return err(ValidationError(
            message="; ".join(errors),
            code="validation/password_weak",
            field="password",
        ))
    
    return ok(raw)
```

## Derived Operations (Kleisli Composition)

Compositions from build/category.yaml composed_of:

```python
# src/domain/workflows/registration.py
"""
User registration workflow.

Derived morphism composed from generators.
"""
from ..effects import App, kleisli_compose
from ..effects.result import Result, ok, err, flat_map
from ..effects.errors import AppError
from ..operations.user_ops import create_user
from ..operations.pure import validate_email, validate_password
from ..types import User, RegistrationInput


def register_user(input: RegistrationInput) -> App[User]:
    """
    Complete user registration.
    
    Spec: register_user = validate_email >=> validate_password >=> create_user
    Composition: kleisli
    
    This is a derived morphism - composed from generators.
    """
    async def _run(env) -> Result[AppError, User]:
        # Step 1: Validate email (pure)
        email_result = validate_email(input.email)
        if email_result.is_err():
            return email_result
        email = email_result.value
        
        # Step 2: Validate password (pure)
        password_result = validate_password(input.password)
        if password_result.is_err():
            return password_result
        
        # Step 3: Create user (effectful)
        from ..types import CreateUserInput
        create_input = CreateUserInput(
            email=str(email),
            password=password_result.value,
        )
        
        return await create_user(create_input).run(env)
    
    return App(_run)


# Alternative: Using kleisli_compose for cleaner composition
def _validate_and_create() -> App[User]:
    """
    Example of explicit Kleisli composition.
    """
    # Lift pure validation into App
    def validate_step(input: RegistrationInput) -> App[CreateUserInput]:
        async def _run(env) -> Result[AppError, CreateUserInput]:
            email_r = validate_email(input.email)
            if email_r.is_err():
                return email_r
            
            pwd_r = validate_password(input.password)
            if pwd_r.is_err():
                return pwd_r
            
            return ok(CreateUserInput(
                email=str(email_r.value),
                password=pwd_r.value,
            ))
        return App(_run)
    
    # Compose: validate >=> create
    return kleisli_compose(validate_step, create_user)
```

## API Handlers (F_api Functor)

Transform domain operations to HTTP handlers:

```python
# src/api/handlers/user_handlers.py
"""
User API handlers.

F_api maps domain morphisms to HTTP endpoints.
These wrap domain operations and handle HTTP concerns.
"""
from fastapi import APIRouter, Depends, HTTPException
from uuid import UUID

from ...domain.effects import App, Env
from ...domain.effects.result import Ok, Err
from ...domain.operations.user_ops import create_user, get_user
from ...domain.workflows.registration import register_user
from ...domain.types import CreateUserInput, RegistrationInput
from ..schemas.requests import CreateUserRequest, RegisterRequest
from ..schemas.responses import UserResponse
from ..dependencies import get_env


router = APIRouter(prefix="/users", tags=["users"])


@router.post("/", response_model=UserResponse, status_code=201)
async def create_user_handler(
    request: CreateUserRequest,
    env: Env = Depends(get_env),
):
    """
    POST /users → create_user
    
    F_api morphism map:
      create_user: CreateUserInput → App[User]
      ↓
      POST /users: CreateUserRequest → UserResponse | ErrorResponse
    """
    # Map request to domain input
    domain_input = CreateUserInput(
        email=request.email,
        password=request.password,
    )
    
    # Run domain operation
    result = await create_user(domain_input).run(env)
    
    # Map result to response
    match result:
        case Ok(user):
            return UserResponse.from_domain(user)
        case Err(error):
            raise HTTPException(
                status_code=error.http_status,
                detail={"code": error.code, "message": error.message},
            )


@router.get("/{user_id}", response_model=UserResponse)
async def get_user_handler(
    user_id: UUID,
    env: Env = Depends(get_env),
):
    """
    GET /users/{id} → get_user
    """
    from ...domain.types.ids import UserId
    
    result = await get_user(UserId(user_id)).run(env)
    
    match result:
        case Ok(user):
            return UserResponse.from_domain(user)
        case Err(error):
            raise HTTPException(
                status_code=error.http_status,
                detail={"code": error.code, "message": error.message},
            )


@router.post("/register", response_model=UserResponse, status_code=201)
async def register_user_handler(
    request: RegisterRequest,
    env: Env = Depends(get_env),
):
    """
    POST /users/register → register_user (derived)
    """
    domain_input = RegistrationInput(
        email=request.email,
        password=request.password,
    )
    
    result = await register_user(domain_input).run(env)
    
    match result:
        case Ok(user):
            return UserResponse.from_domain(user)
        case Err(error):
            raise HTTPException(
                status_code=error.http_status,
                detail={"code": error.code, "message": error.message},
            )
```

## API Dependencies (Env Provider)

```python
# src/api/dependencies.py
"""
FastAPI dependencies for injecting Env.

This is where Reader monad becomes concrete.
"""
from fastapi import Depends
from sqlalchemy.ext.asyncio import AsyncSession

from ..domain.effects.app import Env
from ..domain.interfaces.repositories import Repositories
from ..storage.repositories.user_repository import SqlUserRepository
from ..config import get_settings, Settings
from ..storage.database import get_session


async def get_env(
    session: AsyncSession = Depends(get_session),
    settings: Settings = Depends(get_settings),
) -> Env:
    """
    Build Env from FastAPI dependencies.
    
    This is the Reader interpretation:
    Reader[Env, A] becomes Depends(get_env) in FastAPI.
    """
    repositories = Repositories(
        users=SqlUserRepository(session),
        # ... other repositories
    )
    
    return Env(
        repositories=repositories,
        config=settings,
    )
```

## Error Handler Middleware

```python
# src/middleware/error_handler.py
"""
Global error handler.

Transforms any unhandled AppError to HTTP response.
This is a natural transformation: AppError → HTTPResponse.
"""
from fastapi import Request
from fastapi.responses import JSONResponse
from starlette.middleware.base import BaseHTTPMiddleware

from ..domain.effects.errors import AppError, DomainError, InfraError


class ErrorHandlerMiddleware(BaseHTTPMiddleware):
    """
    Catch domain errors and convert to HTTP responses.
    
    Natural transformation: Either[AppError, Response] → HTTPResponse
    """
    
    async def dispatch(self, request: Request, call_next):
        try:
            return await call_next(request)
        except DomainError as e:
            return JSONResponse(
                status_code=e.http_status,
                content={
                    "error": {
                        "code": e.code,
                        "message": e.message,
                    }
                },
            )
        except InfraError as e:
            return JSONResponse(
                status_code=503,
                content={
                    "error": {
                        "code": "infra/unavailable",
                        "message": "Service temporarily unavailable",
                    }
                },
            )
```

## Validation Checklist

```bash
# 1. Effects module exists (prerequisite)
test -f gen/python/src/domain/effects/app.py || exit 1

# 2. Operations import from effects
grep -q "from ..effects import App" gen/python/src/domain/operations/user_ops.py

# 3. Operations return App[A]
grep -q "def create_user.*-> App\[" gen/python/src/domain/operations/user_ops.py

# 4. Operations don't take repo as parameter
! grep -q "def create_user.*repo:" gen/python/src/domain/operations/user_ops.py

# 5. Handlers use Env dependency
grep -q "env: Env = Depends" gen/python/src/api/handlers/user_handlers.py

# 6. Imports work
cd gen/python
python -c "from src.domain.operations.user_ops import create_user"
python -c "from src.api.handlers.user_handlers import router"
```

## morphisms-manifest.yaml

```yaml
version: "1.0"
language: python

# Generator morphisms
generators:
  - id: "create_user"
    file: "src/domain/operations/user_ops.py"
    signature: "(CreateUserInput) -> App[User]"
    effects: ["IO", "Either[UserError, _]"]
    traces_to: "build/category.yaml#morphisms.create_user"
    
  - id: "get_user"
    file: "src/domain/operations/user_ops.py"
    signature: "(UserId) -> App[User]"
    effects: ["IO", "Either[UserError, _]"]
    traces_to: "build/category.yaml#morphisms.get_user"
    
  - id: "validate_email"
    file: "src/domain/operations/pure.py"
    signature: "(str) -> Result[ValidationError, Email]"
    effects: ["Either[ValidationError, _]"]
    pure: true
    traces_to: "build/category.yaml#morphisms.validate_email"

# Derived morphisms (compositions)
derived:
  - id: "register_user"
    file: "src/domain/workflows/registration.py"
    signature: "(RegistrationInput) -> App[User]"
    composed_of: ["validate_email", "validate_password", "create_user"]
    composition_type: "kleisli"
    traces_to: "build/category.yaml#morphisms.register_user"

# F_api functor application
api_handlers:
  enabled: true
  files:
    - file: "src/api/handlers/user_handlers.py"
      endpoints:
        - method: "POST"
          path: "/users"
          morphism: "create_user"
          
        - method: "GET"
          path: "/users/{id}"
          morphism: "get_user"
          
        - method: "POST"
          path: "/users/register"
          morphism: "register_user"
      traces_to: "build/functors.yaml#F_api"

# Middleware (transformations)
middleware:
  - file: "src/middleware/error_handler.py"
    transformation: "error_to_http"
    traces_to: "build/transformations.yaml"

validation:
  all_return_app: true
  imports_from_effects: true
  env_dependency_injection: true
  signatures_match_spec: true
```

## Do NOT

- **Return plain types** — Effectful ops return `App[A]`
- **Raise exceptions** — Return `err(...)` in Result
- **Pass dependencies as parameters** — Get from `Env`
- **Import Result from here** — Import from `domain/effects`
- **Skip validation** — Verify signatures match spec
- **Mix pure and effectful** — Pure returns `Result`, effectful returns `App`
