---
name: apply-standards
description: |
  Apply standardization contracts to generated code. Injects middleware for
  authentication, validation, error handling, and observability. Uses natural
  transformations to preserve categorical composition. Run after gen-code.
---

# Apply Standards

Inject cross-cutting concerns into generated code while preserving composition.

## Mathematical Basis

Standards are **natural transformations** α: F → G where:
- F is the identity functor (original code)
- G is the standardized functor (code with middleware)

**Naturality condition:** `G(f) ∘ α_A = α_B ∘ F(f)`

This ensures: applying standards then composing = composing then applying standards.

## Input

- `artifacts/v{N}/build/transformations.yaml` — Transformation definitions
- `artifacts/v{N}/build/effects.yaml` — Error types for handlers
- `artifacts/v{N}/gen/python/src/` — Generated code to standardize

## Output

- `artifacts/v{N}/gen/python/src/middleware/` — Middleware implementations
- Modified handler files with middleware applied
- `artifacts/v{N}/gen/standardization-report.yaml`

## Standards to Apply

### 1. Error Handler (AppError → HTTPResponse)

**Natural transformation:** Domain errors to HTTP responses.

```python
# src/middleware/error_handler.py
"""
Error handler middleware.

Natural transformation: Either[AppError, A] → HTTPResponse[A]
Preserves composition by handling errors uniformly.
"""
from fastapi import Request
from fastapi.responses import JSONResponse
from starlette.middleware.base import BaseHTTPMiddleware

from ..domain.effects.errors import (
    AppError,
    DomainError,
    ValidationError,
    NotFoundError,
    AuthorizationError,
    InfraError,
)


class ErrorHandlerMiddleware(BaseHTTPMiddleware):
    """
    Transform AppError to HTTP response.
    
    Injection point: Outer middleware layer
    Naturality: All errors transformed uniformly
    """
    
    async def dispatch(self, request: Request, call_next):
        try:
            return await call_next(request)
        except DomainError as e:
            return JSONResponse(
                status_code=e.http_status,
                content={
                    "success": False,
                    "data": None,
                    "error": {
                        "code": e.code,
                        "message": e.message,
                    },
                    "meta": {
                        "request_id": request.state.request_id,
                    }
                },
            )
        except Exception as e:
            # Unexpected error - log and return 500
            import logging
            logging.exception("Unhandled error")
            return JSONResponse(
                status_code=500,
                content={
                    "success": False,
                    "data": None,
                    "error": {
                        "code": "internal/error",
                        "message": "Internal server error",
                    },
                },
            )
```

### 2. Request ID Propagation

**Natural transformation:** Request → Request with correlation ID.

```python
# src/middleware/request_id.py
"""
Request ID middleware.

Adds correlation ID to all requests for tracing.
"""
from uuid import uuid4
from fastapi import Request
from starlette.middleware.base import BaseHTTPMiddleware


class RequestIdMiddleware(BaseHTTPMiddleware):
    """
    Add request_id to request state.
    
    Injection point: Outer layer (before error handler)
    """
    
    async def dispatch(self, request: Request, call_next):
        request_id = request.headers.get("X-Request-ID", str(uuid4()))
        request.state.request_id = request_id
        
        response = await call_next(request)
        response.headers["X-Request-ID"] = request_id
        
        return response
```

### 3. Authentication

**Natural transformation:** Request → AuthenticatedRequest | Unauthorized.

```python
# src/middleware/auth.py
"""
Authentication middleware.

Verifies JWT tokens and attaches user context.
"""
from fastapi import Request, HTTPException
from starlette.middleware.base import BaseHTTPMiddleware
from jose import jwt, JWTError

from ..config import get_settings


class AuthMiddleware(BaseHTTPMiddleware):
    """
    JWT authentication.
    
    Injection point: After request_id, before handlers
    Excludes: /health, /metrics, /docs, /openapi.json
    """
    
    EXCLUDE_PATHS = {"/health", "/metrics", "/docs", "/openapi.json", "/redoc"}
    
    async def dispatch(self, request: Request, call_next):
        # Skip excluded paths
        if request.url.path in self.EXCLUDE_PATHS:
            return await call_next(request)
        
        # Extract token
        auth_header = request.headers.get("Authorization")
        if not auth_header or not auth_header.startswith("Bearer "):
            raise HTTPException(
                status_code=401,
                detail={"code": "auth/missing_token", "message": "Missing auth token"}
            )
        
        token = auth_header[7:]
        
        try:
            settings = get_settings()
            payload = jwt.decode(
                token,
                settings.jwt_secret,
                algorithms=["HS256"]
            )
            request.state.user_id = payload.get("sub")
            request.state.user_claims = payload
        except JWTError:
            raise HTTPException(
                status_code=401,
                detail={"code": "auth/invalid_token", "message": "Invalid token"}
            )
        
        return await call_next(request)
```

### 4. Standard Response Format

**Inject response wrapper into handlers:**

```python
# Transformation applied to handler return values
# Before:
return UserResponse.from_domain(user)

# After:
from ..middleware.response import wrap_response
return wrap_response(
    data=UserResponse.from_domain(user),
    request_id=request.state.request_id
)
```

```python
# src/middleware/response.py
"""
Standard response formatting.
"""
from datetime import datetime
from typing import TypeVar, Generic, Optional
from pydantic import BaseModel

T = TypeVar("T")


class ResponseMeta(BaseModel):
    request_id: str
    timestamp: str


class StandardResponse(BaseModel, Generic[T]):
    """
    Standard API response envelope.
    
    Invariants:
    - success XOR error (exactly one)
    - success=True → data is not None
    - success=False → error is not None
    - meta always present
    """
    success: bool
    data: Optional[T]
    error: Optional[dict]
    meta: ResponseMeta


def wrap_response(
    data: T,
    request_id: str,
    error: Optional[dict] = None
) -> StandardResponse[T]:
    """
    Wrap response in standard envelope.
    """
    return StandardResponse(
        success=error is None,
        data=data if error is None else None,
        error=error,
        meta=ResponseMeta(
            request_id=request_id,
            timestamp=datetime.utcnow().isoformat(),
        )
    )
```

## Injection Process

### Step 1: Generate Middleware Files

Create all middleware implementations in `src/middleware/`:

```
src/middleware/
├── __init__.py
├── error_handler.py
├── request_id.py
├── auth.py
├── response.py
└── setup.py           ← Middleware registration
```

### Step 2: Generate Middleware Setup

```python
# src/middleware/setup.py
"""
Middleware stack setup.

Order matters! Applied in reverse order (first added = outermost):
1. request_id (outermost - adds ID before anything else)
2. error_handler (catches all errors)
3. auth (authentication check)
"""
from fastapi import FastAPI

from .request_id import RequestIdMiddleware
from .error_handler import ErrorHandlerMiddleware
from .auth import AuthMiddleware


def setup_middleware(app: FastAPI) -> None:
    """
    Configure middleware stack.
    
    Composition order (outer to inner):
    request_id → error_handler → auth → handler
    
    Applied in reverse (inner to outer):
    """
    # Auth (innermost of the custom middleware)
    app.add_middleware(AuthMiddleware)
    
    # Error handler (catches errors from auth and handlers)
    app.add_middleware(ErrorHandlerMiddleware)
    
    # Request ID (outermost - ensures all requests have ID)
    app.add_middleware(RequestIdMiddleware)
```

### Step 3: Inject into main.py

Add middleware setup to application factory:

```python
# In src/main.py, add:
from .middleware.setup import setup_middleware

def create_app() -> FastAPI:
    app = FastAPI(...)
    
    # <<< STANDARDIZATION:MIDDLEWARE_SETUP:BEGIN >>>
    setup_middleware(app)
    # <<< STANDARDIZATION:MIDDLEWARE_SETUP:END >>>
    
    # Routes...
    return app
```

### Step 4: Inject Response Wrapping

Transform handler return statements:

**Before:**
```python
@router.get("/{user_id}")
async def get_user_handler(user_id: UUID, env: Env = Depends(get_env)):
    result = await get_user(UserId(user_id)).run(env)
    match result:
        case Ok(user):
            return UserResponse.from_domain(user)
        case Err(error):
            raise HTTPException(...)
```

**After:**
```python
@router.get("/{user_id}")
async def get_user_handler(
    user_id: UUID,
    request: Request,  # <<< ADDED for request_id
    env: Env = Depends(get_env)
):
    result = await get_user(UserId(user_id)).run(env)
    match result:
        case Ok(user):
            # <<< STANDARDIZATION:RESPONSE_WRAP:BEGIN >>>
            return StandardResponse(
                success=True,
                data=UserResponse.from_domain(user),
                error=None,
                meta=ResponseMeta(
                    request_id=request.state.request_id,
                    timestamp=datetime.utcnow().isoformat(),
                )
            )
            # <<< STANDARDIZATION:RESPONSE_WRAP:END >>>
        case Err(error):
            raise error  # Let error_handler middleware handle
```

## Verification

### Naturality Check

Verify standards preserve composition:

```python
def verify_naturality():
    """
    For all handler compositions h = g ∘ f:
    standardize(h) ≡ standardize(g) ∘ standardize(f)
    """
    # Check that middleware applies uniformly
    # Check that response format is consistent
    # Check that error handling is uniform
    pass
```

### Property Tests

```python
@given(valid_request())
async def test_error_handling_uniform(request):
    """All errors produce same response structure."""
    response = await client.request(...)
    if response.status_code >= 400:
        body = response.json()
        assert "success" in body
        assert body["success"] == False
        assert "error" in body
        assert "code" in body["error"]


@given(valid_request())
async def test_request_id_propagated(request):
    """All responses include request ID."""
    response = await client.request(...)
    assert "X-Request-ID" in response.headers
```

## Output Report

```yaml
# gen/standardization-report.yaml
version: "1.0"

standards_applied:
  - name: error_handler
    file: src/middleware/error_handler.py
    injection_points:
      - src/main.py (middleware stack)
    transforms: "AppError → HTTPResponse"
    
  - name: request_id
    file: src/middleware/request_id.py
    injection_points:
      - src/main.py (middleware stack)
    transforms: "Request → Request with ID"
    
  - name: auth
    file: src/middleware/auth.py
    injection_points:
      - src/main.py (middleware stack)
    excludes: [/health, /metrics, /docs]
    transforms: "Request → AuthenticatedRequest"
    
  - name: response_format
    file: src/middleware/response.py
    injection_points:
      - src/api/handlers/*.py (return statements)
    transforms: "T → StandardResponse[T]"

handlers_modified:
  - file: src/api/handlers/user_handlers.py
    functions: [create_user_handler, get_user_handler, ...]
    injections: [response_wrap, request_param]
    
  - file: src/api/handlers/auth_handlers.py
    functions: [login_handler, refresh_handler, ...]
    injections: [response_wrap, request_param]

naturality_verified: true
composition_preserved: true
```

## Validation

```bash
# Middleware files exist
test -f gen/python/src/middleware/error_handler.py
test -f gen/python/src/middleware/auth.py
test -f gen/python/src/middleware/response.py
test -f gen/python/src/middleware/setup.py

# main.py has middleware setup
grep -q "setup_middleware" gen/python/src/main.py

# Handlers have response wrapping
grep -q "StandardResponse" gen/python/src/api/handlers/*.py

# Imports work
python -c "from src.middleware.setup import setup_middleware"
```

## Do NOT

- **Skip middleware setup** — All middleware must be registered
- **Modify error format** — Must match StandardResponse schema
- **Skip auth on protected routes** — Only exclusion list is exempt
- **Return unwrapped responses** — All handlers use StandardResponse
- **Break naturality** — Standards must apply uniformly
