---
name: handler-generator
description: |
  Generate HTTP route handlers from functor maps. Creates FastAPI routers that
  apply the HTTP functor to domain operations. Transforms requests/responses
  through DTOs and handles errors appropriately.
  Input: maps/functors/http.map.yaml, services, dtos
  Output: generated/python/src/{project}/api/routes/*.py
---

# Handler Generator

Generate HTTP handlers applying the HTTP functor.

## Purpose

Transform HTTP functor maps into route handlers:
1. Generate FastAPI routers for each service
2. Apply HTTP functor (Domain → HTTP)
3. Transform DTOs to/from domain entities
4. Map domain errors to HTTP status codes

## Input

- `maps/functors/http.map.yaml` - HTTP functor definition
- `generated/.../services/*.py` - Application services
- `generated/.../dtos/*.py` - Request/Response DTOs

## Output

```
generated/python/src/{project}/api/
├── __init__.py
├── main.py
├── routes/
│   ├── __init__.py
│   ├── merchant_routes.py
│   ├── profile_routes.py
│   └── analysis_routes.py
└── dependencies.py
```

## HTTP Functor Application

### Mathematical Foundation

```
HTTP Functor: Domain → HTTP

Object map:
  Merchant → (MerchantRequest, MerchantResponse)
  
Morphism map:
  create_merchant: CreateDTO → Merchant
    ↦
  POST /merchants: CreateMerchantRequest → MerchantResponse
  
Functor laws (from functor.cert.yaml):
  - HTTP(id) = id (identity endpoint returns input)
  - HTTP(g∘f) = HTTP(g) ∘ HTTP(f) (composed operations)
```

## Generation Rules

### Route Handler Generation

```yaml
# From http.map.yaml
endpoints:
  - domain_operation: create_merchant
    method: POST
    path: "/merchants"
    request: CreateMerchantRequest
    response: MerchantResponse
    status_codes:
      success: 201
      validation_error: 400
      conflict: 409
```

Generated Python:

```python
# generated/python/src/{project}/api/routes/merchant_routes.py

from __future__ import annotations
from typing import List, Optional
from uuid import UUID

from fastapi import APIRouter, Depends, HTTPException, status
from fastapi.responses import JSONResponse

from ..dependencies import get_merchant_service
from ...application.services.merchant_service import (
    MerchantService,
    MerchantError,
    MerchantNotFound,
    MerchantAlreadyExists,
    ValidationError,
)
from ...application.dtos.requests import CreateMerchantRequest, UpdateMerchantRequest
from ...application.dtos.responses import MerchantResponse, MerchantListResponse
from ...domain.value_objects.identifiers import MerchantId
from ...domain.value_objects.result import Success, Failure

router = APIRouter(prefix="/api/v1/merchants", tags=["merchants"])


@router.post(
    "",
    response_model=MerchantResponse,
    status_code=status.HTTP_201_CREATED,
    responses={
        400: {"description": "Validation error"},
        409: {"description": "Merchant already exists"},
    }
)
async def create_merchant(
    request: CreateMerchantRequest,
    service: MerchantService = Depends(get_merchant_service)
) -> MerchantResponse:
    """
    Create a new merchant.
    
    HTTP Functor application:
    - Request DTO → Domain DTO (to_domain)
    - Domain operation (create_merchant)
    - Domain entity → Response DTO (from_domain)
    
    Certificate: functor.cert.yaml#http_functor_comp
    """
    # Apply HTTP functor (request → domain)
    dto = request.to_domain()
    
    # Execute domain operation (morphism in Domain category)
    result = await service.create_merchant(dto)
    
    # Apply HTTP functor (domain → response) + error handling
    match result:
        case Success(merchant):
            return MerchantResponse.from_domain(merchant)
        case Failure(error):
            raise _map_error_to_http(error)


@router.get(
    "/{merchant_id}",
    response_model=MerchantResponse,
    responses={
        404: {"description": "Merchant not found"},
    }
)
async def get_merchant(
    merchant_id: UUID,
    service: MerchantService = Depends(get_merchant_service)
) -> MerchantResponse:
    """
    Get merchant by ID.
    
    HTTP Functor: GET /{id} → get_merchant(id)
    """
    result = await service.get_merchant(MerchantId(merchant_id))
    
    match result:
        case Success(merchant) if merchant is not None:
            return MerchantResponse.from_domain(merchant)
        case Success(None):
            raise HTTPException(
                status_code=status.HTTP_404_NOT_FOUND,
                detail=f"Merchant {merchant_id} not found"
            )
        case Failure(error):
            raise _map_error_to_http(error)


@router.patch(
    "/{merchant_id}",
    response_model=MerchantResponse,
    responses={
        400: {"description": "Validation error"},
        404: {"description": "Merchant not found"},
    }
)
async def update_merchant(
    merchant_id: UUID,
    request: UpdateMerchantRequest,
    service: MerchantService = Depends(get_merchant_service)
) -> MerchantResponse:
    """
    Update merchant.
    
    HTTP Functor: PATCH /{id} → update_merchant(id, dto)
    Composition: HTTP(get) ∘ HTTP(modify) ∘ HTTP(persist)
    """
    dto = request.to_domain()
    result = await service.update_merchant(MerchantId(merchant_id), dto)
    
    match result:
        case Success(merchant):
            return MerchantResponse.from_domain(merchant)
        case Failure(error):
            raise _map_error_to_http(error)


@router.delete(
    "/{merchant_id}",
    status_code=status.HTTP_204_NO_CONTENT,
    responses={
        404: {"description": "Merchant not found"},
    }
)
async def delete_merchant(
    merchant_id: UUID,
    service: MerchantService = Depends(get_merchant_service)
) -> None:
    """
    Delete merchant.
    
    HTTP Functor: DELETE /{id} → delete_merchant(id)
    """
    result = await service.delete_merchant(MerchantId(merchant_id))
    
    match result:
        case Success(deleted) if deleted:
            return None
        case Success(False):
            raise HTTPException(
                status_code=status.HTTP_404_NOT_FOUND,
                detail=f"Merchant {merchant_id} not found"
            )
        case Failure(error):
            raise _map_error_to_http(error)


@router.get(
    "",
    response_model=MerchantListResponse
)
async def list_merchants(
    offset: int = 0,
    limit: int = 100,
    service: MerchantService = Depends(get_merchant_service)
) -> MerchantListResponse:
    """
    List merchants with pagination.
    
    HTTP Functor: GET / → list_merchants()
    """
    result = await service.list_merchants(offset, limit)
    
    match result:
        case Success(merchants):
            return MerchantListResponse(
                items=[MerchantResponse.from_domain(m) for m in merchants],
                offset=offset,
                limit=limit,
                total=len(merchants)  # Would come from count query
            )
        case Failure(error):
            raise _map_error_to_http(error)


def _map_error_to_http(error: MerchantError) -> HTTPException:
    """
    Natural transformation: MerchantError → HTTPException.
    
    Maps domain errors to appropriate HTTP status codes.
    This is a natural transformation component.
    
    Certificate: naturality.cert.yaml (error handling is natural)
    """
    match error:
        case ValidationError(message):
            return HTTPException(
                status_code=status.HTTP_400_BAD_REQUEST,
                detail=message
            )
        case MerchantNotFound(id):
            return HTTPException(
                status_code=status.HTTP_404_NOT_FOUND,
                detail=f"Merchant {id} not found"
            )
        case MerchantAlreadyExists(domain):
            return HTTPException(
                status_code=status.HTTP_409_CONFLICT,
                detail=f"Merchant with domain {domain} already exists"
            )
        case _:
            return HTTPException(
                status_code=status.HTTP_500_INTERNAL_SERVER_ERROR,
                detail="Internal server error"
            )
```

### Main Application

```python
# generated/python/src/{project}/api/main.py

from __future__ import annotations
from contextlib import asynccontextmanager

from fastapi import FastAPI
from fastapi.middleware.cors import CORSMiddleware

from .routes import merchant_routes, profile_routes, analysis_routes
from .middleware.auth import AuthMiddleware
from .middleware.metrics import MetricsMiddleware
from .middleware.logging import LoggingMiddleware
from ..infrastructure.database import init_db, close_db


@asynccontextmanager
async def lifespan(app: FastAPI):
    """Application lifespan handler."""
    # Startup
    await init_db()
    yield
    # Shutdown
    await close_db()


def create_app() -> FastAPI:
    """
    Create FastAPI application.
    
    Categorical structure:
    - Routes are HTTP functor applications
    - Middleware are natural transformations
    - Composition follows categorical laws
    """
    app = FastAPI(
        title="GlamYouUp API",
        version="1.0.0",
        lifespan=lifespan
    )
    
    # CORS middleware
    app.add_middleware(
        CORSMiddleware,
        allow_origins=["*"],  # Configure properly in production
        allow_credentials=True,
        allow_methods=["*"],
        allow_headers=["*"],
    )
    
    # Custom middleware (natural transformations)
    # Applied in reverse order
    app.add_middleware(LoggingMiddleware)
    app.add_middleware(MetricsMiddleware)
    app.add_middleware(AuthMiddleware)
    
    # Register routes (HTTP functor applications)
    app.include_router(merchant_routes.router)
    app.include_router(profile_routes.router)
    app.include_router(analysis_routes.router)
    
    return app


app = create_app()
```

### Dependencies (Dependency Injection)

```python
# generated/python/src/{project}/api/dependencies.py

from __future__ import annotations
from typing import AsyncGenerator

from fastapi import Depends
from sqlalchemy.ext.asyncio import AsyncSession

from ..infrastructure.database import get_session
from ..infrastructure.repositories.merchant_repository import SqlMerchantRepository
from ..infrastructure.repositories.profile_repository import SqlProfileRepository
from ..infrastructure.external.shopify_client import ShopifyClient
from ..application.services.merchant_service import MerchantService
from ..application.services.profile_service import ProfileService


async def get_merchant_repository(
    session: AsyncSession = Depends(get_session)
) -> SqlMerchantRepository:
    """
    Dependency injection for MerchantRepository.
    
    Categorical: Reader monad - provides repository from context
    Certificate: monad.cert.yaml#reader_left_identity
    """
    return SqlMerchantRepository(session)


async def get_shopify_client() -> ShopifyClient:
    """Dependency injection for ShopifyClient."""
    return ShopifyClient()


async def get_merchant_service(
    repository: SqlMerchantRepository = Depends(get_merchant_repository),
    shopify_client: ShopifyClient = Depends(get_shopify_client)
) -> MerchantService:
    """
    Dependency injection for MerchantService.
    
    Wires all dependencies together.
    Reader composition: R[Repository] × R[Client] → R[Service]
    """
    return MerchantService(
        repository=repository,
        shopify_client=shopify_client
    )


async def get_profile_repository(
    session: AsyncSession = Depends(get_session)
) -> SqlProfileRepository:
    return SqlProfileRepository(session)


async def get_profile_service(
    repository: SqlProfileRepository = Depends(get_profile_repository),
    merchant_repository: SqlMerchantRepository = Depends(get_merchant_repository)
) -> ProfileService:
    return ProfileService(
        repository=repository,
        merchant_repository=merchant_repository
    )
```

## Template Structure

```python
# Route handler template

from __future__ import annotations
from typing import List, Optional
from uuid import UUID

from fastapi import APIRouter, Depends, HTTPException, status

from ..dependencies import get_{{ service_name }}_service
from ...application.services.{{ service_name }}_service import {{ Service }}Service
from ...application.dtos.requests import {{ CreateRequest }}, {{ UpdateRequest }}
from ...application.dtos.responses import {{ Response }}, {{ ListResponse }}
from ...domain.value_objects.identifiers import {{ Entity }}Id
from ...domain.value_objects.result import Success, Failure

router = APIRouter(prefix="/api/v1/{{ route_prefix }}", tags=["{{ tag }}"])


{% for endpoint in endpoints %}
@router.{{ endpoint.method }}(
    "{{ endpoint.path }}",
    {% if endpoint.response_model %}response_model={{ endpoint.response_model }},{% endif %}
    {% if endpoint.status_code %}status_code=status.{{ endpoint.status_code }},{% endif %}
)
async def {{ endpoint.name }}(
    {{ endpoint.params | join(",\n    ") }},
    service: {{ Service }}Service = Depends(get_{{ service_name }}_service)
) -> {{ endpoint.return_type }}:
    """{{ endpoint.docstring }}"""
    {{ endpoint.implementation }}
{% endfor %}
```

## Validation Checks

```yaml
validation:
  routes_generated:
    check: "All services have corresponding routes"
    
  crud_complete:
    check: "All CRUD operations have endpoints"
    
  error_handling:
    check: "All domain errors map to HTTP errors"
    
  dependencies_wired:
    check: "All services have dependency providers"
```

## Next Skills

Output feeds into:
- `middleware-generator`
- `code-validator`
