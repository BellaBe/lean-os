---
name: middleware-generator
description: |
  Generate middleware from transformation maps. Creates FastAPI middleware that
  implement natural transformations for auth, metrics, logging, and tracing.
  Each middleware is a natural transformation component.
  Input: maps/transformations/*.map.yaml
  Output: generated/python/src/{project}/api/middleware/*.py
---

# Middleware Generator

Generate middleware as natural transformation components.

## Purpose

Transform natural transformation maps into middleware:
1. Generate authentication middleware (HTTP ⟹ AuthHTTP)
2. Generate metrics middleware (Handler ⟹ MetricsHandler)
3. Generate logging middleware (Handler ⟹ LoggedHandler)
4. Generate tracing middleware (Handler ⟹ TracedHandler)

## Input

- `maps/transformations/middleware.map.yaml` - Middleware chain
- `maps/transformations/auth.map.yaml` - Auth transformations
- `maps/transformations/observability.map.yaml` - Metrics/tracing/logging

## Output

```
generated/python/src/{project}/api/middleware/
├── __init__.py
├── auth.py
├── metrics.py
├── logging.py
├── tracing.py
└── request_id.py
```

## Natural Transformation Implementation

### Mathematical Foundation

```
Natural transformation α: F ⟹ G

For middleware:
- F = RawHandler: Request → Response
- G = EnhancedHandler: Request → Response (with added behavior)

α_A: F(A) → G(A) is the middleware component

Naturality: α_B ∘ F(f) = G(f) ∘ α_A
- Middleware doesn't affect request/response transformation
- Just adds cross-cutting concerns

Certificate: naturality.cert.yaml
```

## Generated Code

### Authentication Middleware

```python
# generated/python/src/{project}/api/middleware/auth.py

from __future__ import annotations
from typing import Optional, Callable
import logging

from fastapi import Request, HTTPException, status
from fastapi.security import HTTPBearer, HTTPAuthorizationCredentials
from starlette.middleware.base import BaseHTTPMiddleware
from starlette.responses import Response

from ...domain.value_objects.result import Result, Success, Failure
from ...infrastructure.auth import verify_token, TokenPayload

logger = logging.getLogger(__name__)
security = HTTPBearer(auto_error=False)


class AuthMiddleware(BaseHTTPMiddleware):
    """
    Authentication middleware.
    
    Natural transformation: HTTP ⟹ AuthenticatedHTTP
    
    Component α_A adds authentication context to request:
    - Verifies JWT token
    - Attaches user identity to request state
    
    Certificate: naturality.cert.yaml#auth_naturality
    
    Naturality property:
    - Auth(compose(f,g)) = compose(Auth(f), Auth(g))
    - Authentication is independent of route logic
    """
    
    # Paths that don't require authentication
    PUBLIC_PATHS = {
        "/health",
        "/metrics",
        "/docs",
        "/openapi.json",
        "/redoc",
    }
    
    async def dispatch(
        self, 
        request: Request, 
        call_next: Callable
    ) -> Response:
        """
        Apply authentication transformation.
        
        α_Request: Request → AuthenticatedRequest
        """
        # Skip auth for public paths
        if self._is_public_path(request.url.path):
            return await call_next(request)
        
        # Extract token
        auth_header = request.headers.get("Authorization")
        if not auth_header or not auth_header.startswith("Bearer "):
            raise HTTPException(
                status_code=status.HTTP_401_UNAUTHORIZED,
                detail="Missing or invalid authorization header",
                headers={"WWW-Authenticate": "Bearer"}
            )
        
        token = auth_header.split(" ")[1]
        
        # Verify token
        result = await verify_token(token)
        match result:
            case Success(payload):
                # Attach identity to request state
                request.state.user = payload
                request.state.tenant_id = payload.tenant_id
            case Failure(error):
                raise HTTPException(
                    status_code=status.HTTP_401_UNAUTHORIZED,
                    detail=str(error),
                    headers={"WWW-Authenticate": "Bearer"}
                )
        
        # Continue to next handler
        return await call_next(request)
    
    def _is_public_path(self, path: str) -> bool:
        """Check if path is public."""
        return any(path.startswith(p) for p in self.PUBLIC_PATHS)
```

### Metrics Middleware

```python
# generated/python/src/{project}/api/middleware/metrics.py

from __future__ import annotations
from typing import Callable
import time
import logging

from fastapi import Request
from starlette.middleware.base import BaseHTTPMiddleware
from starlette.responses import Response
from prometheus_client import Counter, Histogram

logger = logging.getLogger(__name__)

# Prometheus metrics
REQUEST_COUNT = Counter(
    "http_requests_total",
    "Total HTTP requests",
    ["method", "endpoint", "status"]
)

REQUEST_LATENCY = Histogram(
    "http_request_duration_seconds",
    "HTTP request latency",
    ["method", "endpoint"],
    buckets=[0.01, 0.05, 0.1, 0.25, 0.5, 1.0, 2.5, 5.0, 10.0]
)


class MetricsMiddleware(BaseHTTPMiddleware):
    """
    Metrics collection middleware.
    
    Natural transformation: Handler ⟹ MetricsHandler
    
    Component α_A adds metrics collection:
    - Counts requests by method/endpoint/status
    - Records request latency histogram
    
    Certificate: naturality.cert.yaml#metrics_naturality
    
    Naturality property:
    - Metrics(f ∘ g) = Metrics(f) ∘ Metrics(g)
    - Metrics collection is independent of handler logic
    """
    
    async def dispatch(
        self,
        request: Request,
        call_next: Callable
    ) -> Response:
        """
        Apply metrics transformation.
        
        α_Handler: Handler → MetricsHandler
        """
        method = request.method
        endpoint = self._get_endpoint(request)
        
        # Start timer
        start_time = time.perf_counter()
        
        # Call next handler
        response = await call_next(request)
        
        # Record metrics
        duration = time.perf_counter() - start_time
        status_code = str(response.status_code)
        
        REQUEST_COUNT.labels(
            method=method,
            endpoint=endpoint,
            status=status_code
        ).inc()
        
        REQUEST_LATENCY.labels(
            method=method,
            endpoint=endpoint
        ).observe(duration)
        
        return response
    
    def _get_endpoint(self, request: Request) -> str:
        """Extract endpoint pattern from request."""
        # Use route pattern if available, else path
        if request.scope.get("route"):
            return request.scope["route"].path
        return request.url.path
```

### Logging Middleware

```python
# generated/python/src/{project}/api/middleware/logging.py

from __future__ import annotations
from typing import Callable
import time
import logging
import uuid

from fastapi import Request
from starlette.middleware.base import BaseHTTPMiddleware
from starlette.responses import Response

logger = logging.getLogger(__name__)


class LoggingMiddleware(BaseHTTPMiddleware):
    """
    Structured logging middleware.
    
    Natural transformation: Handler ⟹ LoggedHandler
    
    Component α_A adds structured logging:
    - Logs request start with method, path, request_id
    - Logs request completion with status, duration
    - Logs errors with stack trace
    
    Certificate: naturality.cert.yaml#logging_naturality
    """
    
    async def dispatch(
        self,
        request: Request,
        call_next: Callable
    ) -> Response:
        """
        Apply logging transformation.
        
        α_Handler: Handler → LoggedHandler
        """
        # Get or create request ID
        request_id = request.headers.get("X-Request-ID", str(uuid.uuid4()))
        request.state.request_id = request_id
        
        # Log request start
        logger.info(
            "Request started",
            extra={
                "request_id": request_id,
                "method": request.method,
                "path": request.url.path,
                "client_ip": request.client.host if request.client else None,
            }
        )
        
        start_time = time.perf_counter()
        
        try:
            response = await call_next(request)
            duration = time.perf_counter() - start_time
            
            # Log request completion
            logger.info(
                "Request completed",
                extra={
                    "request_id": request_id,
                    "method": request.method,
                    "path": request.url.path,
                    "status_code": response.status_code,
                    "duration_ms": round(duration * 1000, 2),
                }
            )
            
            # Add request ID to response headers
            response.headers["X-Request-ID"] = request_id
            return response
            
        except Exception as e:
            duration = time.perf_counter() - start_time
            
            logger.exception(
                "Request failed",
                extra={
                    "request_id": request_id,
                    "method": request.method,
                    "path": request.url.path,
                    "duration_ms": round(duration * 1000, 2),
                    "error": str(e),
                }
            )
            raise
```

### Tracing Middleware

```python
# generated/python/src/{project}/api/middleware/tracing.py

from __future__ import annotations
from typing import Callable, Optional
import logging

from fastapi import Request
from starlette.middleware.base import BaseHTTPMiddleware
from starlette.responses import Response
from opentelemetry import trace
from opentelemetry.trace import SpanKind, Status, StatusCode

logger = logging.getLogger(__name__)
tracer = trace.get_tracer(__name__)


class TracingMiddleware(BaseHTTPMiddleware):
    """
    Distributed tracing middleware.
    
    Natural transformation: Handler ⟹ TracedHandler
    
    Component α_A adds distributed tracing:
    - Creates span for each request
    - Propagates trace context
    - Records span attributes and events
    
    Certificate: naturality.cert.yaml#tracing_naturality
    """
    
    async def dispatch(
        self,
        request: Request,
        call_next: Callable
    ) -> Response:
        """
        Apply tracing transformation.
        
        α_Handler: Handler → TracedHandler
        """
        span_name = f"{request.method} {self._get_route(request)}"
        
        with tracer.start_as_current_span(
            span_name,
            kind=SpanKind.SERVER,
        ) as span:
            # Set span attributes
            span.set_attribute("http.method", request.method)
            span.set_attribute("http.url", str(request.url))
            span.set_attribute("http.scheme", request.url.scheme)
            span.set_attribute("http.host", request.url.hostname or "")
            span.set_attribute("http.target", request.url.path)
            
            if hasattr(request.state, "request_id"):
                span.set_attribute("request.id", request.state.request_id)
            
            try:
                response = await call_next(request)
                
                # Record response
                span.set_attribute("http.status_code", response.status_code)
                
                if response.status_code >= 400:
                    span.set_status(Status(StatusCode.ERROR))
                else:
                    span.set_status(Status(StatusCode.OK))
                
                return response
                
            except Exception as e:
                span.set_status(Status(StatusCode.ERROR, str(e)))
                span.record_exception(e)
                raise
    
    def _get_route(self, request: Request) -> str:
        """Get route pattern for span name."""
        if request.scope.get("route"):
            return request.scope["route"].path
        return request.url.path
```

### Request ID Middleware

```python
# generated/python/src/{project}/api/middleware/request_id.py

from __future__ import annotations
from typing import Callable
import uuid

from fastapi import Request
from starlette.middleware.base import BaseHTTPMiddleware
from starlette.responses import Response


class RequestIdMiddleware(BaseHTTPMiddleware):
    """
    Request ID middleware.
    
    Natural transformation: Request ⟹ RequestIdRequest
    
    Component α_A ensures every request has a unique ID:
    - Uses existing X-Request-ID header if present
    - Generates new UUID if not present
    - Propagates to response headers
    """
    
    async def dispatch(
        self,
        request: Request,
        call_next: Callable
    ) -> Response:
        """Add request ID to request and response."""
        request_id = request.headers.get("X-Request-ID")
        
        if not request_id:
            request_id = str(uuid.uuid4())
        
        request.state.request_id = request_id
        
        response = await call_next(request)
        response.headers["X-Request-ID"] = request_id
        
        return response
```

## Middleware Chain Configuration

```python
# generated/python/src/{project}/api/middleware/__init__.py

from .request_id import RequestIdMiddleware
from .logging import LoggingMiddleware
from .metrics import MetricsMiddleware
from .tracing import TracingMiddleware
from .auth import AuthMiddleware

__all__ = [
    "RequestIdMiddleware",
    "LoggingMiddleware", 
    "MetricsMiddleware",
    "TracingMiddleware",
    "AuthMiddleware",
]

# Middleware application order (applied in reverse):
# 1. RequestIdMiddleware - First to run, ensures ID exists
# 2. LoggingMiddleware - Logs request start/end
# 3. MetricsMiddleware - Collects timing metrics
# 4. TracingMiddleware - Creates distributed traces
# 5. AuthMiddleware - Validates authentication
#
# Chain composition: auth ∘ tracing ∘ metrics ∘ logging ∘ request_id
# Naturality ensures: each transformation is independent
```

## Validation Checks

```yaml
validation:
  middleware_generated:
    check: "All transformation maps have middleware"
    
  chain_order_correct:
    check: "Middleware applied in correct order"
    
  naturality_preserved:
    check: "Middleware don't modify request/response data"
```

## Next Skills

Output feeds into:
- `code-validator`
