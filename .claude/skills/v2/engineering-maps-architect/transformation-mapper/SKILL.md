---
name: transformation-mapper
description: |
  Map natural transformations to middleware and adapter implementations. Produces
  authentication transforms, validation middleware, observability wrappers.
  Natural transformations become decorators/wrappers preserving structure.
  Input: standards/security/*.std.yaml, standards/observability/*.std.yaml
  Output: maps/transformations/*.map.yaml
---

# Transformation Mapper

Map natural transformations to middleware implementations.

## Purpose

Transform natural transformations into wrappers/decorators:
1. Authentication transformation (HTTP ⟹ AuthHTTP)
2. Authorization transformation (AuthHTTP ⟹ AuthzHTTP)
3. Validation transformation (Request ⟹ ValidRequest)
4. Observability transformations (F ⟹ ObservedF)

## Input

- `standards/security/*.std.yaml` - Security transformations
- `standards/observability/*.std.yaml` - Observability transformations
- `maps/functors/*.map.yaml` - Functor mappings

## Output

```
maps/transformations/
├── middleware.map.yaml      # HTTP middleware chain
├── auth.map.yaml            # Authentication/authorization
└── observability.map.yaml   # Metrics/tracing/logging
```

## Natural Transformation Structure

### Abstract Pattern

```yaml
natural_transformation_pattern:
  structure:
    source_functor: "F: C → D"
    target_functor: "G: C → D"
    components: "α_A: F(A) → G(A) for each A in C"
    
  naturality:
    square: |
      For f: A → B in C,
      α_B ∘ F(f) = G(f) ∘ α_A
      (the naturality square commutes)
      
  implementation:
    pattern: |
      Wrap operations uniformly
      Same transformation applied to all operations
      Preserves composition
```

## Middleware Mapping

### Schema

```yaml
# maps/transformations/middleware.map.yaml

middleware:
  description: "HTTP middleware as natural transformation chain"
  
  # Middleware chain composition
  chain:
    order:
      - request_id      # Add request ID
      - logging_start   # Log request start
      - authentication  # Verify identity
      - authorization   # Check permissions
      - validation      # Validate input
      - rate_limiting   # Apply rate limits
      - handler         # Execute handler
      - logging_end     # Log response
      - error_handling  # Handle errors
      
    composition: |
      errorHandling ∘ loggingEnd ∘ handler ∘ rateLimiting ∘ 
      validation ∘ authorization ∘ authentication ∘ loggingStart ∘ requestId
      
  # Individual middleware mappings
  mappings:
    - name: request_id
      transformation: "HTTP ⟹ RequestIdHTTP"
      abstract:
        input: Request
        output: "Request with X-Request-ID header"
        component: "Add unique request ID if not present"
      targets:
        python:
          pattern: middleware_function
          template: |
            @app.middleware("http")
            async def request_id_middleware(
                request: Request, 
                call_next: Callable
            ) -> Response:
                """Natural transformation: Add request ID"""
                request_id = request.headers.get(
                    "X-Request-ID", 
                    str(uuid.uuid4())
                )
                request.state.request_id = request_id
                response = await call_next(request)
                response.headers["X-Request-ID"] = request_id
                return response
                
        typescript:
          pattern: express_middleware
          template: |
            function requestIdMiddleware(
              req: Request, 
              res: Response, 
              next: NextFunction
            ) {
              const requestId = req.headers['x-request-id'] || uuidv4();
              req.requestId = requestId;
              res.setHeader('X-Request-ID', requestId);
              next();
            }
            
    - name: error_handling
      transformation: "HandlerHTTP ⟹ SafeHTTP"
      abstract:
        input: "Handler that may throw"
        output: "Handler that returns error response"
        component: "Catch exceptions, convert to HTTP errors"
      targets:
        python:
          pattern: exception_handler
          template: |
            @app.exception_handler(ApplicationError)
            async def application_error_handler(
                request: Request, 
                exc: ApplicationError
            ) -> JSONResponse:
                """Transform application errors to HTTP responses"""
                return JSONResponse(
                    status_code=exc.status_code,
                    content={
                        "error": exc.error_code,
                        "message": exc.message,
                        "request_id": request.state.request_id,
                    },
                )
                
            @app.exception_handler(Exception)
            async def generic_error_handler(
                request: Request, 
                exc: Exception
            ) -> JSONResponse:
                """Catch-all error handler"""
                logger.exception("Unhandled exception", exc_info=exc)
                return JSONResponse(
                    status_code=500,
                    content={
                        "error": "INTERNAL_ERROR",
                        "message": "An unexpected error occurred",
                        "request_id": request.state.request_id,
                    },
                )
```

## Auth Transformation Mapping

### Schema

```yaml
# maps/transformations/auth.map.yaml

auth_transformations:
  # Authentication: HTTP ⟹ AuthenticatedHTTP
  authentication:
    transformation: "HTTP ⟹ AuthenticatedHTTP"
    description: "Verify identity, attach to request"
    
    components:
      verify_token:
        input: "Request with Authorization header"
        output: "Request with Identity attached"
        
    targets:
      python:
        pattern: dependency
        template: |
          async def get_current_user(
              authorization: str = Header(None),
              auth_service: AuthService = Depends(get_auth_service),
          ) -> Identity:
              """
              Natural transformation component: HTTP → AuthenticatedHTTP
              
              Naturality: For any handler f,
              AuthenticatedHTTP(f) ∘ verify = verify' ∘ HTTP(f)
              """
              if not authorization:
                  raise HTTPException(
                      status_code=401,
                      detail="Missing authorization header",
                  )
                  
              if not authorization.startswith("Bearer "):
                  raise HTTPException(
                      status_code=401,
                      detail="Invalid authorization format",
                  )
                  
              token = authorization[7:]
              result = await auth_service.verify_token(token)
              
              match result:
                  case Success(identity):
                      return identity
                  case Failure(error):
                      raise HTTPException(
                          status_code=401,
                          detail=str(error),
                      )
                      
        usage: |
          @router.get("/protected")
          async def protected_endpoint(
              current_user: Identity = Depends(get_current_user),
          ):
              # Handler runs in AuthenticatedHTTP context
              pass
              
      typescript:
        pattern: middleware
        template: |
          async function authMiddleware(
            req: Request, 
            res: Response, 
            next: NextFunction
          ) {
            const authHeader = req.headers.authorization;
            
            if (!authHeader?.startsWith('Bearer ')) {
              return res.status(401).json({ error: 'Missing or invalid auth' });
            }
            
            const token = authHeader.slice(7);
            const result = await authService.verifyToken(token);
            
            if (isLeft(result)) {
              return res.status(401).json({ error: result.left.message });
            }
            
            req.user = result.right;
            next();
          }

  # Authorization: AuthenticatedHTTP ⟹ AuthorizedHTTP
  authorization:
    transformation: "AuthenticatedHTTP ⟹ AuthorizedHTTP"
    description: "Check permissions for requested action"
    
    components:
      check_permission:
        input: "(Identity, Permission, Resource)"
        output: "Either[Forbidden, Authorized]"
        
    targets:
      python:
        pattern: dependency_factory
        template: |
          def require_permission(permission: Permission):
              """
              Factory for authorization transformation components.
              
              Returns a dependency that checks the permission.
              """
              async def check(
                  current_user: Identity = Depends(get_current_user),
                  authz_service: AuthzService = Depends(get_authz_service),
              ) -> Identity:
                  result = await authz_service.check_permission(
                      current_user, 
                      permission
                  )
                  
                  match result:
                      case Success(_):
                          return current_user
                      case Failure(error):
                          raise HTTPException(
                              status_code=403,
                              detail=f"Forbidden: {error}",
                          )
                          
              return check
              
        usage: |
          @router.post("/merchants")
          async def create_merchant(
              current_user: Identity = Depends(
                  require_permission(Permission.MERCHANT_CREATE)
              ),
          ):
              # Handler runs in AuthorizedHTTP context
              pass

  # Tenant isolation: AuthorizedHTTP ⟹ TenantScopedHTTP
  tenant_isolation:
    transformation: "AuthorizedHTTP ⟹ TenantScopedHTTP"
    description: "Scope all operations to current tenant"
    
    targets:
      python:
        pattern: context_manager
        template: |
          @asynccontextmanager
          async def tenant_context(tenant_id: TenantId):
              """
              Natural transformation: scope to tenant.
              
              All database queries within this context
              are automatically filtered by tenant.
              """
              token = tenant_context_var.set(tenant_id)
              try:
                  yield
              finally:
                  tenant_context_var.reset(token)
                  
          async def get_tenant_scope(
              current_user: Identity = Depends(get_current_user),
          ) -> TenantId:
              """Extract tenant from identity"""
              return current_user.tenant_id
```

## Observability Transformation Mapping

### Schema

```yaml
# maps/transformations/observability.map.yaml

observability_transformations:
  # Metrics: F ⟹ MetricsF
  metrics:
    transformation: "Handler ⟹ MetricsHandler"
    description: "Add metrics collection to handlers"
    
    components:
      instrument:
        input: "Handler"
        output: "Handler with metrics"
        metrics:
          - counter: "{operation}_total"
          - histogram: "{operation}_duration_seconds"
          
    targets:
      python:
        pattern: decorator
        template: |
          def with_metrics(operation: str):
              """
              Natural transformation: add metrics.
              
              Naturality: metrics collection is uniform across operations.
              """
              counter = Counter(
                  f"{operation}_total",
                  f"Total {operation} calls",
                  ["status"]
              )
              histogram = Histogram(
                  f"{operation}_duration_seconds",
                  f"{operation} duration",
              )
              
              def decorator(func):
                  @wraps(func)
                  async def wrapper(*args, **kwargs):
                      start = time.perf_counter()
                      try:
                          result = await func(*args, **kwargs)
                          counter.labels(status="success").inc()
                          return result
                      except Exception as e:
                          counter.labels(status="error").inc()
                          raise
                      finally:
                          histogram.observe(time.perf_counter() - start)
                  return wrapper
              return decorator
              
        usage: |
          @with_metrics("create_merchant")
          async def create_merchant(input: CreateMerchantInput):
              ...

  # Tracing: F ⟹ TracedF
  tracing:
    transformation: "Handler ⟹ TracedHandler"
    description: "Add distributed tracing spans"
    
    components:
      trace:
        input: "Handler"
        output: "Handler with span"
        
    targets:
      python:
        pattern: decorator
        template: |
          def with_tracing(operation: str):
              """Natural transformation: add tracing span."""
              def decorator(func):
                  @wraps(func)
                  async def wrapper(*args, **kwargs):
                      with tracer.start_as_current_span(operation) as span:
                          span.set_attribute("operation", operation)
                          try:
                              result = await func(*args, **kwargs)
                              span.set_status(StatusCode.OK)
                              return result
                          except Exception as e:
                              span.set_status(StatusCode.ERROR, str(e))
                              span.record_exception(e)
                              raise
                  return wrapper
              return decorator

  # Logging: F ⟹ LoggedF
  logging:
    transformation: "Handler ⟹ LoggedHandler"
    description: "Add structured logging"
    
    targets:
      python:
        pattern: decorator
        template: |
          def with_logging(operation: str):
              """Natural transformation: add logging."""
              def decorator(func):
                  @wraps(func)
                  async def wrapper(*args, **kwargs):
                      logger.info(
                          f"Starting {operation}",
                          extra={"operation": operation}
                      )
                      try:
                          result = await func(*args, **kwargs)
                          logger.info(
                              f"Completed {operation}",
                              extra={"operation": operation}
                          )
                          return result
                      except Exception as e:
                          logger.error(
                              f"Failed {operation}: {e}",
                              extra={"operation": operation},
                              exc_info=True,
                          )
                          raise
                  return wrapper
              return decorator

  # Combined observability
  combined:
    composition: "Logged ∘ Traced ∘ Metrics"
    targets:
      python:
        template: |
          def observable(operation: str):
              """Compose all observability transformations."""
              def decorator(func):
                  @with_logging(operation)
                  @with_tracing(operation)
                  @with_metrics(operation)
                  @wraps(func)
                  async def wrapper(*args, **kwargs):
                      return await func(*args, **kwargs)
                  return wrapper
              return decorator
```

## Validation

### Completeness Checks

```yaml
completeness:
  - all_middleware_mapped
  - auth_chain_complete
  - observability_covers_operations
```

### Consistency Checks

```yaml
consistency:
  - naturality_squares_commute
  - composition_order_correct
  - transformations_uniform
```

## Next Skills

Output feeds into:
- `module-mapper`
- `maps-validator`
