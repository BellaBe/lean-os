---
name: shared-modules
description: |
  Shared Modules: Cross-cutting constructs used by multiple modules.
  Shared items are detected automatically based on usage patterns.
  
  This is not a "level" but a cross-cutting concern that spans levels 0-9.
  
  Scope: shared items are used by 2+ modules
  Location: generated code goes to shared/ directory
  
  UNIVERSAL: Works for any domain.
---

# Shared Modules

Cross-cutting constructs that serve multiple modules.

## Principle

An item is **shared** if it's traced by items from 2+ different modules.

```
Shared(item) ⟺ |{module(consumer) : consumer traces to item}| ≥ 2
```

Shared items form the "common vocabulary" of the system.

## Detection

Scope is computed, not declared:

```python
def detect_scope(item, all_items):
    consumers = [i for i in all_items if traces_to(i, item)]
    
    if not consumers:
        return "internal"
    
    modules = set(get_module(c) for c in consumers)
    
    if len(modules) >= 2:
        return "shared"
    else:
        return "module"
```

## Shared Items by Level

### Level 0: Universal Primitives

All Level 0 items are inherently shared (they're the foundation):

```yaml
level_0_shared:
  types:
    all_shared: true
    items:
      - Bool, String, Int, Nat, Float, Decimal
      - DateTime, Date, Duration
      - UUID, Bytes, Json, Unit
      - Option[A], List[A], Set[A], Map[K,V]
      
  effects:
    all_shared: true
    items:
      - IO[A], Either[E,A], Reader[R,A], State[S,A]
      
  constraints:
    all_shared: true
    items:
      - NonEmptyString, Email, Url, Money, Percentage
      - PositiveInt, NonNegativeInt
```

### Level 1: Shared Entities

Cross-cutting domain types:

```yaml
shared_entities:
  # Audit metadata (embedded in many entities)
  - id: "entity.shared.AuditInfo"
    scope: "shared"
    type_params: []
    definition:
      type: "product"
      fields:
        - {name: "created_at", type: "DateTime"}
        - {name: "created_by", type: "Option[UserId]"}
        - {name: "updated_at", type: "DateTime"}
        - {name: "updated_by", type: "Option[UserId]"}
    used_by:
      - {ref: "entity.Customer", module: "customers"}
      - {ref: "entity.Order", module: "orders"}
      - {ref: "entity.Product", module: "inventory"}
      
  # Pagination request
  - id: "entity.shared.Pagination"
    scope: "shared"
    definition:
      type: "product"
      fields:
        - {name: "page", type: "PositiveInt", default: 1}
        - {name: "per_page", type: "PositiveInt", default: 25}
        
  # Paginated result (polymorphic)
  - id: "entity.shared.PaginatedResult"
    scope: "shared"
    type_params:
      - {name: "A"}
    definition:
      type: "product"
      fields:
        - {name: "items", type: "List[A]"}
        - {name: "pagination", type: "Pagination"}
        - {name: "total", type: "Nat"}
        - {name: "has_next", type: "Bool"}
        - {name: "has_prev", type: "Bool"}
        
  # Sort specification
  - id: "entity.shared.SortSpec"
    scope: "shared"
    definition:
      type: "product"
      fields:
        - {name: "field", type: "String"}
        - {name: "direction", type: "SortDirection"}
        
  - id: "enum.shared.SortDirection"
    scope: "shared"
    definition:
      type: "coproduct"
      variants: ["Asc", "Desc"]
```

### Level 1: Shared Error Types

Base error algebra:

```yaml
shared_errors:
  # Base error (all domain errors extend this)
  - id: "entity.shared.AppError"
    scope: "shared"
    definition:
      type: "coproduct"
      variants:
        NotFound:
          fields:
            - {name: "entity", type: "String"}
            - {name: "id", type: "String"}
            
        ValidationError:
          fields:
            - {name: "field", type: "String"}
            - {name: "message", type: "String"}
            - {name: "code", type: "String"}
            
        ValidationErrors:
          fields:
            - {name: "errors", type: "List[ValidationError]"}
            
        Unauthorized:
          fields:
            - {name: "reason", type: "String"}
            
        Forbidden:
          fields:
            - {name: "action", type: "String"}
            - {name: "resource", type: "String"}
            
        Conflict:
          fields:
            - {name: "message", type: "String"}
            
        RateLimited:
          fields:
            - {name: "retry_after", type: "Duration"}
            
        Internal:
          fields:
            - {name: "message", type: "String"}
            - {name: "cause", type: "Option[String]"}
```

### Level 2: Shared Morphisms

Utility functions used across modules:

```yaml
shared_morphisms:
  # Validation
  - id: "morphism.shared.validate_email"
    scope: "shared"
    definition:
      domain: "String"
      codomain: "Either[ValidationError, Email]"
      effects: []
      
  - id: "morphism.shared.validate_not_empty"
    scope: "shared"
    type_params:
      - {name: "A"}
    definition:
      domain: "List[A]"
      codomain: "Either[ValidationError, NonEmptyList[A]]"
      effects: []
      
  - id: "morphism.shared.validate_positive"
    scope: "shared"
    definition:
      domain: "Int"
      codomain: "Either[ValidationError, PositiveInt]"
      effects: []
      
  # Error mapping
  - id: "morphism.shared.map_error"
    scope: "shared"
    type_params:
      - {name: "E1"}
      - {name: "E2"}
      - {name: "A"}
    definition:
      domain: "(E1 → E2, Either[E1, A])"
      codomain: "Either[E2, A]"
      effects: []
      
  # Pagination
  - id: "morphism.shared.paginate"
    scope: "shared"
    type_params:
      - {name: "A"}
    definition:
      domain: "(List[A], Pagination, Nat)"
      codomain: "PaginatedResult[A]"
      effects: []
      
  # Retry with backoff
  - id: "morphism.shared.with_retry"
    scope: "shared"
    type_params:
      - {name: "A"}
    definition:
      domain: "(App[A], RetryPolicy)"
      codomain: "App[A]"
      effects: [IO]
      note: "Wraps operation with retry logic"
```

### Level 3: Shared Module Interfaces

Generic interfaces implemented by concrete modules:

```yaml
shared_interfaces:
  # Generic repository
  - id: "module.shared.IRepository"
    scope: "shared"
    type_params:
      - {name: "E", constraint: "Entity"}
      - {name: "Id", constraint: "Identifier"}
    definition:
      kind: "interface"
      operations:
        - name: "get"
          signature: "Id → App[E]"
          
        - name: "get_optional"
          signature: "Id → App[Option[E]]"
          
        - name: "save"
          signature: "E → App[E]"
          
        - name: "delete"
          signature: "Id → App[Unit]"
          
        - name: "exists"
          signature: "Id → App[Bool]"
          
        - name: "list"
          signature: "Pagination → App[PaginatedResult[E]]"
          
  # Generic CRUD service
  - id: "module.shared.ICRUDService"
    scope: "shared"
    type_params:
      - {name: "E", constraint: "Entity"}
      - {name: "Id", constraint: "Identifier"}
      - {name: "CreateDTO"}
      - {name: "UpdateDTO"}
    definition:
      kind: "interface"
      operations:
        - name: "create"
          signature: "CreateDTO → App[E]"
          
        - name: "get"
          signature: "Id → App[E]"
          
        - name: "update"
          signature: "(Id, UpdateDTO) → App[E]"
          
        - name: "delete"
          signature: "Id → App[Unit]"
          
        - name: "list"
          signature: "Pagination → App[PaginatedResult[E]]"
          
  # Event publisher interface
  - id: "module.shared.IEventPublisher"
    scope: "shared"
    type_params:
      - {name: "E", constraint: "DomainEvent"}
    definition:
      kind: "interface"
      operations:
        - name: "publish"
          signature: "E → App[Unit]"
          
        - name: "publish_batch"
          signature: "List[E] → App[Unit]"
```

### Level 4: Shared Monads

The App monad stack is shared:

```yaml
shared_monads:
  - id: "monad.shared.App"
    scope: "shared"
    definition:
      stack:
        - {monad: "IO"}
        - {transformer: "EitherT", param: "AppError"}
      expanded: "IO[Either[AppError, A]]"
      
  - id: "monad.shared.AppReader"
    scope: "shared"
    definition:
      stack:
        - {transformer: "ReaderT", param: "Dependencies"}
        - {monad: "IO"}
        - {transformer: "EitherT", param: "AppError"}
      expanded: "Dependencies → IO[Either[AppError, A]]"
      note: "App with dependency injection"
```

### Level 5: Shared Functors

Generic functors:

```yaml
shared_functors:
  # Generic HTTP functor
  - id: "functor.shared.HTTP"
    scope: "shared"
    type_params:
      - {name: "E", constraint: "Entity"}
    definition:
      object_map: "E → (CreateRequest[E], UpdateRequest[E], Response[E])"
      morphism_map: "op → handler"
      
  # Generic Repository functor
  - id: "functor.shared.Repository"
    scope: "shared"
    type_params:
      - {name: "E", constraint: "Entity"}
    definition:
      source: "Domain[E]"
      target: "Storage[E]"
      object_map: "E → Model[E]"
```

### Level 7: Shared Transformations (Middleware)

All middleware is shared by definition:

```yaml
shared_transformations:
  # Request tracking
  - id: "transformation.shared.RequestId"
    scope: "shared"
    definition:
      source: "Handler"
      target: "TrackedHandler"
      implementation: |
        1. Generate UUID for request
        2. Attach to context
        3. Add to response headers
        
  # Logging
  - id: "transformation.shared.Logging"
    scope: "shared"
    definition:
      source: "Handler"
      target: "LoggedHandler"
      implementation: |
        1. Log request (method, path, headers)
        2. Call inner handler
        3. Log response (status, duration)
        4. Log errors with stack trace
        
  # Metrics
  - id: "transformation.shared.Metrics"
    scope: "shared"
    definition:
      source: "Handler"
      target: "MetricsHandler"
      implementation: |
        1. Start timer
        2. Call inner handler
        3. Record: request_count, request_duration, response_status
        
  # Distributed tracing
  - id: "transformation.shared.Tracing"
    scope: "shared"
    definition:
      source: "Handler"
      target: "TracedHandler"
      implementation: |
        1. Extract trace context from headers (or create new)
        2. Create span for this request
        3. Call inner handler
        4. Close span with status
        
  # Authentication
  - id: "transformation.shared.Auth"
    scope: "shared"
    definition:
      source: "Handler"
      target: "AuthenticatedHandler"
      implementation: |
        1. Extract token from Authorization header
        2. Validate token (signature, expiry)
        3. Decode identity
        4. Attach to context OR return 401
        
  # Rate limiting
  - id: "transformation.shared.RateLimit"
    scope: "shared"
    definition:
      source: "Handler"
      target: "RateLimitedHandler"
      implementation: |
        1. Extract rate limit key (IP, user, API key)
        2. Check counter in cache
        3. If exceeded, return 429 with Retry-After
        4. Increment counter
        5. Call inner handler
        
  # CORS
  - id: "transformation.shared.CORS"
    scope: "shared"
    definition:
      source: "Handler"
      target: "CORSHandler"
      implementation: |
        1. Check Origin header against allowed origins
        2. Handle OPTIONS preflight
        3. Add CORS headers to response
```

## Code Generation

Shared items generate to `shared/` directory:

```yaml
code_structure:
  generated/{language}/src/{project}/
    shared/
      # Level 1: Types
      types/
        __init__.py
        audit.py           # AuditInfo
        pagination.py      # Pagination, PaginatedResult
        sort.py            # SortSpec, SortDirection
        
      # Level 1: Errors  
      errors/
        __init__.py
        base.py            # AppError and variants
        
      # Level 2: Utilities
      validation/
        __init__.py
        email.py           # validate_email
        common.py          # validate_not_empty, validate_positive
        
      utils/
        __init__.py
        pagination.py      # paginate()
        retry.py           # with_retry()
        errors.py          # map_error()
        
      # Level 3: Interfaces
      interfaces/
        __init__.py
        repository.py      # IRepository[E, Id]
        service.py         # ICRUDService[...]
        events.py          # IEventPublisher[E]
        
      # Level 4: Monads
      monads/
        __init__.py
        app.py             # App, AppReader
        result.py          # Result helpers
        
      # Level 7: Middleware
      middleware/
        __init__.py
        request_id.py      # RequestId
        logging.py         # Logging
        metrics.py         # Metrics
        tracing.py         # Tracing
        auth.py            # Auth
        rate_limit.py      # RateLimit
        cors.py            # CORS
        chain.py           # compose_middleware()
```

## Validation Rules

```yaml
validation:
  shared_usage:
    rule: "∀ scope=shared: used_by has 2+ unique modules"
    critical: true
    
  shared_stability:
    rule: "∀ scope=shared: traces only to shared or level-0"
    description: "Shared items should not depend on module-specific items"
    severity: "warning"
    
  shared_location:
    rule: "∀ scope=shared code: generated to shared/ directory"
    critical: true
    
  interface_implementation:
    rule: "∀ interface: at least one implementation exists"
    critical: true
    
  generic_instantiation:
    rule: "∀ generic with type_params: used via instantiation"
    description: "Generics should be instantiated, not used directly"
```

## Process Integration

```yaml
process:
  # After items enumerated, before code generation
  step_detect_scope:
    timing: "After step_enumerate, before step_generate"
    action: |
      for item in all_items:
          item.scope = detect_scope(item, all_items)
          if item.scope == "shared":
              item.used_by = find_consumers(item, all_items)
              
  step_validate_shared:
    timing: "After step_detect_scope"
    action: |
      for item in items.where(scope="shared"):
          assert len(unique_modules(item.used_by)) >= 2
          assert not depends_on_module_scoped(item)
          
  step_generate_shared:
    timing: "During code generation, before module code"
    action: |
      # Generate shared items first (modules depend on them)
      for item in items.where(scope="shared"):
          generate_to("shared/", item)
```

## Example: Complete Shared Manifest

```yaml
# Excerpt from level-1.manifest.yaml showing shared items

items:
  - id: "entity.shared.Pagination"
    name: "Pagination"
    kind: "entity"
    scope: "shared"
    used_by:
      - {ref: "morphism.customers.list_customers", module: "customers"}
      - {ref: "morphism.orders.list_orders", module: "orders"}
      - {ref: "morphism.products.list_products", module: "products"}
    traces:
      - ref: "level-0.type.PositiveInt"
    definition:
      type: "product"
      fields:
        - {name: "page", type: "PositiveInt"}
        - {name: "per_page", type: "PositiveInt"}
    artifacts:
      - path: "generated/python/src/project/shared/types/pagination.py"
    status: "validated"
    
  - id: "entity.shared.PaginatedResult"
    name: "PaginatedResult"
    kind: "entity"
    scope: "shared"
    type_params:
      - {name: "A"}
    used_by:
      - {ref: "morphism.customers.list_customers", module: "customers"}
      - {ref: "morphism.orders.list_orders", module: "orders"}
    traces:
      - ref: "level-0.type.List"
      - ref: "entity.shared.Pagination"
    definition:
      type: "product"
      fields:
        - {name: "items", type: "List[A]"}
        - {name: "pagination", type: "Pagination"}
        - {name: "total", type: "Nat"}
    artifacts:
      - path: "generated/python/src/project/shared/types/pagination.py"
    status: "validated"
    
  - id: "entity.customers.Customer"
    name: "Customer"
    kind: "entity"
    scope: "module"  # Only used by customers module
    traces:
      - ref: "level-0.identifier.CustomerId"
      - ref: "level-0.constraint.Email"
      - ref: "entity.shared.AuditInfo"  # Uses shared!
    definition:
      type: "product"
      fields:
        - {name: "id", type: "CustomerId"}
        - {name: "email", type: "Email"}
        - {name: "audit", type: "AuditInfo"}
    artifacts:
      - path: "generated/python/src/project/modules/customers/entities/customer.py"
    status: "validated"

counts:
  total: 15
  by_scope:
    shared: 5
    module: 10
    internal: 0
```
