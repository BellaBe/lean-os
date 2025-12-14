---
name: build-functors
description: |
  Define functors from domain to target categories. Uses targets.yaml to
  determine which functors to create. Maps domain objects and morphisms
  to target representations. Use when: mapping domain to API, persistence,
  events; formalizing structural transformations.
---

# Build Functors

Define structure-preserving maps from Domain to target categories.

## Categorical Foundation

A functor F: C → D consists of:
- **Object map**: F(A) for each object A in C
- **Morphism map**: F(f) : F(A) → F(B) for each f : A → B
- **Preserves identity**: F(id_A) = id_{F(A)}
- **Preserves composition**: F(g ∘ f) = F(g) ∘ F(f)

## Input

- `artifacts/v{N}/build/category.yaml`
- `artifacts/v{N}/targets.yaml`

## Output

`artifacts/v{N}/build/functors.yaml`

## Process

1. **Read targets.yaml** — Which targets are enabled?
2. **For each enabled target** — Define functor
3. **Map objects** — Domain types to target types
4. **Map morphisms** — Domain ops to target ops
5. **State preservation laws**

## Conditional Functor Creation

```python
if targets.api.enabled:
    create F_api: Domain → Api
    
if targets.persistence.enabled:
    create F_persist: Domain → Storage
    
if targets.events.enabled:
    create F_events: Domain → Events
```

Only enabled targets get functors. Disabled targets are skipped.

## Functor Definitions

### F_api: Domain → Api

Maps domain to API layer (REST, GraphQL, gRPC).

```yaml
- id: "F_api"
  enabled: true  # from targets.api.enabled
  source: "Domain"
  target: "Api"
  
  target_category:
    description: "API contracts and endpoints"
    objects:
      # Request types (from domain inputs)
      - id: "CreateUserRequest"
        source: "CreateUserInput"
        transform: "Add validation annotations, JSON schema"
        
      # Response types (from domain entities)
      - id: "UserResponse"
        source: "User"
        transform: "Select public fields, format dates"
        
      # Error responses
      - id: "ErrorResponse"
        source: "AppError"
        transform: "Map to HTTP status + message"
        
    morphisms:
      # Endpoints
      - id: "POST /users"
        source: "create_user"
        hom: "CreateUserRequest → UserResponse"
        
      - id: "GET /users/{id}"
        source: "get_user"
        hom: "UserId → UserResponse"
        
  object_map:
    - from: "CreateUserInput"
      to: "CreateUserRequest"
      transform: |
        Add @validate decorators
        Generate JSON schema
        
    - from: "User"
      to: "UserResponse"
      transform: |
        Select: id, email, status, created_at
        Format: datetime → ISO 8601 string
        
    - from: "AppError"
      to: "ErrorResponse"
      transform: |
        UserError.NotFound → 404 + "User not found"
        UserError.AlreadyExists → 409 + "Email taken"
        ValidationError → 400 + field errors
        
  morphism_map:
    - from: "create_user"
      to: "POST /users"
      wrapping: |
        deserialize request
        → call domain morphism
        → serialize response
        → handle errors
        
    - from: "get_user"
      to: "GET /users/{id}"
      wrapping: |
        parse path parameter
        → call domain morphism
        → serialize response
        → handle errors
        
  preserves:
    identity:
      statement: "F_api(id_A) = id_{F_api(A)}"
      explanation: "Identity endpoint returns input unchanged"
      status: stated
      
    composition:
      statement: "F_api(g ∘ f) = F_api(g) ∘ F_api(f)"
      explanation: "Endpoint composition matches domain composition"
      status: stated
```

### F_persist: Domain → Storage

Maps domain to persistence layer.

```yaml
- id: "F_persist"
  enabled: true  # from targets.persistence.enabled
  source: "Domain"
  target: "Storage"
  
  config:
    type: "sql"  # from targets.persistence.type
    provider: "postgresql"  # from targets.persistence.provider
    
  target_category:
    description: "Database models and queries"
    objects:
      - id: "UserModel"
        source: "User"
        transform: "Map to table columns"
        
      - id: "UserRow"
        source: "User"
        transform: "Raw database row"
        
    morphisms:
      - id: "insert_user"
        source: "create_user"
        hom: "UserModel → IO[UserId]"
        
      - id: "select_user_by_id"
        source: "get_user"
        hom: "UserId → IO[Option[UserModel]]"
        
  object_map:
    - from: "User"
      to: "UserModel"
      transform: |
        id: UUID PRIMARY KEY
        email: VARCHAR(255) UNIQUE NOT NULL
        status: VARCHAR(50) NOT NULL
        created_at: TIMESTAMP WITH TIME ZONE
        
    - from: "UserId"
      to: "UserId"
      transform: "identity"  # UUIDs pass through
      
  morphism_map:
    - from: "create_user"
      to: "insert_user"
      wrapping: |
        to_model: User → UserModel
        → execute INSERT
        → return id
        
    - from: "get_user"
      to: "select_user_by_id"
      wrapping: |
        execute SELECT
        → from_model: Option[UserModel] → Option[User]
        → option_to_either: Option → Either[NotFound, _]
        
  preserves:
    identity:
      statement: "F_persist(id_A) = id_{F_persist(A)}"
      status: stated
      
    composition:
      statement: "F_persist(g ∘ f) = F_persist(g) ∘ F_persist(f)"
      status: stated
```

### F_events: Domain → Events

Maps domain to event-driven layer (if enabled).

```yaml
- id: "F_events"
  enabled: false  # from targets.events.enabled
  # Not generated when disabled
```

When enabled:

```yaml
- id: "F_events"
  enabled: true
  source: "Domain"
  target: "Events"
  
  config:
    style: "async"  # from targets.events.style
    broker: "nats"  # from targets.events.broker
    
  target_category:
    description: "Event schemas and handlers"
    objects:
      - id: "UserCreatedEvent"
        source: "User"
        transform: "Event payload with metadata"
        
      - id: "UserStatusChangedEvent"
        source: "Tuple[UserId, UserStatus, UserStatus]"
        transform: "Event with old and new status"
        
    morphisms:
      - id: "publish_user_created"
        source: "create_user"
        hom: "User → IO[Unit]"
        
      - id: "handle_user_created"
        source: null  # External trigger
        hom: "UserCreatedEvent → IO[Unit]"
        
  object_map:
    - from: "User"
      to: "UserCreatedEvent"
      transform: |
        event_id: UUID (generated)
        timestamp: DateTime (now)
        payload: { user_id, email }
        
  morphism_map:
    - from: "create_user"
      to: "publish_user_created"
      wrapping: |
        After successful create:
        → build event from User
        → publish to "users.created" topic
```

## Output Format

```yaml
version: "1.0"

functors:
  # ========================================
  # F_api: Domain → Api
  # ========================================
  - id: "F_api"
    enabled: true
    source: "Domain"
    target: "Api"
    
    config:
      style: "rest"
      framework: "fastapi"
      prefix: "/api/v1"
      
    target_category:
      objects:
        - "CreateUserRequest"
        - "UserResponse"
        - "ErrorResponse"
        - "UserListResponse"
        
      morphisms:
        - id: "POST /api/v1/users"
          hom: "CreateUserRequest → UserResponse"
        - id: "GET /api/v1/users/{id}"
          hom: "UserId → UserResponse"
        - id: "GET /api/v1/users"
          hom: "UserFilter → UserListResponse"
          
    object_map:
      - from: "CreateUserInput"
        to: "CreateUserRequest"
        
      - from: "User"
        to: "UserResponse"
        fields:
          - from: "id"
            to: "id"
          - from: "email"
            to: "email"
          - from: "status"
            to: "status"
          - from: "created_at"
            to: "created_at"
            transform: "ISO 8601"
            
      - from: "AppError"
        to: "ErrorResponse"
        mapping:
          - error: "UserError.NotFound"
            status: 404
            message: "User not found"
          - error: "UserError.AlreadyExists"
            status: 409
            message: "Email already registered"
          - error: "ValidationError"
            status: 400
            message: "Validation failed"
            
    morphism_map:
      - from: "create_user"
        to: "POST /api/v1/users"
        
      - from: "get_user"
        to: "GET /api/v1/users/{id}"
        
    preserves:
      identity:
        statement: "F_api(id_A) = id_{F_api(A)}"
        status: stated
      composition:
        statement: "F_api(g ∘ f) = F_api(g) ∘ F_api(f)"
        status: stated
        
  # ========================================
  # F_persist: Domain → Storage
  # ========================================
  - id: "F_persist"
    enabled: true
    source: "Domain"
    target: "Storage"
    
    config:
      type: "sql"
      provider: "postgresql"
      migrations: true
      
    target_category:
      objects:
        - "UserModel"
        - "OrderModel"
        
      morphisms:
        - id: "insert_user"
          hom: "UserModel → IO[UserId]"
        - id: "select_user"
          hom: "UserId → IO[Option[UserModel]]"
        - id: "update_user"
          hom: "UserModel → IO[Unit]"
        - id: "delete_user"
          hom: "UserId → IO[Unit]"
          
    object_map:
      - from: "User"
        to: "UserModel"
        table: "users"
        columns:
          - from: "id"
            to: "id"
            type: "UUID"
            constraints: ["PRIMARY KEY"]
          - from: "email"
            to: "email"
            type: "VARCHAR(255)"
            constraints: ["UNIQUE", "NOT NULL"]
          - from: "status"
            to: "status"
            type: "VARCHAR(50)"
            constraints: ["NOT NULL"]
          - from: "created_at"
            to: "created_at"
            type: "TIMESTAMP WITH TIME ZONE"
            constraints: ["NOT NULL"]
            
    morphism_map:
      - from: "create_user"
        to: "insert_user"
        query: "INSERT INTO users (...) VALUES (...) RETURNING id"
        
      - from: "get_user"
        to: "select_user"
        query: "SELECT * FROM users WHERE id = $1"
        
    preserves:
      identity:
        statement: "F_persist(id_A) = id_{F_persist(A)}"
        status: stated
      composition:
        statement: "F_persist(g ∘ f) = F_persist(g) ∘ F_persist(f)"
        status: stated
        
  # ========================================
  # F_events: Domain → Events (disabled)
  # ========================================
  - id: "F_events"
    enabled: false
    note: "Events disabled in targets.yaml"

# ========================================
# Validation
# ========================================
validation:
  functors_generated:
    F_api: true
    F_persist: true
    F_events: false
    
  coverage:
    domain_objects_mapped:
      F_api: "8/10"  # Some internal types not exposed
      F_persist: "5/10"  # Only persistent entities
      
    domain_morphisms_mapped:
      F_api: "12/12"
      F_persist: "8/12"  # Not all morphisms touch DB
```

## Disabled Functors

When a target is disabled in targets.yaml:

```yaml
- id: "F_events"
  enabled: false
  note: "Events disabled in targets.yaml"
```

The functor is listed but not defined. Gen phase skips disabled functors.

## Validation Rules

1. **Only enabled targets**: Functor only if target enabled
2. **Complete object map**: All exposed domain objects mapped
3. **Complete morphism map**: All relevant morphisms mapped
4. **Preservation stated**: Identity and composition laws stated
5. **Config matches targets**: Functor config from targets.yaml

## Validation Checklist

- [ ] Each enabled target has corresponding functor
- [ ] Each disabled target has functor with enabled: false
- [ ] Object maps reference valid domain objects
- [ ] Morphism maps reference valid domain morphisms
- [ ] Preservation laws stated for each enabled functor
- [ ] Config values match targets.yaml

## Do NOT

- **Create functor for disabled target** — Just stub with enabled: false
- **Map internal-only types to API** — Only public types
- **Skip preservation laws** — Must be stated even if trivial
- **Include implementation code** — Just structure and mappings
