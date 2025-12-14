---
name: gen-maps
description: |
  Generate code maps - lightweight specifications of what code will look like.
  Code maps can be verified BEFORE generating actual code, catching type mismatches,
  wrong arguments, and missing imports early. Use when: after gen-types, before gen-code.
---

# Gen Maps

Generate verifiable code maps before generating actual source code.

## Why Code Maps?

**Problem:** Generating 5000+ lines of code, then discovering type mismatches or wrong function arguments wastes cycles and produces broken code.

**Solution:** Generate 300-line map files that specify:
- What functions exist
- What arguments they take
- What they call
- What they import

Verify these maps against type definitions BEFORE generating full code.

## CRITICAL RULE

Code maps are **specifications**, not code. They describe structure and can be formally verified.

## Input

- `artifacts/v{N}/build/category.yaml` — Morphisms to implement
- `artifacts/v{N}/build/effects.yaml` — Effect types
- `artifacts/v{N}/gen/types-manifest.yaml` — Generated type locations
- Generated type files from gen-types

## Output

- `artifacts/v{N}/gen/maps/operations/*.map.yaml`
- `artifacts/v{N}/gen/maps/handlers/*.map.yaml`
- `artifacts/v{N}/gen/maps/repositories/*.map.yaml`
- `artifacts/v{N}/gen/maps-manifest.yaml`

## Code Map Format

### Operation Map

```yaml
# maps/operations/user_ops.map.yaml
version: "1.0"
module: src.domain.operations.user_ops

imports:
  - from: "..effects"
    names: [App, Env]
  - from: "..effects.result"
    names: [Result, ok, err]
  - from: "..effects.errors"
    names: [UserNotFound, UserAlreadyExists]
  - from: "..types"
    names: [User, UserId, CreateUserInput, UserStatus]
  - from: "..types.ids"
    names: [UserId]
  - from: "datetime"
    names: [datetime]
  - from: "uuid"
    names: [uuid4]

functions:
  - name: create_user
    signature:
      params:
        - name: input
          type: CreateUserInput
      returns: App[User]
    
    env_access:
      - path: env.repositories.users
        type: UserRepository
        alias: repo
    
    # FIELD ACCESS DECLARATIONS (NEW)
    # Every field access must be declared and will be verified
    field_accesses:
      - variable: input
        type: CreateUserInput
        field: email
        field_type: str
        # Proves: CreateUserInput has field 'email' of type 'str'
      
      - variable: input
        type: CreateUserInput
        field: password
        field_type: str
    
    body:
      # Each step with exact types
      steps:
        - action: call
          target: repo.get_by_email
          args:
            - name: email
              value: input.email        # Uses declared field access
              type: str
          returns:
            type: Optional[User]
            bind: existing
        
        - action: condition
          test: existing is not None
          if_true:
            action: return
            value: err(UserAlreadyExists(...))
        
        - action: construct
          type: User
          args:
            id: UserId(uuid4())
            email: input.email          # Uses declared field access
            status: UserStatus.PENDING
            created_at: datetime.utcnow()
          bind: user
          # Constructor args verification
          constructor_field_accesses:
            - field: id
              value_type: UserId
            - field: email
              value_type: str
            - field: status
              value_type: UserStatus
            - field: created_at
              value_type: datetime
        
        - action: call
          target: repo.save
          args:
            - name: user
              value: user
              type: User
          returns:
            type: User
            bind: saved
        
        - action: return
          value: ok(saved)
    
    traces_to: build/category.yaml#morphisms.create_user

  - name: get_user_email_domain
    signature:
      params:
        - name: user
          type: User
      returns: str
    
    # Chained field access example
    field_accesses:
      - variable: user
        type: User
        field: email
        field_type: str
      
      # For nested access like user.org.name
      - variable: user
        type: User
        field: org_id
        field_type: OrgId
    
    body:
      steps:
        - action: call
          target: user.email.split
          args:
            - name: sep
              value: "@"
              type: str
          returns:
            type: list[str]
            bind: parts
        
        - action: return
          value: parts[1]
```

### Field Access Declaration Rules

Every access to an object's field MUST be declared in `field_accesses`:

```yaml
field_accesses:
  # Simple field access: input.email
  - variable: input           # Variable name in scope
    type: CreateUserInput     # Declared type of variable
    field: email              # Field being accessed
    field_type: str           # Expected type of field
  
  # Nested field access: user.profile.avatar_url
  - variable: user
    type: User
    field: profile
    field_type: UserProfile
  
  - variable: user.profile    # Chained access
    type: UserProfile
    field: avatar_url
    field_type: Optional[str]
```

**Why this matters:**
- Prevents `AttributeError` at runtime
- Catches typos (e.g., `input.emial` vs `input.email`)
- Verifies type has the field before generating code
- Documents data flow through the function

  - name: get_user
    signature:
      params:
        - name: user_id
          type: UserId
      returns: App[User]
    
    env_access:
      - path: env.repositories.users
        type: UserRepository
        alias: repo
    
    body:
      steps:
        - action: call
          target: repo.get_by_id
          args:
            - name: user_id
              value: user_id
              type: UserId
          returns:
            type: Optional[User]
            bind: user
        
        - action: condition
          test: user is None
          if_true:
            action: return
            value: err(UserNotFound(...))
        
        - action: return
          value: ok(user)
    
    traces_to: build/category.yaml#morphisms.get_user
```

### Handler Map

```yaml
# maps/handlers/user_handlers.map.yaml
version: "1.0"
module: src.api.handlers.user_handlers

imports:
  - from: "fastapi"
    names: [APIRouter, Depends, HTTPException]
  - from: "uuid"
    names: [UUID]
  - from: "...domain.effects"
    names: [App, Env]
  - from: "...domain.effects.result"
    names: [Ok, Err]
  - from: "...domain.operations.user_ops"
    names: [create_user, get_user]
  - from: "...domain.types"
    names: [CreateUserInput]
  - from: "..schemas.requests"
    names: [CreateUserRequest]
  - from: "..schemas.responses"
    names: [UserResponse]
  - from: "..dependencies"
    names: [get_env]

router:
  prefix: /users
  tags: [users]

endpoints:
  - name: create_user_handler
    decorator: router.post("/", response_model=UserResponse, status_code=201)
    signature:
      params:
        - name: request
          type: CreateUserRequest
        - name: env
          type: Env
          default: Depends(get_env)
      returns: UserResponse
    
    body:
      steps:
        - action: construct
          type: CreateUserInput
          args:
            email: request.email
            password: request.password
          bind: domain_input
        
        - action: call
          target: create_user
          args:
            - name: input
              value: domain_input
              type: CreateUserInput
          returns:
            type: App[User]
            bind: app
        
        - action: call
          target: app.run
          args:
            - name: env
              value: env
              type: Env
          returns:
            type: Result[AppError, User]
            bind: result
        
        - action: match
          on: result
          cases:
            - pattern: Ok(user)
              body:
                action: return
                value: UserResponse.from_domain(user)
            - pattern: Err(error)
              body:
                action: raise
                value: HTTPException(status_code=error.http_status, detail=...)
    
    traces_to: build/functors.yaml#F_api.create_user
```

### Repository Interface Map

```yaml
# maps/repositories/user_repository.map.yaml
version: "1.0"
module: src.domain.interfaces.repositories

protocols:
  - name: UserRepository
    description: Repository protocol for User aggregate
    
    methods:
      - name: get_by_id
        signature:
          params:
            - name: user_id
              type: UserId
          returns: Optional[User]
        async: true
        
      - name: get_by_email
        signature:
          params:
            - name: email
              type: str
          returns: Optional[User]
        async: true
        
      - name: save
        signature:
          params:
            - name: user
              type: User
          returns: User
        async: true
        
      - name: delete
        signature:
          params:
            - name: user_id
              type: UserId
          returns: bool
        async: true
```

## Verification Rules

### Rule 1: Argument Types Match

For every call in a code map:
```yaml
- action: call
  target: repo.get_by_email
  args:
    - name: email
      value: input.email
      type: str
```

Verify:
1. `repo` has type `UserRepository` (from env_access)
2. `UserRepository.get_by_email` exists (from repository map)
3. `UserRepository.get_by_email` takes `email: str` (signature match)
4. `input.email` is `str` (from CreateUserInput definition)

### Rule 2: Return Types Match

```yaml
returns:
  type: Optional[User]
  bind: existing
```

Verify:
1. `UserRepository.get_by_email` returns `Optional[User]`
2. Later uses of `existing` treat it as `Optional[User]`

### Rule 3: Imports Cover Usage

For every type/function used in the map, verify it's in imports:
```python
used_names = extract_all_names(map)
imported_names = extract_imports(map)
assert used_names.issubset(imported_names)
```

### Rule 4: Env Access Valid

```yaml
env_access:
  - path: env.repositories.users
    type: UserRepository
```

Verify:
1. `Env` has `repositories` attribute
2. `Repositories` has `users` attribute
3. `users` has type `UserRepository`

## Process

### 1. Parse Type Definitions

Build symbol table from gen-types output:
```python
symbol_table = {
    "User": {
        "kind": "dataclass",
        "fields": {"id": "UserId", "email": "str", ...}
    },
    "CreateUserInput": {
        "kind": "pydantic",
        "fields": {"email": "str", "password": "str"}
    },
    "UserRepository": {
        "kind": "protocol",
        "methods": {
            "get_by_email": {"params": [("email", "str")], "returns": "Optional[User]"},
            ...
        }
    }
}
```

### 2. Generate Code Maps

For each morphism in category.yaml:
1. Determine signature from spec
2. Determine env dependencies from effects
3. Plan body steps (calls, conditions, returns)
4. Determine required imports
5. Generate map YAML

### 3. Verify Maps

For each code map:
1. Parse all steps
2. Check every call against symbol table
3. Check every construct against type definitions
4. Check imports complete
5. Report any mismatches

### 4. Output Verification Report

```yaml
# gen/maps-verification.yaml
verification:
  status: PASS  # or FAIL
  maps_checked: 15
  errors: []
  warnings:
    - map: user_ops.map.yaml
      warning: "Unused import: uuid4"
  
  type_checks:
    - map: user_ops.map.yaml
      function: create_user
      checks:
        - "repo.get_by_email(input.email) ✓"
        - "repo.save(user) ✓"
        - "CreateUserInput.email: str ✓"
  
  import_checks:
    - map: user_ops.map.yaml
      status: PASS
      imported: 12
      used: 12
```

## Validation Checklist

```bash
# 1. Maps generated for all morphisms
ls gen/maps/operations/*.map.yaml

# 2. Maps generated for all handlers
ls gen/maps/handlers/*.map.yaml

# 3. Verification passed
grep "status: PASS" gen/maps-verification.yaml

# 4. No type errors
! grep "type_error" gen/maps-verification.yaml
```

## Do NOT

- **Generate code yet** — This skill only generates maps
- **Skip verification** — Maps must be verified before gen-code
- **Ignore type mismatches** — Any mismatch is a FAIL
- **Assume imports** — Every used name must be explicitly imported
