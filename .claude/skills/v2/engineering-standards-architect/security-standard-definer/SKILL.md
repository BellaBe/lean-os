---
name: security-standard-definer
description: |
  Define security standards as categorical structures. Produces authentication flows,
  authorization models (RBAC/ABAC), input sanitization, output encoding, and tenant
  isolation patterns. Security as natural transformations on HTTP category.
  Input: categories/*.std.yaml, services.spec.yaml
  Output: standards/security/*.std.yaml
---

# Security Standard Definer

Define security patterns as categorical structures.

## Purpose

Transform security requirements into formal standards:
1. Authentication (identity verification)
2. Authorization (permission model)
3. Input sanitization (cleaning/validation)
4. Tenant isolation (multi-tenancy)

## Input

- `standards/categories/http.std.yaml` - HTTP category
- `services.spec.yaml` - Operations requiring security
- `domain-concepts.yaml` - Entities with ownership

## Output

```
standards/security/
├── authentication.std.yaml   # Identity verification
├── authorization.std.yaml    # Permission model
├── sanitization.std.yaml     # Input/output cleaning
└── tenant-isolation.std.yaml # Multi-tenancy
```

## Authentication Standard

### Schema

```yaml
# standards/security/authentication.std.yaml

standard:
  name: Authentication
  description: "Identity verification as natural transformation"
  
# Authentication as natural transformation: HTTP ⟹ AuthenticatedHTTP
transformation:
  name: Authenticate
  source_functor: HTTP
  target_functor: AuthenticatedHTTP
  
  # Components for each HTTP object
  components:
    Request:
      morphism: "verify_identity: Request → Either[AuthError, AuthenticatedRequest]"
      
  naturality: |
    For any HTTP morphism f: A → B,
    AuthenticatedHTTP(f) ∘ verify_A = verify_B ∘ HTTP(f)

# Authentication strategies
strategies:
  - name: JWT
    type: bearer_token
    flow:
      - extract: "Request → Option[Token]"
      - decode: "Token → Either[DecodeError, Claims]"
      - validate: "Claims → Either[ValidationError, Identity]"
      - attach: "Identity → AuthenticatedRequest"
    token_structure:
      header:
        alg: RS256
        typ: JWT
      payload:
        sub: user_id
        iss: issuer
        exp: expiration
        iat: issued_at
        scope: permissions
        
  - name: OAuth2
    type: authorization_code
    flow:
      - redirect: "Request → AuthorizationUrl"
      - callback: "AuthCode → Either[Error, TokenPair]"
      - refresh: "RefreshToken → Either[Error, TokenPair]"
    providers:
      - shopify  # For merchant auth

# Session management
session:
  type: stateless  # JWT-based
  storage: none    # Token contains all info
  refresh:
    enabled: true
    strategy: sliding_window
    max_age_hours: 24

# Error types
errors:
  - name: AuthError
    type: coproduct
    variants:
      - MissingToken
      - InvalidToken
      - ExpiredToken
      - InsufficientScope
      - InvalidSignature
      
# Endpoints excluded from auth
exclusions:
  - pattern: "/health"
    reason: "Health check"
  - pattern: "/metrics"
    reason: "Prometheus scraping"
  - pattern: "/api/auth/*"
    reason: "Auth endpoints themselves"

# Categorical interpretation
categorical:
  # Auth forms a monad
  monad:
    name: Auth
    type_constructor: "Auth[A] = Either[AuthError, A]"
    pure: "a ↦ Right(a)"
    bind: "ma.flatMap(f)"
  
  # Laws
  laws:
    - left_identity: "pure(a) >>= f ≡ f(a)"
    - right_identity: "m >>= pure ≡ m"
    - associativity: "(m >>= f) >>= g ≡ m >>= (x ↦ f(x) >>= g)"
```

## Authorization Standard

### Schema

```yaml
# standards/security/authorization.std.yaml

standard:
  name: Authorization
  description: "Permission checking as morphism guards"

# Authorization as guard morphisms
guard:
  type: "Permission × Request → Either[Forbidden, Request]"
  position: after_authentication
  
# Permission model: RBAC + ABAC hybrid
model:
  type: hybrid
  
  # Role-Based Access Control
  rbac:
    roles:
      - name: owner
        description: "Full access to own resources"
        permissions:
          - "merchant:*"
          - "profile:*"
          - "analysis:*"
          
      - name: admin
        description: "Platform administrator"
        permissions:
          - "*:*"
          
      - name: viewer
        description: "Read-only access"
        permissions:
          - "merchant:read"
          - "profile:read"
          - "analysis:read"
          
    hierarchy:
      admin:
        includes: [owner]
      owner:
        includes: [viewer]
        
  # Attribute-Based Access Control
  abac:
    attributes:
      subject:
        - id
        - role
        - tenant_id
        - subscription_tier
      resource:
        - id
        - owner_id
        - tenant_id
        - visibility
      environment:
        - time
        - ip_address
        - request_count
        
    policies:
      - name: owner_access
        description: "Users can access their own resources"
        condition: "subject.id == resource.owner_id"
        
      - name: tenant_isolation
        description: "Users can only access tenant resources"
        condition: "subject.tenant_id == resource.tenant_id"
        
      - name: rate_limit
        description: "Limit by subscription tier"
        condition: |
          subject.subscription_tier match {
            Free: environment.request_count < 100
            Pro: environment.request_count < 1000
            Enterprise: true
          }

# Permission checking morphisms
morphisms:
  - name: check_permission
    domain: "(Identity, Permission, Resource)"
    codomain: "Either[Forbidden, Authorized]"
    implementation: |
      1. Extract roles from identity
      2. Check RBAC permissions
      3. Evaluate ABAC policies
      4. Return Authorized or Forbidden
      
  - name: filter_resources
    domain: "(Identity, List[Resource])"
    codomain: "List[Resource]"
    implementation: |
      Filter to only resources user can access

# Categorical interpretation
categorical:
  # Authorization as a slice category
  slice:
    name: "Auth/Identity"
    description: "Category of resources accessible to identity"
    objects: "Resources where check_permission returns Authorized"
    morphisms: "Operations preserving authorization"
    
  # Guard as natural transformation
  transformation:
    name: Authorize
    source: AuthenticatedHTTP
    target: AuthorizedHTTP
    components:
      AuthenticatedRequest: check_permission
      
  laws:
    - "Authorized requests remain authorized under composition"
    - "Authorization is idempotent: auth(auth(r)) = auth(r)"

# Error types
errors:
  - name: AuthzError
    type: coproduct
    variants:
      - Forbidden: "No permission for action"
      - ResourceNotFound: "Resource doesn't exist or not visible"
      - QuotaExceeded: "Rate limit exceeded"
```

## Sanitization Standard

### Schema

```yaml
# standards/security/sanitization.std.yaml

standard:
  name: Sanitization
  description: "Input cleaning and output encoding"

# Input sanitization as endofunctor
input_sanitization:
  functor:
    name: Sanitize
    source: RawInput
    target: SanitizedInput
    
  rules:
    # String sanitization
    strings:
      - trim_whitespace: true
      - max_length: 10000
      - strip_null_bytes: true
      - normalize_unicode: NFC
      
    # HTML sanitization
    html:
      - escape_entities: true
      - allowed_tags: []  # No HTML by default
      - strip_scripts: true
      
    # SQL sanitization
    sql:
      - parameterized_queries: required
      - escape_quotes: true
      - no_dynamic_sql: true
      
    # Path sanitization
    paths:
      - no_traversal: true  # Block ../
      - allowed_extensions: [jpg, jpeg, png, gif, webp]
      - max_filename_length: 255

  morphisms:
    - name: sanitize_string
      domain: RawString
      codomain: "Either[SanitizationError, SafeString]"
      
    - name: sanitize_email
      domain: RawString
      codomain: "Either[SanitizationError, Email]"
      validation: "RFC 5322 compliant"
      
    - name: sanitize_url
      domain: RawString
      codomain: "Either[SanitizationError, Url]"
      validation: "Valid URL, allowed schemes: [https]"
      
    - name: sanitize_json
      domain: RawJSON
      codomain: "Either[SanitizationError, SafeJSON]"
      validation: "Well-formed, depth < 10, size < 1MB"

# Output encoding
output_encoding:
  rules:
    # JSON responses
    json:
      - escape_html_in_strings: true
      - no_executable_content: true
      
    # HTML responses (if any)
    html:
      - encode_entities: true
      - content_type: "text/html; charset=utf-8"
      - csp_header: true
      
    # Headers
    headers:
      - no_injection: true
      - secure_cookies: true
      - cors_restricted: true

  morphisms:
    - name: encode_response
      domain: InternalResponse
      codomain: HTTPResponse
      applies: "Content-Type based encoding"

# Validation as functor composition
validation_chain:
  order:
    - sanitize_input
    - validate_schema
    - validate_business_rules
  composition: "validate ∘ sanitize"

# Categorical interpretation
categorical:
  # Sanitization forms a monad
  monad:
    name: Sanitized
    type_constructor: "Sanitized[A] = Either[SanitizationError, A]"
    
  # Kleisli composition for chained validation
  kleisli:
    composition: "g <=< f = λx. f(x) >>= g"
    
  laws:
    - "Sanitization is idempotent: sanitize(sanitize(x)) = sanitize(x)"
    - "Sanitization preserves type structure"

# Error types
errors:
  - name: SanitizationError
    type: coproduct
    variants:
      - InvalidFormat: "Input doesn't match expected format"
      - TooLong: "Input exceeds maximum length"
      - DangerousContent: "Potentially malicious content detected"
      - EncodingError: "Invalid character encoding"
```

## Tenant Isolation Standard

### Schema

```yaml
# standards/security/tenant-isolation.std.yaml

standard:
  name: TenantIsolation
  description: "Multi-tenancy as slice categories"
  enabled: true  # Set false for single-tenant deployments

# Tenant model
tenant:
  identifier: merchant_id  # Each merchant is a tenant
  propagation: context     # Passed through request context
  
# Slice category per tenant
categorical:
  slice_category:
    name: "Domain/Tenant"
    description: "Category of objects belonging to tenant"
    
    # Objects are filtered by tenant
    objects: |
      For tenant T, objects are:
      { X ∈ Domain | tenant(X) = T }
      
    # Morphisms preserve tenant
    morphisms: |
      For f: A → B in Domain,
      f ∈ Domain/T iff tenant(A) = tenant(B) = T
      
    # Inclusion functor
    inclusion:
      name: "ι_T: Domain/T → Domain"
      forgetful: true

# Isolation rules
isolation:
  # Data isolation
  data:
    - all_queries_filtered: true
    - filter_type: "WHERE tenant_id = :current_tenant"
    - no_cross_tenant_joins: true
    
  # Row-level security
  rls:
    enabled: true
    policy: |
      CREATE POLICY tenant_isolation ON {table}
      USING (tenant_id = current_setting('app.tenant_id'))
      
  # API isolation
  api:
    - tenant_in_path: false    # Not /tenant/{id}/resource
    - tenant_from_auth: true   # Extract from JWT
    - validate_ownership: true # Check resource belongs to tenant

# Context propagation
context:
  extraction: |
    1. Extract tenant_id from JWT claims
    2. Validate tenant exists and active
    3. Set in request context
    4. Propagate to all downstream calls
    
  storage:
    type: context_var  # Python contextvars
    key: current_tenant
    
  database:
    type: session_var  # PostgreSQL session variable
    set: "SET app.tenant_id = :tenant_id"

# Morphism guards
guards:
  - name: verify_tenant
    domain: "(TenantId, Resource)"
    codomain: "Either[TenantError, Resource]"
    check: "resource.tenant_id == context.tenant_id"
    
  - name: filter_by_tenant
    domain: "Query"
    codomain: "TenantFilteredQuery"
    action: "Add WHERE tenant_id = :tenant clause"

# Cross-tenant operations (admin only)
admin_operations:
  allowed_roles: [platform_admin]
  operations:
    - name: migrate_tenant
    - name: export_tenant_data
    - name: delete_tenant
  audit: required

# Error types
errors:
  - name: TenantError
    type: coproduct
    variants:
      - TenantNotFound: "Tenant doesn't exist"
      - CrossTenantAccess: "Attempted access to another tenant"
      - TenantSuspended: "Tenant account suspended"
```

## Validation

### Completeness Checks

```yaml
completeness:
  - authentication_strategy_defined
  - authorization_model_complete
  - sanitization_rules_for_all_inputs
  - tenant_isolation_if_multi_tenant
```

### Consistency Checks

```yaml
consistency:
  - auth_before_authz
  - sanitize_before_validate
  - tenant_filter_on_all_queries
  - no_security_bypass_paths
```

## Next Skills

Output feeds into:
- `configuration-standard-definer` (for secrets management)
- `standards-validator`
