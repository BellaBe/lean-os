---
name: category-standard-definer
description: |
  Define categorical structure standards from specifications. Produces category definitions
  for domain, storage, external, and HTTP layers with objects, morphisms, functors, 
  adjunctions, and laws. Foundation for all other standards.
  Input: architecture.categorical, requirements.adt, services.spec.yaml
  Output: standards/categories/*.std.yaml
---

# Category Standard Definer

Define the core categorical structures that govern system composition.

## Purpose

Transform detected categorical structure into formal standards:
1. Domain category (business types and operations)
2. Storage category (persistence layer)
3. External category (third-party integrations)
4. HTTP category (API layer)

## Input

From specifications:
- `architecture.categorical` - Detected structure
- `requirements.adt` - Type definitions
- `services.spec.yaml` - Morphism signatures

## Output

```
standards/categories/
├── domain.std.yaml     # Domain category standard
├── storage.std.yaml    # Storage/repository standard
├── external.std.yaml   # External API standard
└── http.std.yaml       # HTTP/REST standard
```

## Domain Category Standard

### Schema

```yaml
# standards/categories/domain.std.yaml

category:
  name: Domain
  description: "Business domain types and pure operations"
  
objects:
  # From requirements.adt products
  - name: Merchant
    type: product
    factors:
      - MerchantId
      - ShopDomain
      - Subscription
      - Settings
    laws:
      - "projection: π₁(merchant) = merchant.id"
      - "pairing: ⟨π₁, π₂⟩ ∘ Δ = id"
      
  # From requirements.adt coproducts
  - name: SubscriptionTier
    type: coproduct
    variants:
      - Free
      - Pro
      - Enterprise
    laws:
      - "injection: inl, inr are monic"
      - "case: [f, g] ∘ inl = f"

morphisms:
  # Pure domain operations
  - name: validate_input
    domain: RawInput
    codomain: "Either[ValidationError, ValidInput]"
    properties:
      total: true
      deterministic: true
    laws:
      - "idempotent: validate(validate(x)) = validate(x)"
      
identity_morphisms:
  # Every object has identity
  - object: Merchant
    morphism: "id_Merchant: Merchant → Merchant"
  - object: Profile
    morphism: "id_Profile: Profile → Profile"

composition:
  # Composition laws
  associativity: "(h ∘ g) ∘ f = h ∘ (g ∘ f)"
  left_identity: "id ∘ f = f"
  right_identity: "f ∘ id = f"
  
products:
  # Product types with universal property
  - name: "A × B"
    projections:
      - "π₁: A × B → A"
      - "π₂: A × B → B"
    universal: |
      For any C with f: C → A and g: C → B,
      ∃! ⟨f,g⟩: C → A × B such that
      π₁ ∘ ⟨f,g⟩ = f and π₂ ∘ ⟨f,g⟩ = g

coproducts:
  # Coproduct types with universal property
  - name: "A + B"
    injections:
      - "inl: A → A + B"
      - "inr: B → A + B"
    universal: |
      For any C with f: A → C and g: B → C,
      ∃! [f,g]: A + B → C such that
      [f,g] ∘ inl = f and [f,g] ∘ inr = g
```

### Generation Rules

1. **Objects from ADT:**
   - Product types → Objects with projections
   - Coproduct types → Objects with injections
   - Recursive types → Initial algebras

2. **Morphisms from services.spec:**
   - Pure operations (no effects) → Domain morphisms
   - Domain layer in services.spec → Domain category

3. **Laws:**
   - Product laws (projection, pairing)
   - Coproduct laws (injection, case)
   - Composition laws (associativity, identity)

## Storage Category Standard

### Schema

```yaml
# standards/categories/storage.std.yaml

category:
  name: Storage
  description: "Persistence operations with IO effects"

objects:
  # Repository representations
  - name: StoredMerchant
    maps_to: Merchant  # Domain object it represents
    storage_type: table
    table_name: merchants
    
  - name: StoredProfile
    maps_to: Profile
    storage_type: table
    table_name: profiles

morphisms:
  # CRUD as morphisms
  - name: insert
    domain: Merchant
    codomain: "IO[Either[DbError, StoredMerchant]]"
    sql_pattern: INSERT
    
  - name: select
    domain: MerchantId
    codomain: "IO[Either[DbError, StoredMerchant]]"
    sql_pattern: "SELECT WHERE id = ?"
    
  - name: update
    domain: "(MerchantId, MerchantPatch)"
    codomain: "IO[Either[DbError, StoredMerchant]]"
    sql_pattern: UPDATE
    idempotent: true
    
  - name: delete
    domain: MerchantId
    codomain: "IO[Either[DbError, Unit]]"
    sql_pattern: DELETE
    idempotent: true

# Repository adjunction: Free ⊣ Repository
adjunction:
  name: "Free ⊣ Repository"
  left_functor:
    name: Free
    source: Storage
    target: Domain
    object_map: "StoredX ↦ X"
    morphism_map: "select ↦ get, insert ↦ create"
    
  right_functor:
    name: Repository
    source: Domain
    target: Storage
    object_map: "X ↦ StoredX"
    morphism_map: "create ↦ insert, get ↦ select"
    
  unit:
    name: η
    type: "Domain → Repository(Free(Domain))"
    meaning: "Embed domain object into storage representation"
    
  counit:
    name: ε
    type: "Free(Repository(Storage)) → Storage"
    meaning: "Execute storage operation"
    
  triangle_identities:
    left: "(ε ∘ Free) ∘ (Free ∘ η) = id_Free"
    right: "(Repository ∘ ε) ∘ (η ∘ Repository) = id_Repository"

laws:
  - name: "Repository preserves composition"
    statement: "Repository(g ∘ f) = Repository(g) ∘ Repository(f)"
    
  - name: "Repository preserves identity"
    statement: "Repository(id_A) = id_Repository(A)"
    
  - name: "Free preserves composition"
    statement: "Free(g ∘ f) = Free(g) ∘ Free(f)"
```

### Generation Rules

1. **Objects:** Domain entities with `lifecycle: true` or `persistence: true`
2. **Morphisms:** Repository layer from services.spec.yaml
3. **Adjunction:** Free ⊣ Repository standard pattern
4. **Laws:** Functor laws for both directions

## External Category Standard

### Schema

```yaml
# standards/categories/external.std.yaml

category:
  name: External
  description: "Third-party API integrations"

objects:
  # External service representations
  - name: ShopifyShop
    external_type: shopify
    api_version: "2024-01"
    
  - name: GroqCompletion
    external_type: groq
    model: "llama-3.2-90b-vision-preview"

morphisms:
  # External API calls as morphisms
  - name: fetch_shop
    domain: ShopDomain
    codomain: "IO[Either[ShopifyError, ShopifyShop]]"
    http_method: GET
    endpoint: "/admin/api/{version}/shop.json"
    resilience:
      timeout_ms: 5000
      retry: exponential
      circuit_breaker: true
      
  - name: analyze_image
    domain: "(ImageData, Prompt)"
    codomain: "IO[Either[GroqError, GroqCompletion]]"
    http_method: POST
    endpoint: "/v1/chat/completions"
    resilience:
      timeout_ms: 30000
      retry: exponential
      circuit_breaker: true
      fallback: cached

# External functor: Domain → External
functor:
  name: External
  source: Domain
  target: ExternalCategory
  
  object_map:
    Merchant: ShopifyShop
    Photo: ImageData
    AnalysisResult: GroqCompletion
    
  morphism_map:
    get_shop_data: fetch_shop
    analyze_photo: analyze_image
    
  laws:
    - "External(id) = id"
    - "External(g ∘ f) = External(g) ∘ External(f)"

# Natural transformation: adds resilience
resilience_transformation:
  name: Resilient
  source: External
  target: ResilientExternal
  
  components:
    # For each external morphism, wrap with resilience
    fetch_shop: "External[fetch_shop] → Resilient[fetch_shop]"
    analyze_image: "External[analyze_image] → Resilient[analyze_image]"
    
  naturality: |
    For f: A → B in External,
    Resilient(f) ∘ η_A = η_B ∘ f
```

### Generation Rules

1. **Objects:** From domain-concepts.yaml `external_dependencies`
2. **Morphisms:** External layer from services.spec.yaml with resilience
3. **Functor:** Maps domain operations to external calls
4. **Transformation:** Adds resilience patterns systematically

## HTTP Category Standard

### Schema

```yaml
# standards/categories/http.std.yaml

category:
  name: HTTP
  description: "REST API layer"

objects:
  # HTTP representations
  - name: Request
    components:
      - method: "GET | POST | PUT | PATCH | DELETE"
      - path: string
      - headers: "Map[string, string]"
      - body: "Option[JSON]"
      
  - name: Response
    components:
      - status: int
      - headers: "Map[string, string]"
      - body: "Option[JSON]"

morphisms:
  # Endpoints as morphisms
  - name: "POST /api/merchants"
    domain: CreateMerchantRequest
    codomain: "IO[Response[Merchant]]"
    maps_to: create_merchant
    
  - name: "GET /api/merchants/{id}"
    domain: MerchantId
    codomain: "IO[Response[Merchant]]"
    maps_to: get_merchant
    
  - name: "PUT /api/merchants/{id}"
    domain: "(MerchantId, UpdateMerchantRequest)"
    codomain: "IO[Response[Merchant]]"
    maps_to: update_merchant

# HTTP functor: Domain → HTTP
functor:
  name: HTTP
  source: Domain
  target: HTTPCategory
  
  object_map:
    Merchant: MerchantResource
    Profile: ProfileResource
    Analysis: AnalysisResource
    
  morphism_map:
    create_merchant: "POST /api/merchants"
    get_merchant: "GET /api/merchants/{id}"
    update_merchant: "PUT /api/merchants/{id}"

# Natural transformations for middleware
middleware_transformations:
  - name: Auth
    type: "HTTP ⟹ AuthenticatedHTTP"
    applies_to: "all except /health, /metrics"
    components:
      verify_token: "Request → Either[AuthError, AuthRequest]"
      
  - name: Validation
    type: "AuthenticatedHTTP ⟹ ValidatedHTTP"
    applies_to: "POST, PUT, PATCH"
    components:
      validate_body: "AuthRequest → Either[ValidationError, ValidRequest]"
      
  - name: Logging
    type: "ValidatedHTTP ⟹ LoggedHTTP"
    applies_to: all
    components:
      log_request: "ValidRequest → IO[LoggedRequest]"

# Middleware composition
middleware_chain:
  order:
    - Auth
    - Validation
    - Logging
  composition: "Logging ∘ Validation ∘ Auth"
  associativity: "guaranteed by natural transformation composition"
```

### Generation Rules

1. **Objects:** Request/Response types
2. **Morphisms:** From services.spec.yaml API layer
3. **Functor:** Domain → HTTP mapping
4. **Transformations:** Middleware as natural transformations

## Validation

### Completeness Checks

```yaml
completeness:
  - every_domain_object_has_identity
  - every_functor_has_object_and_morphism_maps
  - every_adjunction_has_unit_and_counit
  - every_natural_transformation_has_components
```

### Consistency Checks

```yaml
consistency:
  - functor_laws_hold
  - adjunction_triangle_identities
  - naturality_squares_commute
  - composition_is_associative
```

## Next Skill

Output feeds into:
- `security-standard-definer`
- `observability-standard-definer`
- `caching-standard-definer`
- `transaction-standard-definer`
