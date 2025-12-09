---
name: functor-mapper
description: |
  Map categorical functors to structure-preserving transformations. Produces HTTP functor
  (Domain → HTTP), storage functor (Domain → Storage), external functor mappings.
  Functors become adapter/mapper classes preserving composition.
  Input: standards/categories/*.std.yaml, primitives maps
  Output: maps/functors/*.map.yaml
---

# Functor Mapper

Map functors to structure-preserving implementations.

## Purpose

Transform functors into adapter/mapper patterns:
1. HTTP functor (Domain → HTTP endpoints)
2. Storage functor (Domain → Database models)
3. External functor (Domain → External APIs)
4. Preserve identity and composition

## Input

- `standards/categories/http.std.yaml` - HTTP functor
- `standards/categories/storage.std.yaml` - Storage functor
- `standards/categories/external.std.yaml` - External functor
- `maps/primitives/*.map.yaml` - Type mappings

## Output

```
maps/functors/
├── http.map.yaml      # Domain → HTTP
├── storage.map.yaml   # Domain → Storage
└── external.map.yaml  # Domain → External
```

## Functor Structure

### Abstract Pattern

```yaml
functor_pattern:
  structure:
    source: "Category C"
    target: "Category D"
    object_map: "F: Ob(C) → Ob(D)"
    morphism_map: "F: Hom(A,B) → Hom(F(A),F(B))"
    
  laws:
    identity: "F(id_A) = id_F(A)"
    composition: "F(g ∘ f) = F(g) ∘ F(f)"
    
  implementation:
    object_map: "Type transformation"
    morphism_map: "Operation transformation"
```

## HTTP Functor

### Schema

```yaml
# maps/functors/http.map.yaml

functor:
  name: HTTP
  description: "Domain → HTTP category"
  source: Domain
  target: HTTP
  
  # Object mapping: Domain types → HTTP representations
  object_map:
    pattern: |
      Domain type → Request/Response DTO
      
    mappings:
      # Request DTOs (input)
      - domain: Merchant
        http:
          create_request: CreateMerchantRequest
          update_request: UpdateMerchantRequest
          
      - domain: Profile
        http:
          create_request: CreateProfileRequest
          update_request: UpdateProfileRequest
          
      # Response DTOs (output)
      - domain: Merchant
        http:
          response: MerchantResponse
          list_response: MerchantListResponse
          
      - domain: AnalysisResult
        http:
          response: AnalysisResponse
          
    targets:
      python:
        request_template: |
          class {Name}Request(BaseModel):
              """HTTP request DTO for {name}."""
              {fields}
              
              def to_domain(self) -> {Domain}:
                  """Inverse functor (right adjoint)"""
                  return {Domain}(
                      {field_mappings}
                  )
                  
        response_template: |
          class {Name}Response(BaseModel):
              """HTTP response DTO for {name}."""
              {fields}
              
              @classmethod
              def from_domain(cls, domain: {Domain}) -> '{Name}Response':
                  """Functor application"""
                  return cls(
                      {field_mappings}
                  )
                  
      typescript:
        request_template: |
          interface {Name}Request {
            {fields}
          }
          
          function toDomain(req: {Name}Request): {Domain} {
            return {
              {field_mappings}
            };
          }
          
        response_template: |
          interface {Name}Response {
            {fields}
          }
          
          function fromDomain(domain: {Domain}): {Name}Response {
            return {
              {field_mappings}
            };
          }

  # Morphism mapping: Domain operations → HTTP endpoints
  morphism_map:
    pattern: |
      Domain morphism f: A → B
      HTTP morphism: HTTP(A) → HTTP(B)
      As endpoint: {method} {path} with request → response
      
    mappings:
      # CRUD operations
      - domain_morphism: create_merchant
        http:
          method: POST
          path: "/api/v{version}/merchants"
          request: CreateMerchantRequest
          response: MerchantResponse
          status_codes:
            success: 201
            validation_error: 400
            conflict: 409
            
      - domain_morphism: get_merchant
        http:
          method: GET
          path: "/api/v{version}/merchants/{id}"
          path_params: [id]
          response: MerchantResponse
          status_codes:
            success: 200
            not_found: 404
            
      - domain_morphism: update_merchant
        http:
          method: PATCH
          path: "/api/v{version}/merchants/{id}"
          path_params: [id]
          request: UpdateMerchantRequest
          response: MerchantResponse
          status_codes:
            success: 200
            validation_error: 400
            not_found: 404
            
      - domain_morphism: delete_merchant
        http:
          method: DELETE
          path: "/api/v{version}/merchants/{id}"
          path_params: [id]
          status_codes:
            success: 204
            not_found: 404
            
      # Custom operations
      - domain_morphism: analyze_photo
        http:
          method: POST
          path: "/api/v{version}/analyses"
          request: AnalyzePhotoRequest
          response: AnalysisResponse
          status_codes:
            success: 202  # Accepted (async)
            validation_error: 400
            quota_exceeded: 429

    targets:
      python:
        handler_template: |
          @router.{method}("{path}")
          async def {operation}(
              {path_params}
              {request_param}
              service: {Service} = Depends(get_{service}),
          ) -> {Response}:
              """
              {docstring}
              
              Functor: HTTP({domain_morphism})
              """
              {convert_request}
              result = await service.{domain_morphism}({args})
              
              match result:
                  case Success(value):
                      return {Response}.from_domain(value)
                  case Failure(error):
                      raise HTTPException(
                          status_code={error_status},
                          detail=error.message,
                      )
                      
      typescript:
        handler_template: |
          app.{method}('{path}', async (req, res) => {
            const {input} = {parse_input};
            const result = await service.{domain_morphism}({input});
            
            if (isLeft(result)) {
              return res.status({error_status}).json(result.left);
            }
            
            return res.status({success_status}).json(
              fromDomain(result.right)
            );
          });

  # Functor laws verification
  laws:
    identity:
      statement: "HTTP(id_A) = id_HTTP(A)"
      implementation: |
        Identity morphism in domain = no-op
        HTTP identity = returning input unchanged
        Verification: GET then immediate response = same data
        
    composition:
      statement: "HTTP(g ∘ f) = HTTP(g) ∘ HTTP(f)"
      implementation: |
        Composed domain operations
        Map to composed HTTP operations
        Or: single endpoint performing both
```

## Storage Functor

### Schema

```yaml
# maps/functors/storage.map.yaml

functor:
  name: Storage
  description: "Domain → Storage category"
  source: Domain
  target: Storage
  
  # Object mapping: Domain types → Database models
  object_map:
    pattern: |
      Domain entity → Database table/model
      Domain value object → Embedded/JSON column
      
    mappings:
      - domain: Merchant
        storage:
          model: MerchantModel
          table: merchants
          columns:
            id: "UUID PRIMARY KEY"
            shop_domain: "VARCHAR(255) UNIQUE NOT NULL"
            subscription_tier: "VARCHAR(50) NOT NULL"
            settings: "JSONB"
            created_at: "TIMESTAMP NOT NULL"
            updated_at: "TIMESTAMP NOT NULL"
            
      - domain: Profile
        storage:
          model: ProfileModel
          table: profiles
          columns:
            id: "UUID PRIMARY KEY"
            merchant_id: "UUID REFERENCES merchants(id)"
            skin_data: "JSONB"
            created_at: "TIMESTAMP NOT NULL"
            
    targets:
      python:
        model_template: |
          class {Name}Model(Base):
              """Storage functor: {Domain} → {Name}Model"""
              __tablename__ = '{table}'
              
              {column_definitions}
              
              @classmethod
              def from_domain(cls, entity: {Domain}) -> '{Name}Model':
                  """Functor object map"""
                  return cls(
                      {field_mappings}
                  )
                  
              def to_domain(self) -> {Domain}:
                  """Inverse functor (Free)"""
                  return {Domain}(
                      {field_mappings}
                  )
                  
      typescript:
        model_template: |
          // Prisma schema
          model {Name} {
            {field_definitions}
          }
          
          function fromDomain(entity: {Domain}): Prisma.{Name}CreateInput {
            return {
              {field_mappings}
            };
          }
          
          function toDomain(model: {Name}): {Domain} {
            return {
              {field_mappings}
            };
          }

  # Morphism mapping: Domain operations → SQL operations
  morphism_map:
    pattern: |
      Domain morphism → SQL query/command
      
    mappings:
      - domain_morphism: "create: A → Stored[A]"
        storage:
          operation: INSERT
          template: "INSERT INTO {table} ({columns}) VALUES ({values})"
          
      - domain_morphism: "get: Id → Option[A]"
        storage:
          operation: SELECT
          template: "SELECT * FROM {table} WHERE id = :id"
          
      - domain_morphism: "update: (Id, Patch) → A"
        storage:
          operation: UPDATE
          template: "UPDATE {table} SET {assignments} WHERE id = :id"
          
      - domain_morphism: "delete: Id → Unit"
        storage:
          operation: DELETE
          template: "DELETE FROM {table} WHERE id = :id"
          
      - domain_morphism: "list: Query → List[A]"
        storage:
          operation: SELECT
          template: "SELECT * FROM {table} WHERE {conditions} LIMIT :limit OFFSET :offset"
```

## External Functor

### Schema

```yaml
# maps/functors/external.map.yaml

functor:
  name: External
  description: "Domain → External API category"
  source: Domain
  target: External
  
  # Object mapping: Domain types → External API types
  object_map:
    pattern: |
      Domain type → External API request/response
      
    mappings:
      - domain: ShopData
        external:
          api: shopify
          endpoint_response: ShopifyShopResponse
          
      - domain: AnalysisRequest
        external:
          api: groq
          request_format: GroqChatRequest
          
    targets:
      python:
        template: |
          @dataclass
          class {External}Request:
              """External API request format."""
              {fields}
              
              @classmethod
              def from_domain(cls, domain: {Domain}) -> '{External}Request':
                  """Functor: Domain → External"""
                  return cls(
                      {mappings}
                  )
                  
          @dataclass
          class {External}Response:
              """External API response format."""
              {fields}
              
              def to_domain(self) -> {Domain}:
                  """Inverse functor"""
                  return {Domain}(
                      {mappings}
                  )

  # Morphism mapping: Domain operations → API calls
  morphism_map:
    mappings:
      - domain_morphism: fetch_shop_data
        external:
          api: shopify
          method: GET
          endpoint: "/admin/api/{version}/shop.json"
          
      - domain_morphism: analyze_image
        external:
          api: groq
          method: POST
          endpoint: "/v1/chat/completions"
          request_transform: |
            {
              "model": config.model,
              "messages": [
                {"role": "user", "content": [
                  {"type": "image_url", "image_url": {"url": image_data}},
                  {"type": "text", "text": prompt}
                ]}
              ]
            }
```

## Validation

### Completeness Checks

```yaml
completeness:
  - all_domain_types_have_http_dtos
  - all_domain_types_have_storage_models
  - all_morphisms_have_endpoint_mappings
  - all_external_apis_mapped
```

### Consistency Checks

```yaml
consistency:
  - functor_laws_preserved
  - type_conversions_reversible
  - all_fields_mapped
```

## Next Skills

Output feeds into:
- `module-mapper`
- `maps-validator`
