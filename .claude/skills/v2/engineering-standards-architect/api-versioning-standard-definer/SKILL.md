---
name: api-versioning-standard-definer
description: |
  Define API versioning standards as categorical structures. Produces version strategies,
  breaking change detection, deprecation morphisms, and migration paths.
  API versions as category with natural transformations for migrations.
  Input: categories/http.std.yaml, services.spec.yaml
  Output: standards/api-versioning/*.std.yaml
---

# API Versioning Standard Definer

Define API versioning patterns as categorical structures.

## Purpose

Transform API evolution requirements into formal standards:
1. Version strategy (URL, header, content-type)
2. Breaking vs non-breaking change detection
3. Deprecation morphisms
4. Migration paths as natural transformations

## Input

- `standards/categories/http.std.yaml` - HTTP category
- `services.spec.yaml` - API operations

## Output

```
standards/api-versioning/
├── versioning.std.yaml   # Version strategy
└── deprecation.std.yaml  # Deprecation morphisms
```

## Versioning Standard

### Schema

```yaml
# standards/api-versioning/versioning.std.yaml

standard:
  name: APIVersioning
  description: "API versions as category with migration natural transformations"

# Version category
category:
  name: APIVersions
  description: "Category where objects are API versions"
  
  objects:
    - V1: "Initial API version"
    - V2: "Current stable version"
    - V3: "Beta/preview version"
    
  morphisms:
    # Migration morphisms between versions
    - name: migrate_v1_v2
      domain: V1
      codomain: V2
      direction: forward
      automatic: true
      
    - name: migrate_v2_v1
      domain: V2
      codomain: V1
      direction: backward
      lossy: true  # Some V2 features not in V1
      
  composition: |
    migrate_v1_v3 = migrate_v2_v3 ∘ migrate_v1_v2

# Version strategy
strategy:
  type: url_path  # Or: header, content_type, query_param
  
  patterns:
    url_path:
      format: "/api/v{version}/{resource}"
      example: "/api/v2/merchants"
      pros: [explicit, cacheable, easy_routing]
      cons: [url_pollution, hard_to_change]
      
    header:
      header_name: "X-API-Version"
      format: "{major}.{minor}"
      example: "X-API-Version: 2.0"
      pros: [clean_urls, flexible]
      cons: [hidden, harder_to_cache]
      
    content_type:
      format: "application/vnd.{app}.v{version}+json"
      example: "application/vnd.leanos.v2+json"
      pros: [rest_compliant, content_negotiation]
      cons: [complex, tooling_issues]
      
    query_param:
      param_name: "version"
      format: "?version={version}"
      example: "/api/merchants?version=2"
      pros: [simple]
      cons: [not_restful, caching_issues]
      
  selected: url_path

# Version format
versioning:
  scheme: semantic  # major.minor.patch
  
  major:
    increment_on: breaking_changes
    compatibility: none
    
  minor:
    increment_on: new_features
    compatibility: backward
    
  patch:
    increment_on: bug_fixes
    compatibility: full

# Supported versions
versions:
  - version: "1"
    status: deprecated
    deprecated_at: "2024-01-01"
    sunset_at: "2024-07-01"
    
  - version: "2"
    status: stable
    released_at: "2024-01-01"
    
  - version: "3"
    status: beta
    released_at: "2024-06-01"

# Default version
default:
  strategy: latest_stable
  fallback: "2"
  header_for_unversioned: true

# Breaking changes definition
breaking_changes:
  - type: endpoint_removed
    description: "Removing an endpoint"
    example: "DELETE /api/v1/legacy_endpoint"
    
  - type: field_removed
    description: "Removing field from response"
    example: "Removing 'legacy_field' from Merchant"
    
  - type: field_type_changed
    description: "Changing field type"
    example: "id: int → id: string"
    
  - type: required_field_added
    description: "Adding required field to request"
    example: "Adding required 'tenant_id'"
    
  - type: enum_value_removed
    description: "Removing enum variant"
    example: "Removing 'legacy_status' from Status"
    
  - type: behavior_changed
    description: "Changing operation semantics"
    example: "GET now returns 404 instead of empty"

# Non-breaking changes
non_breaking_changes:
  - type: endpoint_added
    description: "Adding new endpoint"
    
  - type: optional_field_added
    description: "Adding optional field to request/response"
    
  - type: enum_value_added
    description: "Adding new enum variant"
    
  - type: field_made_optional
    description: "Making required field optional"

# Categorical interpretation
categorical:
  # Versions form a category
  version_category:
    objects: "API versions (V1, V2, V3, ...)"
    morphisms: "Migration functions between versions"
    identity: "id_Vn: Vn → Vn (no migration)"
    composition: "Transitive migration"
    
  # Migration as functor
  migration_functor:
    definition: |
      For each version pair (Vn, Vm),
      Migrate: API_Vn → API_Vm
      preserving endpoint structure
      
  # Natural transformation for schema evolution
  schema_evolution:
    definition: |
      For migration M: V1 → V2,
      For each endpoint E,
      α_E: Schema_V1(E) → Schema_V2(E)
      forming natural transformation α: Schema_V1 ⟹ Schema_V2
```

## Deprecation Standard

### Schema

```yaml
# standards/api-versioning/deprecation.std.yaml

standard:
  name: Deprecation
  description: "Deprecation as morphism lifecycle"

# Deprecation lifecycle
lifecycle:
  states:
    - name: active
      description: "Fully supported"
      
    - name: deprecated
      description: "Still works, but discouraged"
      headers:
        Deprecation: "true"
        Sunset: "{sunset_date}"
        Link: "<{migration_doc}>; rel=\"deprecation\""
        
    - name: sunset
      description: "No longer available"
      response: 410 Gone
      
  transitions:
    - from: active
      to: deprecated
      trigger: deprecation_announced
      notice_period: 6_months
      
    - from: deprecated
      to: sunset
      trigger: sunset_date_reached

# Deprecation rules
rules:
  notice_period:
    minimum: 6_months
    recommended: 12_months
    
  communication:
    - changelog_entry
    - api_response_headers
    - documentation_update
    - email_notification
    
  migration_support:
    required: true
    documentation: true
    automated_tools: optional

# Deprecation registry
deprecated:
  endpoints:
    - path: "/api/v1/legacy_analyze"
      deprecated_at: "2024-01-01"
      sunset_at: "2024-07-01"
      replacement: "/api/v2/analyses"
      migration_guide: "docs/migrations/v1-to-v2.md"
      
  fields:
    - resource: Merchant
      field: legacy_settings
      deprecated_at: "2024-03-01"
      sunset_at: "2024-09-01"
      replacement: settings
      
  parameters:
    - endpoint: "GET /api/v2/products"
      parameter: legacy_filter
      deprecated_at: "2024-02-01"
      sunset_at: "2024-08-01"
      replacement: filter

# Deprecation headers
headers:
  - name: Deprecation
    value: "true"
    description: "Indicates endpoint is deprecated"
    
  - name: Sunset
    value: "Sat, 01 Jul 2024 00:00:00 GMT"
    format: "HTTP-date (RFC 7231)"
    description: "When endpoint will be removed"
    
  - name: Link
    value: '<https://docs.example.com/deprecation>; rel="deprecation"'
    description: "Link to deprecation documentation"

# Migration paths
migrations:
  - from_version: "1"
    to_version: "2"
    changes:
      - type: endpoint_renamed
        old: "/api/v1/analyze"
        new: "/api/v2/analyses"
        
      - type: field_renamed
        resource: Merchant
        old: shop_url
        new: shop_domain
        
      - type: field_type_changed
        resource: Analysis
        field: id
        old_type: int
        new_type: string
        transform: "str(id)"
        
      - type: field_added
        resource: Merchant
        field: subscription
        default: { tier: "Free" }
        
    migration_script: |
      # Automated migration
      def migrate_v1_to_v2(request):
        # Rename endpoints
        if request.path.startswith("/api/v1/analyze"):
          request.path = request.path.replace("/analyze", "/analyses")
          
        # Transform fields
        if "shop_url" in request.body:
          request.body["shop_domain"] = request.body.pop("shop_url")
          
        return request

# Response transformation
response_transformation:
  - name: backward_compatible
    description: "V2 response includes V1 fields"
    strategy: |
      Include deprecated fields with new fields
      Mark deprecated fields in schema
      
  - name: strict
    description: "Each version has exact schema"
    strategy: |
      Transform response based on requested version
      
  selected: backward_compatible

# Categorical interpretation
categorical:
  # Deprecation as morphism annotation
  annotation:
    definition: |
      Deprecated morphism f: A → B has:
      - sunset_date: Timestamp
      - replacement: Option[Morphism]
      
  # Migration as natural transformation
  migration_transformation:
    definition: |
      For migration M: V1 → V2,
      M is natural transformation: API_V1 ⟹ API_V2
      
      Components:
      - M_endpoints: Transform endpoint paths
      - M_schemas: Transform request/response schemas
      - M_behavior: Preserve semantics
      
    naturality: |
      For any operation f in V1,
      M_output ∘ f_V1 = f_V2 ∘ M_input
      (Migrating then operating = operating then migrating)
      
  # Version functor
  version_functor:
    definition: |
      Version: ℕ → Category
      Version(n) = API_Vn
      
    morphism_map: |
      For n < m,
      Version(n → m) = Migration(Vn → Vm)
```

## Validation

### Completeness Checks

```yaml
completeness:
  - version_strategy_selected
  - all_versions_documented
  - breaking_changes_identified
  - migration_paths_defined
```

### Consistency Checks

```yaml
consistency:
  - deprecation_dates_future
  - sunset_after_deprecation
  - migrations_are_composable
  - no_version_gaps
```

## Next Skills

Output feeds into:
- `standards-validator`
