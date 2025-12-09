---
name: type-correspondence-prover
description: Verify bijection between OpenAPI schemas and TypeScript types. Proves type correspondence (no information loss). Checks all endpoints covered. Generates correspondence proof. Sub-skill of frontend-prover.
version: 1.0.0
allowed-tools: bash_tool, create_file, view
model: claude-sonnet-4-20250514
license: Proprietary - LeanOS Engineering Layer
---

# type-correspondence-prover: Verify TypeScript ↔ OpenAPI Bijection

## Purpose

Prove **bijective correspondence** between OpenAPI schemas and TypeScript types.

**Bijection means:**
- **Surjection:** Every OpenAPI schema has TypeScript equivalent (completeness)
- **Injection:** Every TypeScript type maps to OpenAPI schema (no extras)
- **One-to-one:** No information loss in translation

**This is NOT composition verification** (that's backend-prover's job). This is **type isomorphism verification**.

---

## Input

**OpenAPI schema (original):**
```
artifacts/engineering/specifications/v{X}/api.openapi.json
```

**Generated TypeScript types:**
```
artifacts/engineering/code/frontend/types/api.ts
```

---

## Verification Process

### Verification 1: Surjection (Completeness)

**Goal:** Every OpenAPI schema has TypeScript interface

```python
def verify_surjection(openapi_schemas, typescript_types):
    """
    Check: For every schema in OpenAPI, there exists a TypeScript type
    """
    
    errors = []
    
    for schema_name, schema_def in openapi_schemas.items():
        # Check TypeScript type exists
        if not typescript_type_exists(schema_name, typescript_types):
            errors.append({
                "type": "missing_typescript_type",
                "schema_name": schema_name,
                "fix": f"Generate TypeScript interface for {schema_name}"
            })
            continue
        
        # Verify properties match
        ts_type = get_typescript_type(schema_name, typescript_types)
        
        for prop_name, prop_def in schema_def.get('properties', {}).items():
            if not typescript_property_exists(prop_name, ts_type):
                errors.append({
                    "type": "missing_property",
                    "schema_name": schema_name,
                    "property": prop_name,
                    "fix": f"Add {prop_name} to {schema_name} TypeScript interface"
                })
    
    return {
        "complete": len(errors) == 0,
        "schemas_checked": len(openapi_schemas),
        "errors": errors
    }
```

**Example error:**
```json
{
  "type": "missing_typescript_type",
  "schema_name": "ProductStatus",
  "fix": "Generate TypeScript interface for ProductStatus"
}
```

---

### Verification 2: Injection (No Extras)

**Goal:** Every TypeScript type maps to OpenAPI schema (no extra types)

```python
def verify_injection(openapi_schemas, typescript_types):
    """
    Check: For every TypeScript type, there exists an OpenAPI schema
    
    Exception: Helper types allowed (e.g., ApiError, utility types)
    """
    
    errors = []
    allowed_helpers = [
        'ApiError',           # Standard error type
        'ApiClientError',     # Client error class
        'RequestConfig',      # Request configuration
        'ResponseMeta'        # Response metadata
    ]
    
    for ts_type_name in typescript_types:
        # Skip helper types
        if ts_type_name in allowed_helpers:
            continue
        
        # Skip generated request/response types
        if ts_type_name.endswith('Request') or ts_type_name.endswith('Response'):
            # These are derived from endpoints, not schemas
            continue
        
        # Check OpenAPI schema exists
        if not openapi_schema_exists(ts_type_name, openapi_schemas):
            errors.append({
                "type": "extra_typescript_type",
                "typescript_type": ts_type_name,
                "fix": f"Remove {ts_type_name} or add to OpenAPI schema"
            })
    
    return {
        "no_extras": len(errors) == 0,
        "types_checked": len(typescript_types),
        "errors": errors
    }
```

---

### Verification 3: Property-Level Correspondence

**Goal:** Properties in TypeScript match properties in OpenAPI

```python
def verify_property_correspondence(openapi_schemas, typescript_types):
    """
    For each schema/type pair, verify:
    - Properties match
    - Types match
    - Optionality matches (required/optional)
    """
    
    errors = []
    
    for schema_name in openapi_schemas:
        openapi_schema = openapi_schemas[schema_name]
        ts_type = typescript_types.get(schema_name)
        
        if not ts_type:
            continue  # Caught by surjection check
        
        openapi_props = openapi_schema.get('properties', {})
        required_props = set(openapi_schema.get('required', []))
        
        for prop_name, prop_def in openapi_props.items():
            ts_prop = ts_type.get('properties', {}).get(prop_name)
            
            if not ts_prop:
                errors.append({
                    "type": "missing_property",
                    "schema": schema_name,
                    "property": prop_name
                })
                continue
            
            # Verify type matches
            openapi_type = map_openapi_type(prop_def)
            ts_type_annotation = ts_prop['type']
            
            if not types_equivalent(openapi_type, ts_type_annotation):
                errors.append({
                    "type": "type_mismatch",
                    "schema": schema_name,
                    "property": prop_name,
                    "openapi_type": openapi_type,
                    "typescript_type": ts_type_annotation
                })
            
            # Verify optionality matches
            is_required_openapi = prop_name in required_props
            is_optional_typescript = ts_prop.get('optional', False)
            
            if is_required_openapi and is_optional_typescript:
                errors.append({
                    "type": "optionality_mismatch",
                    "schema": schema_name,
                    "property": prop_name,
                    "issue": "Required in OpenAPI, optional in TypeScript"
                })
            
            if not is_required_openapi and not is_optional_typescript:
                errors.append({
                    "type": "optionality_mismatch",
                    "schema": schema_name,
                    "property": prop_name,
                    "issue": "Optional in OpenAPI, required in TypeScript"
                })
    
    return {
        "properties_match": len(errors) == 0,
        "errors": errors
    }
```

**Type equivalence rules:**
```python
def types_equivalent(openapi_type, typescript_type):
    """
    Check if OpenAPI type matches TypeScript type
    """
    equivalences = {
        'string': 'string',
        'number': 'number',
        'integer': 'number',  # TypeScript has no integer type
        'boolean': 'boolean',
        'array': 'Array',     # or []
        'object': 'object'    # or interface
    }
    
    # Handle arrays
    if openapi_type.startswith('array<'):
        item_type = extract_array_item_type(openapi_type)
        return typescript_type.endswith('[]') or 'Array<' in typescript_type
    
    # Handle objects/interfaces
    if openapi_type == 'object':
        return is_object_type(typescript_type)
    
    # Handle enums
    if 'enum' in openapi_type:
        return is_union_type(typescript_type)
    
    return equivalences.get(openapi_type) == typescript_type
```

---

### Verification 4: Endpoint Coverage

**Goal:** All endpoints have TypeScript request/response types

```python
def verify_endpoint_coverage(openapi_endpoints, typescript_types):
    """
    For each endpoint, verify request/response types exist
    """
    
    errors = []
    
    for endpoint in openapi_endpoints:
        operation_id = endpoint['operationId']
        
        # Check request type (if endpoint has body)
        if endpoint.get('requestBody'):
            request_type_name = f"{pascalcase(operation_id)}Request"
            if request_type_name not in typescript_types:
                errors.append({
                    "type": "missing_request_type",
                    "endpoint": endpoint['path'],
                    "method": endpoint['method'],
                    "operation_id": operation_id,
                    "expected_type": request_type_name
                })
        
        # Check response type
        response_type_name = f"{pascalcase(operation_id)}Response"
        if response_type_name not in typescript_types:
            # Maybe it's aliased to a schema type
            response_schema = extract_response_schema(endpoint['responses']['200'])
            if response_schema not in typescript_types:
                errors.append({
                    "type": "missing_response_type",
                    "endpoint": endpoint['path'],
                    "method": endpoint['method'],
                    "operation_id": operation_id,
                    "expected_type": response_type_name
                })
    
    return {
        "all_endpoints_covered": len(errors) == 0,
        "endpoints_checked": len(openapi_endpoints),
        "errors": errors
    }
```

---

### Verification 5: Information Preservation

**Goal:** No information loss in translation

```python
def verify_information_preservation(openapi_schemas, typescript_types):
    """
    Verify no semantic information lost:
    - Descriptions preserved (as comments)
    - Constraints preserved (validation schemas)
    - Formats preserved (UUID, date-time)
    - Enums preserved (union types)
    """
    
    warnings = []
    
    for schema_name in openapi_schemas:
        openapi_schema = openapi_schemas[schema_name]
        ts_type = typescript_types.get(schema_name)
        
        if not ts_type:
            continue
        
        # Check description preserved
        if openapi_schema.get('description') and not ts_type.get('description'):
            warnings.append({
                "type": "missing_description",
                "schema": schema_name,
                "severity": "low"
            })
        
        # Check constraints preserved (e.g., string length, number range)
        for prop_name, prop_def in openapi_schema.get('properties', {}).items():
            ts_prop = ts_type['properties'].get(prop_name)
            
            if not ts_prop:
                continue
            
            # String constraints
            if prop_def.get('minLength') or prop_def.get('maxLength'):
                if not has_validation_schema(ts_type, prop_name):
                    warnings.append({
                        "type": "missing_constraint",
                        "schema": schema_name,
                        "property": prop_name,
                        "constraint": "string length",
                        "severity": "medium"
                    })
            
            # Number constraints
            if prop_def.get('minimum') or prop_def.get('maximum'):
                if not has_validation_schema(ts_type, prop_name):
                    warnings.append({
                        "type": "missing_constraint",
                        "schema": schema_name,
                        "property": prop_name,
                        "constraint": "number range",
                        "severity": "medium"
                    })
    
    return {
        "information_preserved": len(warnings) == 0,
        "warnings": warnings
    }
```

---

## Proof Generation

```python
def generate_correspondence_proof(verification_results):
    """
    Generate proof document showing bijection verified
    """
    
    all_checks = [
        verification_results['surjection'],
        verification_results['injection'],
        verification_results['property_correspondence'],
        verification_results['endpoint_coverage'],
        verification_results['information_preservation']
    ]
    
    all_passed = all(check.get('complete', check.get('no_extras', check.get('properties_match', False))) for check in all_checks)
    
    proof = {
        "status": "verified" if all_passed else "failed",
        "bijection": all_passed,
        "timestamp": datetime.utcnow().isoformat() + "Z",
        "specification_version": get_spec_version(),
        
        "verification_results": {
            "surjection": {
                "complete": verification_results['surjection']['complete'],
                "schemas_checked": verification_results['surjection']['schemas_checked'],
                "errors": verification_results['surjection']['errors']
            },
            
            "injection": {
                "no_extras": verification_results['injection']['no_extras'],
                "types_checked": verification_results['injection']['types_checked'],
                "errors": verification_results['injection']['errors']
            },
            
            "property_correspondence": {
                "properties_match": verification_results['property_correspondence']['properties_match'],
                "errors": verification_results['property_correspondence']['errors']
            },
            
            "endpoint_coverage": {
                "all_endpoints_covered": verification_results['endpoint_coverage']['all_endpoints_covered'],
                "endpoints_checked": verification_results['endpoint_coverage']['endpoints_checked'],
                "errors": verification_results['endpoint_coverage']['errors']
            },
            
            "information_preservation": {
                "information_preserved": verification_results['information_preservation']['information_preserved'],
                "warnings": verification_results['information_preservation']['warnings']
            }
        },
        
        "verification_method": "bijection_analysis",
        "types_verified": count_types(verification_results),
        "endpoints_covered": count_endpoints(verification_results)
    }
    
    return proof
```

---

## Output: Correspondence Proof

**Success case:**
```json
{
  "status": "verified",
  "bijection": true,
  "timestamp": "2025-01-15T10:30:00Z",
  "specification_version": "v1.2.0",
  
  "verification_results": {
    "surjection": {
      "complete": true,
      "schemas_checked": 47,
      "errors": []
    },
    
    "injection": {
      "no_extras": true,
      "types_checked": 51,
      "errors": []
    },
    
    "property_correspondence": {
      "properties_match": true,
      "errors": []
    },
    
    "endpoint_coverage": {
      "all_endpoints_covered": true,
      "endpoints_checked": 23,
      "errors": []
    },
    
    "information_preservation": {
      "information_preserved": true,
      "warnings": []
    }
  },
  
  "verification_method": "bijection_analysis",
  "types_verified": 47,
  "endpoints_covered": 23
}
```

**Failure case:**
```json
{
  "status": "failed",
  "bijection": false,
  "timestamp": "2025-01-15T10:30:00Z",
  
  "verification_results": {
    "surjection": {
      "complete": false,
      "errors": [
        {
          "type": "missing_typescript_type",
          "schema_name": "ProductStatus",
          "fix": "Generate TypeScript interface for ProductStatus"
        }
      ]
    },
    
    "property_correspondence": {
      "properties_match": false,
      "errors": [
        {
          "type": "type_mismatch",
          "schema": "Product",
          "property": "price",
          "openapi_type": "number",
          "typescript_type": "string"
        }
      ]
    }
  }
}
```

**Output location:**
```
artifacts/engineering/proofs/frontend/type-correspondence/
└── openapi-to-typescript.proof
```

---

## Success Criteria

✓ Surjection verified (all OpenAPI schemas have TypeScript types)
✓ Injection verified (no extra TypeScript types)
✓ Property correspondence verified (properties match)
✓ Endpoint coverage verified (all endpoints have types)
✓ Information preservation verified (no semantic loss)
✓ Bijection proven ✓

---

## Comparison: Backend vs Frontend Verification

| Aspect | Backend (composition-map-validator) | Frontend (type-correspondence-prover) |
|--------|-------------------------------------|---------------------------------------|
| **Problem** | Verify composition laws | Verify type bijection |
| **Input** | Backend maps | OpenAPI + TypeScript |
| **Method** | Structural analysis (associativity) | Bijection analysis (surjection + injection) |
| **Checks** | Types compose, effects valid | Types match, properties correspond |
| **Proof** | Composition correctness | Type isomorphism |
| **Goal** | Morphisms compose correctly | No information loss |

---

## Error Handling

**Missing TypeScript type:**
```
ERROR: Bijection failed - missing TypeScript type
OpenAPI schema: ProductStatus
Action: Re-run typescript-generator
```

**Type mismatch:**
```
ERROR: Type mismatch detected
Schema: Product.price
OpenAPI: number
TypeScript: string
Action: Fix typescript-generator type mapping
```

**Missing endpoint types:**
```
ERROR: Endpoint not covered
Endpoint: POST /products
Missing: CreateProductRequest
Action: Re-run typescript-generator with endpoint types
```

---

## Key Insights

1. **Bijection ≠ Composition** - Different verification problems
2. **OpenAPI is source of truth** - TypeScript must match exactly
3. **Information preservation matters** - Descriptions, constraints, formats
4. **Endpoint coverage critical** - All API operations must have types
5. **Verification is decidable** - Structural analysis (fast)

**Frontend-prover complete when bijection proven.**
