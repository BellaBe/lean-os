---
name: openapi-parser
description: Parse OpenAPI 3.0 schema and extract types, endpoints, security requirements. Normalizes $ref references and builds internal AST for type generation. Sub-skill of frontend-prover.
version: 1.0.0
allowed-tools: bash_tool, view
model: claude-sonnet-4-20250514
license: Proprietary - LeanOS Engineering Layer
---

# openapi-parser: OpenAPI Schema → Internal AST

## Purpose

Parse OpenAPI 3.0 schema and extract structured information for type generation.

**Input:** OpenAPI JSON schema  
**Output:** Internal AST (Abstract Syntax Tree) as JSON

---

## Input

```
artifacts/engineering/specifications/v{X}/api.openapi.json
```

**Expected structure (OpenAPI 3.0):**
```json
{
  "openapi": "3.0.0",
  "info": {
    "title": "Catalog API",
    "version": "1.0.0"
  },
  "paths": {
    "/products": {
      "get": {
        "operationId": "getProducts",
        "responses": {
          "200": {
            "content": {
              "application/json": {
                "schema": {"$ref": "#/components/schemas/ProductList"}
              }
            }
          }
        }
      }
    }
  },
  "components": {
    "schemas": {
      "Product": {
        "type": "object",
        "properties": {
          "id": {"type": "string", "format": "uuid"},
          "title": {"type": "string"},
          "price": {"type": "number"}
        },
        "required": ["id", "title", "price"]
      },
      "ProductList": {
        "type": "object",
        "properties": {
          "items": {
            "type": "array",
            "items": {"$ref": "#/components/schemas/Product"}
          },
          "total": {"type": "integer"}
        }
      }
    },
    "securitySchemes": {
      "bearerAuth": {
        "type": "http",
        "scheme": "bearer"
      }
    }
  }
}
```

---

## Parsing Process

### Step 1: Validate OpenAPI Version

```python
import json

def validate_openapi(schema):
    """Verify OpenAPI 3.0.x schema"""
    if 'openapi' not in schema:
        raise ValueError("Missing 'openapi' field")
    
    version = schema['openapi']
    if not version.startswith('3.0'):
        raise ValueError(f"Unsupported OpenAPI version: {version}. Expected 3.0.x")
    
    if 'paths' not in schema:
        raise ValueError("Missing required field 'paths'")
    
    if 'components' not in schema or 'schemas' not in schema['components']:
        raise ValueError("Missing 'components.schemas'")
    
    return True
```

---

### Step 2: Extract Schemas (Types)

```python
def extract_schemas(openapi_schema):
    """
    Extract all type definitions from components/schemas
    
    Returns dict mapping schema name to definition
    """
    schemas = openapi_schema.get('components', {}).get('schemas', {})
    
    extracted = {}
    
    for schema_name, schema_def in schemas.items():
        extracted[schema_name] = {
            'name': schema_name,
            'type': schema_def.get('type', 'object'),
            'properties': schema_def.get('properties', {}),
            'required': schema_def.get('required', []),
            'description': schema_def.get('description', ''),
            'enum': schema_def.get('enum', None),
            'oneOf': schema_def.get('oneOf', None),
            'anyOf': schema_def.get('anyOf', None),
            'allOf': schema_def.get('allOf', None),
            'items': schema_def.get('items', None),
            'additionalProperties': schema_def.get('additionalProperties', None)
        }
    
    return extracted
```

**Example output:**
```json
{
  "Product": {
    "name": "Product",
    "type": "object",
    "properties": {
      "id": {"type": "string", "format": "uuid"},
      "title": {"type": "string"},
      "price": {"type": "number"}
    },
    "required": ["id", "title", "price"],
    "description": "Product entity"
  }
}
```

---

### Step 3: Extract Endpoints

```python
def extract_endpoints(openapi_schema):
    """
    Extract all API endpoints from paths
    
    Returns list of endpoint definitions
    """
    paths = openapi_schema.get('paths', {})
    endpoints = []
    
    for path, path_def in paths.items():
        for method, operation in path_def.items():
            if method in ['get', 'post', 'put', 'patch', 'delete']:
                endpoint = {
                    'path': path,
                    'method': method.upper(),
                    'operationId': operation.get('operationId', f"{method}_{path.replace('/', '_')}"),
                    'summary': operation.get('summary', ''),
                    'description': operation.get('description', ''),
                    'parameters': extract_parameters(operation.get('parameters', [])),
                    'requestBody': extract_request_body(operation.get('requestBody', {})),
                    'responses': extract_responses(operation.get('responses', {})),
                    'security': operation.get('security', None)
                }
                endpoints.append(endpoint)
    
    return endpoints

def extract_parameters(parameters):
    """Extract path/query parameters"""
    extracted = []
    for param in parameters:
        extracted.append({
            'name': param['name'],
            'in': param['in'],  # path, query, header, cookie
            'required': param.get('required', False),
            'schema': param.get('schema', {}),
            'description': param.get('description', '')
        })
    return extracted

def extract_request_body(request_body):
    """Extract request body schema"""
    if not request_body:
        return None
    
    content = request_body.get('content', {})
    json_content = content.get('application/json', {})
    
    return {
        'required': request_body.get('required', False),
        'schema': json_content.get('schema', {})
    }

def extract_responses(responses):
    """Extract response schemas"""
    extracted = {}
    
    for status_code, response_def in responses.items():
        content = response_def.get('content', {})
        json_content = content.get('application/json', {})
        
        extracted[status_code] = {
            'description': response_def.get('description', ''),
            'schema': json_content.get('schema', {})
        }
    
    return extracted
```

**Example output:**
```json
{
  "path": "/products",
  "method": "GET",
  "operationId": "getProducts",
  "parameters": [
    {
      "name": "page",
      "in": "query",
      "required": false,
      "schema": {"type": "integer"}
    }
  ],
  "responses": {
    "200": {
      "description": "Success",
      "schema": {"$ref": "#/components/schemas/ProductList"}
    }
  }
}
```

---

### Step 4: Normalize References

```python
def normalize_refs(openapi_schema, extracted_schemas):
    """
    Resolve all $ref references to actual schemas
    
    Replaces {"$ref": "#/components/schemas/Product"}
    with actual Product schema definition
    """
    
    def resolve_ref(ref_string):
        """Resolve #/components/schemas/Product to schema definition"""
        if not ref_string.startswith('#/components/schemas/'):
            raise ValueError(f"Unsupported $ref: {ref_string}")
        
        schema_name = ref_string.split('/')[-1]
        
        if schema_name not in extracted_schemas:
            raise ValueError(f"Cannot resolve $ref: {schema_name} not found")
        
        return extracted_schemas[schema_name]
    
    def walk_and_resolve(obj):
        """Recursively resolve all $ref in object"""
        if isinstance(obj, dict):
            if '$ref' in obj:
                return resolve_ref(obj['$ref'])
            else:
                return {k: walk_and_resolve(v) for k, v in obj.items()}
        elif isinstance(obj, list):
            return [walk_and_resolve(item) for item in obj]
        else:
            return obj
    
    return walk_and_resolve(openapi_schema)
```

---

### Step 5: Extract Security Requirements

```python
def extract_security(openapi_schema):
    """
    Extract security schemes and requirements
    """
    security_schemes = openapi_schema.get('components', {}).get('securitySchemes', {})
    global_security = openapi_schema.get('security', [])
    
    extracted = {
        'schemes': {},
        'global': global_security
    }
    
    for scheme_name, scheme_def in security_schemes.items():
        extracted['schemes'][scheme_name] = {
            'type': scheme_def['type'],  # http, apiKey, oauth2, openIdConnect
            'scheme': scheme_def.get('scheme', ''),  # bearer, basic
            'bearerFormat': scheme_def.get('bearerFormat', ''),  # JWT
            'in': scheme_def.get('in', ''),  # header, query, cookie
            'name': scheme_def.get('name', '')  # header name for apiKey
        }
    
    return extracted
```

**Example output:**
```json
{
  "schemes": {
    "bearerAuth": {
      "type": "http",
      "scheme": "bearer",
      "bearerFormat": "JWT"
    }
  },
  "global": [
    {"bearerAuth": []}
  ]
}
```

---

## Output: Internal AST

**Complete AST structure:**
```json
{
  "openapi_version": "3.0.0",
  "api_info": {
    "title": "Catalog API",
    "version": "1.0.0",
    "description": "Multi-tenant catalog API"
  },
  
  "schemas": {
    "Product": {
      "name": "Product",
      "type": "object",
      "properties": {
        "id": {"type": "string", "format": "uuid"},
        "title": {"type": "string"},
        "price": {"type": "number"}
      },
      "required": ["id", "title", "price"]
    },
    "ProductList": {
      "name": "ProductList",
      "type": "object",
      "properties": {
        "items": {
          "type": "array",
          "items": {
            "name": "Product",
            "type": "object",
            "properties": {...}
          }
        },
        "total": {"type": "integer"}
      },
      "required": ["items", "total"]
    }
  },
  
  "endpoints": [
    {
      "path": "/products",
      "method": "GET",
      "operationId": "getProducts",
      "parameters": [
        {
          "name": "page",
          "in": "query",
          "required": false,
          "schema": {"type": "integer"}
        }
      ],
      "responses": {
        "200": {
          "description": "Success",
          "schema": {
            "name": "ProductList",
            "type": "object",
            "properties": {...}
          }
        }
      },
      "security": [{"bearerAuth": []}]
    },
    {
      "path": "/products",
      "method": "POST",
      "operationId": "createProduct",
      "requestBody": {
        "required": true,
        "schema": {
          "name": "ProductCreateRequest",
          "type": "object",
          "properties": {...}
        }
      },
      "responses": {
        "201": {
          "description": "Created",
          "schema": {"name": "Product", ...}
        }
      }
    }
  ],
  
  "security": {
    "schemes": {
      "bearerAuth": {
        "type": "http",
        "scheme": "bearer",
        "bearerFormat": "JWT"
      }
    },
    "global": [{"bearerAuth": []}]
  }
}
```

---

## Output Location

**AST saved to:**
```
artifacts/engineering/code/frontend/.internal/openapi-ast.json
```

(Internal file, not part of final output)

---

## Success Criteria

✓ OpenAPI 3.0 schema validated
✓ All schemas extracted from components/schemas
✓ All endpoints extracted from paths
✓ All $ref references normalized
✓ Security schemes extracted
✓ AST generated as valid JSON

---

## Error Handling

**Invalid OpenAPI version:**
```
ERROR: Unsupported OpenAPI version: 2.0
Expected: 3.0.x
Action: Update OpenAPI schema to 3.0
```

**Missing required fields:**
```
ERROR: Missing required field 'paths'
Action: Check system-architect OpenAPI generation
```

**Unresolvable reference:**
```
ERROR: Cannot resolve $ref: Product not found in components/schemas
Action: Check OpenAPI schema completeness
```

**Invalid schema structure:**
```
ERROR: Schema 'Product' missing 'type' field
Action: Verify OpenAPI schema validity
```

---

## Key Insights

1. **OpenAPI is the contract** - Single source of truth for frontend types
2. **$ref resolution is critical** - Must normalize all references
3. **AST is internal** - Not exposed to user, only for type generation
4. **Validation is strict** - Better to fail fast on invalid schema
5. **Security matters** - Auth requirements propagate to client

**Next:** typescript-generator uses this AST to generate TypeScript interfaces
