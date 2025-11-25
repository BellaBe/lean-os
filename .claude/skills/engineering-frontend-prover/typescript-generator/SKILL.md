---
name: typescript-generator
description: Generate TypeScript interfaces from OpenAPI AST. Handles primitive types, complex types, enums, oneOf/anyOf/allOf. Generates type guards and validation schemas. Framework-agnostic output. Sub-skill of frontend-prover.
version: 1.0.0
allowed-tools: bash_tool, create_file
model: claude-sonnet-4-20250514
license: Proprietary - LeanOS Engineering Layer
---

# typescript-generator: OpenAPI AST → TypeScript Types

## Purpose

Generate TypeScript interfaces from parsed OpenAPI AST. Output is **framework-agnostic** (pure TypeScript).

**Input:** OpenAPI AST (from openapi-parser)  
**Output:** TypeScript type definitions

---

## Input

```
artifacts/engineering/code/frontend/.internal/openapi-ast.json
```

---

## Type Mapping Rules

### Primitive Types

| OpenAPI | TypeScript |
|---------|------------|
| `string` | `string` |
| `number` | `number` |
| `integer` | `number` |
| `boolean` | `boolean` |
| `null` | `null` |

### Format Modifiers

| Format | TypeScript |
|--------|------------|
| `format: "uuid"` | `string // UUID` |
| `format: "date"` | `string // ISO date` |
| `format: "date-time"` | `string // ISO datetime` |
| `format: "email"` | `string // Email` |
| `format: "uri"` | `string // URI` |

### Complex Types

**Object:**
```typescript
// OpenAPI
{
  "type": "object",
  "properties": {
    "id": {"type": "string"},
    "name": {"type": "string"}
  },
  "required": ["id"]
}

// TypeScript
interface ObjectName {
  id: string;
  name?: string;
}
```

**Array:**
```typescript
// OpenAPI
{
  "type": "array",
  "items": {"type": "string"}
}

// TypeScript
type ArrayName = string[];
```

**Enum:**
```typescript
// OpenAPI
{
  "type": "string",
  "enum": ["active", "draft", "archived"]
}

// TypeScript
type StatusEnum = "active" | "draft" | "archived";
```

---

## Generation Process

### Step 1: Generate Base Interfaces

```typescript
// Generated header
/**
 * Generated from: artifacts/engineering/specifications/v1.2.0/api.openapi.json
 * Specification version: v1.2.0
 * Generated at: 2025-01-15T10:30:00Z
 * 
 * DO NOT EDIT MANUALLY - Regenerate from OpenAPI schema
 * 
 * This file contains TypeScript type definitions matching the backend API.
 * Types are framework-agnostic and can be used with any framework.
 */

// Generate from AST schemas
export interface Product {
  /** Product unique identifier (UUID) */
  id: string;
  
  /** Product title */
  title: string;
  
  /** Product price */
  price: number;
  
  /** Product status */
  status: ProductStatus;
  
  /** Created timestamp (ISO datetime) */
  created_at?: string;
}

export interface ProductList {
  /** List of products */
  items: Product[];
  
  /** Total count */
  total: number;
  
  /** Pagination cursor */
  cursor?: string;
}

export type ProductStatus = "active" | "draft" | "archived";
```

---

### Step 2: Handle Optional vs Required

```typescript
def generate_interface_property(prop_name, prop_def, required_fields):
    """
    Generate interface property with correct optionality
    """
    is_required = prop_name in required_fields
    optional_marker = "" if is_required else "?"
    
    type_annotation = map_openapi_type_to_typescript(prop_def)
    description = prop_def.get('description', '')
    
    return f"""
  /** {description} */
  {prop_name}{optional_marker}: {type_annotation};
"""
```

**Example:**
```typescript
// Required field
id: string;

// Optional field
cursor?: string;
```

---

### Step 3: Handle Complex Type Combinators

**oneOf (Union):**
```typescript
// OpenAPI
{
  "oneOf": [
    {"$ref": "#/components/schemas/Cat"},
    {"$ref": "#/components/schemas/Dog"}
  ]
}

// TypeScript
export type Pet = Cat | Dog;
```

**anyOf (Union with overlap allowed):**
```typescript
// OpenAPI
{
  "anyOf": [
    {"type": "string"},
    {"type": "number"}
  ]
}

// TypeScript
export type StringOrNumber = string | number;
```

**allOf (Intersection):**
```typescript
// OpenAPI
{
  "allOf": [
    {"$ref": "#/components/schemas/BaseProduct"},
    {
      "type": "object",
      "properties": {
        "variants": {"type": "array", "items": {"type": "string"}}
      }
    }
  ]
}

// TypeScript
export interface Product extends BaseProduct {
  variants: string[];
}
```

---

### Step 4: Generate Endpoint Types

For each endpoint, generate request/response types:

```typescript
// GET /products endpoint
export interface GetProductsRequest {
  /** Page number for pagination */
  page?: number;
  
  /** Number of items per page */
  limit?: number;
}

export interface GetProductsResponse {
  items: Product[];
  total: number;
  cursor?: string;
}

// POST /products endpoint
export interface CreateProductRequest {
  title: string;
  price: number;
  status: ProductStatus;
}

export interface CreateProductResponse {
  id: string;
  title: string;
  price: number;
  status: ProductStatus;
  created_at: string;
}
```

---

### Step 5: Generate Type Guards

```typescript
/**
 * Type guard for Product
 */
export function isProduct(value: unknown): value is Product {
  return (
    typeof value === 'object' &&
    value !== null &&
    'id' in value &&
    typeof (value as any).id === 'string' &&
    'title' in value &&
    typeof (value as any).title === 'string' &&
    'price' in value &&
    typeof (value as any).price === 'number'
  );
}

/**
 * Type guard for ProductList
 */
export function isProductList(value: unknown): value is ProductList {
  return (
    typeof value === 'object' &&
    value !== null &&
    'items' in value &&
    Array.isArray((value as any).items) &&
    (value as any).items.every(isProduct) &&
    'total' in value &&
    typeof (value as any).total === 'number'
  );
}
```

---

### Step 6: Generate Validation Schemas (Optional)

Using Zod for runtime validation:

```typescript
import { z } from 'zod';

/**
 * Zod schema for Product validation
 */
export const ProductSchema = z.object({
  id: z.string().uuid(),
  title: z.string().min(1),
  price: z.number().positive(),
  status: z.enum(['active', 'draft', 'archived']),
  created_at: z.string().datetime().optional()
});

/**
 * Zod schema for ProductList validation
 */
export const ProductListSchema = z.object({
  items: z.array(ProductSchema),
  total: z.number().int().nonnegative(),
  cursor: z.string().optional()
});

// Type inference from schema
export type ProductValidated = z.infer<typeof ProductSchema>;
```

---

## Complete Output Example

```typescript
/**
 * Generated from: artifacts/engineering/specifications/v1.2.0/api.openapi.json
 * Specification version: v1.2.0
 * Generated at: 2025-01-15T10:30:00Z
 * 
 * DO NOT EDIT MANUALLY - Regenerate from OpenAPI schema
 */

// ============================================================================
// Base Types
// ============================================================================

export interface Product {
  /** Product unique identifier (UUID) */
  id: string;
  
  /** Product title */
  title: string;
  
  /** Product price */
  price: number;
  
  /** Product status */
  status: ProductStatus;
  
  /** Created timestamp (ISO datetime) */
  created_at?: string;
}

export interface ProductList {
  /** List of products */
  items: Product[];
  
  /** Total count */
  total: number;
  
  /** Pagination cursor */
  cursor?: string;
}

export type ProductStatus = "active" | "draft" | "archived";

// ============================================================================
// Endpoint Request/Response Types
// ============================================================================

// GET /products
export interface GetProductsRequest {
  page?: number;
  limit?: number;
}

export type GetProductsResponse = ProductList;

// POST /products
export interface CreateProductRequest {
  title: string;
  price: number;
  status: ProductStatus;
}

export type CreateProductResponse = Product;

// GET /products/{id}
export interface GetProductByIdRequest {
  id: string;
}

export type GetProductByIdResponse = Product;

// PUT /products/{id}
export interface UpdateProductRequest {
  id: string;
  title?: string;
  price?: number;
  status?: ProductStatus;
}

export type UpdateProductResponse = Product;

// ============================================================================
// Type Guards
// ============================================================================

export function isProduct(value: unknown): value is Product {
  return (
    typeof value === 'object' &&
    value !== null &&
    'id' in value &&
    typeof (value as any).id === 'string' &&
    'title' in value &&
    typeof (value as any).title === 'string' &&
    'price' in value &&
    typeof (value as any).price === 'number' &&
    'status' in value &&
    ['active', 'draft', 'archived'].includes((value as any).status)
  );
}

export function isProductList(value: unknown): value is ProductList {
  return (
    typeof value === 'object' &&
    value !== null &&
    'items' in value &&
    Array.isArray((value as any).items) &&
    (value as any).items.every(isProduct) &&
    'total' in value &&
    typeof (value as any).total === 'number'
  );
}

// ============================================================================
// Validation Schemas (Zod)
// ============================================================================

import { z } from 'zod';

export const ProductSchema = z.object({
  id: z.string().uuid(),
  title: z.string().min(1),
  price: z.number().positive(),
  status: z.enum(['active', 'draft', 'archived']),
  created_at: z.string().datetime().optional()
});

export const ProductListSchema = z.object({
  items: z.array(ProductSchema),
  total: z.number().int().nonnegative(),
  cursor: z.string().optional()
});

// ============================================================================
// Error Types
// ============================================================================

export interface ApiError {
  status: number;
  error: string;
  detail?: string;
  meta?: {
    trace_id?: string;
    timestamp?: string;
  };
}

export function isApiError(value: unknown): value is ApiError {
  return (
    typeof value === 'object' &&
    value !== null &&
    'status' in value &&
    typeof (value as any).status === 'number' &&
    'error' in value &&
    typeof (value as any).error === 'string'
  );
}
```

---

## Output Location

```
artifacts/engineering/code/frontend/types/api.ts
```

---

## Success Criteria

✓ All OpenAPI schemas have TypeScript interfaces
✓ All endpoints have request/response types
✓ Optional vs required fields correct
✓ Type guards generated
✓ Validation schemas generated (if requested)
✓ Error types included
✓ Framework-agnostic (pure TypeScript)

---

## Type Generation Rules

**1. Naming conventions:**
- Interfaces: PascalCase (Product, ProductList)
- Types: PascalCase (ProductStatus)
- Properties: snake_case (matching backend)

**2. Documentation:**
- Include descriptions from OpenAPI
- Add format hints (UUID, ISO datetime)
- Note required vs optional

**3. Type safety:**
- Use strict types (no `any`)
- Generate type guards for runtime validation
- Include validation schemas

**4. Framework agnostic:**
- No framework-specific imports
- Pure TypeScript types
- Can be used with any framework

---

## Error Handling

**Unsupported OpenAPI type:**
```
ERROR: Unsupported OpenAPI type 'custom'
Schema: Product.customField
Action: Report to system-architect for ADT definition
```

**Circular reference:**
```
ERROR: Circular reference detected: Product → Category → Product
Action: Use TypeScript recursive types or lazy references
```

**Invalid type definition:**
```
ERROR: Schema 'Product' has invalid property type
Property: price
Expected: string, number, boolean, object, array
Found: custom
Action: Fix OpenAPI schema
```

---

## Key Insights

1. **TypeScript types are framework-agnostic** - Reusable across all frameworks
2. **Type guards enable runtime validation** - Bridge static/runtime types
3. **Validation schemas optional** - Add when runtime validation needed
4. **Naming matches backend** - snake_case properties for API consistency
5. **Documentation matters** - Inline docs from OpenAPI descriptions

**Next:** framework-adapter uses these types to generate framework bindings
