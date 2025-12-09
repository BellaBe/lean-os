---
name: frontend-prover
description: Type-safe frontend generation with type correspondence verification. Generates TypeScript types and framework-specific bindings ({Platform} Remix, React, Vue, vanilla) from OpenAPI schema. Proves bijection between backend API types and frontend types. Use when engineering thread requests frontend implementation.
version: 1.0.0
allowed-tools: bash_tool, create_file, view, str_replace
model: claude-sonnet-4-20250514
license: Proprietary - LeanOS Engineering Layer
---

# frontend-prover: Type-Safe Frontend Generation

## Purpose

Generate type-safe frontend matching backend API with **type correspondence verification** (not composition verification like backend).

**Key insight:** Frontend verification is about **bijective type mapping**, not composition laws.

**Process:**
1. Parse OpenAPI schema (backend API contract)
2. Generate TypeScript types (bijective mapping)
3. Generate framework-specific bindings
4. Prove type correspondence (no information loss)

---

## Position in Engineering Layer

You are skill #4 of 6:

1. **system-architect** - Requirements → Specifications + Curry-Howard proofs
2. **backend-prover** - Specifications → Maps → Code + Runtime monitors
3. **standardization-layer** - Code → Middleware injection (naturality proofs)
4. **frontend-prover** (YOU) - OpenAPI → TypeScript + Framework bindings + Type correspondence proof
5. **infrastructure-prover** - Services spec → Deployment configs (topology isomorphism)
6. **proof-composer** - Validates entire proof chain

---

## Input Requirements

**From system-architect:**
```
artifacts/engineering/specifications/v{X}/
├── manifest.json                    # Version hash (locked)
└── api.openapi.json                 # OpenAPI 3.0 schema (backend API contract)
```

**From thread:**
```
threads/engineering/{requirement}/5-actions/action-3-frontend.md

Execute frontend-prover:
  framework: {platform}-remix | react | vue | vanilla
  features:
    - API client
    - State management
    - Components (optional)
```

---

## Output Guarantees

```
artifacts/engineering/code/frontend/
├── types/
│   └── api.ts                       # TypeScript types (framework-agnostic)
├── client/
│   └── api-client.ts                # API client layer
├── framework/
│   ├── {platform}-remix/               # Remix-specific bindings
│   ├── react/                       # React-specific bindings
│   ├── vue/                         # Vue-specific bindings
│   └── vanilla/                     # Framework-free
└── components/                       # Optional scaffolding

artifacts/engineering/proofs/frontend/
├── type-correspondence/
│   └── openapi-to-typescript.proof  # Bijection proof
├── framework-correctness/
└── state-consistency/
```

---

## Why Type Correspondence (Not Composition)?

**Backend verification problem:** Composition laws (morphisms compose correctly)
**Frontend verification problem:** Type correspondence (types match backend exactly)

**Reasoning:**
- OpenAPI schema already defines complete API contract
- TypeScript types directly map to OpenAPI schemas (bijective)
- No composition to verify (framework handles data flow)
- Goal: Prove frontend types ≅ backend types (isomorphism)

**What we verify:**
- Every OpenAPI type has TypeScript equivalent
- Every TypeScript type maps to OpenAPI type
- No information loss in translation
- All endpoints covered

---

## Orchestration Flow

### Pre-check: Validate OpenAPI Exists

```bash
spec_version=$(jq -r '.version' artifacts/engineering/specifications/manifest.json)
spec_hash=$(jq -r '.hash' artifacts/engineering/specifications/manifest.json)

if [ ! -f "artifacts/engineering/specifications/v${spec_version}/api.openapi.json" ]; then
    echo "ERROR: OpenAPI schema not found. Run system-architect first."
    exit 1
fi

echo "✓ Using OpenAPI schema from specification v$spec_version (hash: $spec_hash)"
```

---

### Step 1: Parse OpenAPI Schema

**Invoke sub-skill:** `openapi-parser`

**Purpose:** Extract types and endpoints from OpenAPI schema

**Input:**
- `artifacts/engineering/specifications/v{X}/api.openapi.json`

**Output:**
- Internal JSON representation (AST)
- Endpoint definitions
- Request/response types
- Authentication requirements

**What it does:**
- Parses OpenAPI 3.0 schema
- Extracts `components/schemas` (types)
- Extracts `paths` (endpoints)
- Extracts `security` (auth requirements)
- Normalizes references (`$ref`)

---

### Step 2: Generate TypeScript Types

**Invoke sub-skill:** `typescript-generator`

**Purpose:** Generate TypeScript interfaces from OpenAPI schemas

**Input:**
- Parsed OpenAPI AST (from step 1)

**Output:**
- `artifacts/engineering/code/frontend/types/api.ts`

**What it does:**
- OpenAPI schemas → TypeScript interfaces
- Handles primitive types (string, number, boolean)
- Handles complex types (objects, arrays)
- Handles enums
- Handles `oneOf`, `anyOf`, `allOf`
- Generates type guards
- Generates validation schemas

**Key property:** **Framework-agnostic** (pure TypeScript types)

---

### Step 3: Generate Framework Bindings

**Invoke sub-skill:** `framework-adapter`

**Purpose:** Generate framework-specific API client and bindings

**Input:**
- TypeScript types (from step 2)
- Framework choice (from thread)
- Parsed OpenAPI (for endpoint details)

**Output:**
- API client layer
- Framework-specific bindings:
  - **{Platform} Remix:** Loaders, actions, {Platform} App Bridge
  - **React:** Hooks (useState, useEffect, custom)
  - **Vue:** Composition API, composables
  - **Vanilla:** Pure fetch API

**What it does:**
- Generates API client (HTTP layer)
- Generates framework-specific wrappers
- Handles authentication
- Handles state management (if requested)
- Generates error handling

---

### Step 4: Prove Type Correspondence

**Invoke sub-skill:** `type-correspondence-prover`

**Purpose:** Verify TypeScript types bijective with OpenAPI schemas

**Input:**
- OpenAPI schema (original)
- Generated TypeScript types

**Output:**
- `artifacts/engineering/proofs/frontend/type-correspondence/openapi-to-typescript.proof`

**What it verifies:**
1. **Surjection:** Every OpenAPI type has TypeScript equivalent
2. **Injection:** Every TypeScript type maps to OpenAPI type
3. **Bijection:** One-to-one correspondence (no information loss)
4. **Coverage:** All endpoints have TypeScript definitions

**Proof structure:**
```json
{
  "status": "verified",
  "bijection": true,
  "types_verified": 47,
  "endpoints_covered": 23,
  "verification_method": "structural_analysis"
}
```

---

## Orchestration Summary

**Execution sequence:**

```
1. Validate OpenAPI schema exists (system-architect output)
   ↓
2. Parse OpenAPI
   └─ 4.1: openapi-parser (schema → AST)
   ↓
3. Generate TypeScript Types
   └─ 4.2: typescript-generator (AST → types.ts)
   ↓
4. Generate Framework Bindings
   └─ 4.3: framework-adapter (types + framework → client + bindings)
   ↓
5. Prove Type Correspondence
   └─ 4.4: type-correspondence-prover (schema + types → proof)
   ↓
6. Output: Type-safe frontend + correspondence proof
```

---

## Usage Examples

### Example 1: Platform-Specific Frontend

```bash
# Thread action invokes frontend-prover
# Input: threads/engineering/{feature-sync}/5-actions/action-3-frontend.md
#   framework: {platform}-remix
#   features: [API client, state management]

# Execution
✓ OpenAPI schema loaded (v1.2.0, 23 endpoints)
✓ Types generated (47 interfaces, api.ts)
✓ {Platform} Remix bindings generated (loaders, actions, App Bridge)
✓ Type correspondence verified (bijection: true)

# Output
artifacts/engineering/code/frontend/
├── types/api.ts                     (47 interfaces)
├── client/api-client.ts             (HTTP layer)
└── framework/{platform}-remix/
    ├── entities.tsx                 (loader + component)
    ├── transactions.tsx             (action + component)
    └── auth.tsx                     ({Platform} App Bridge)

artifacts/engineering/proofs/frontend/type-correspondence/
└── openapi-to-typescript.proof      (verified)
```

---

### Example 2: React Frontend

```bash
# Thread action
#   framework: react
#   features: [API client, hooks, state management]

# Execution
✓ OpenAPI schema loaded (v1.2.0)
✓ Types generated (api.ts)
✓ React hooks generated (useEntities, useTransactions)
✓ Type correspondence verified

# Output
artifacts/engineering/code/frontend/
├── types/api.ts
├── client/api-client.ts
└── framework/react/
    ├── hooks/
    │   ├── useEntities.ts
    │   ├── useTransactions.ts
    │   └── useAuth.ts
    └── context/
        └── ApiContext.tsx
```

---

### Example 3: Vue Frontend

```bash
# Thread action
#   framework: vue
#   features: [API client, composables]

# Execution
✓ OpenAPI schema loaded
✓ Types generated
✓ Vue composables generated (useEntities, useTransactions)
✓ Type correspondence verified

# Output
artifacts/engineering/code/frontend/
├── types/api.ts
├── client/api-client.ts
└── framework/vue/
    ├── composables/
    │   ├── useEntities.ts
    │   ├── useTransactions.ts
    │   └── useAuth.ts
    └── stores/
        └── api.ts
```

---

## Sub-skill Responsibilities

### 4.1: openapi-parser
- Parse OpenAPI 3.0 schema
- Extract schemas (components/schemas)
- Extract endpoints (paths)
- Extract security requirements
- Normalize `$ref` references
- Output: Internal AST (JSON)

### 4.2: typescript-generator
- Generate TypeScript interfaces from schemas
- Handle primitive types
- Handle complex types (objects, arrays, enums)
- Generate type guards
- Generate validation schemas
- Output: types/api.ts (framework-agnostic)

### 4.3: framework-adapter
- Generate API client (HTTP layer)
- Generate framework-specific bindings:
  - {Platform} Remix: loaders, actions
  - React: hooks, context
  - Vue: composables, stores
  - Vanilla: pure functions
- Handle authentication
- Handle state management
- Output: framework/{framework}/*

### 4.4: type-correspondence-prover
- Verify TypeScript types ↔ OpenAPI schemas (bijection)
- Check all endpoints covered
- Verify no information loss
- Generate correspondence proof
- Output: proofs/frontend/type-correspondence/openapi-to-typescript.proof

---

## Success Criteria

**Complete when:**
- OpenAPI schema parsed ✓
- TypeScript types generated ✓
- Framework bindings generated ✓
- Type correspondence verified ✓
- Proof generated ✓

**Type correspondence verified means:**
- Every OpenAPI schema has TypeScript interface ✓
- Every TypeScript interface maps to OpenAPI schema ✓
- Bijection proven (one-to-one) ✓
- All endpoints covered ✓
- No information loss ✓

---

## Error Handling

### OpenAPI Parsing Errors

**Schema not found:**
```
ERROR: OpenAPI schema not found at specifications/v{X}/api.openapi.json
Action: Run system-architect first
```

**Invalid OpenAPI:**
```
ERROR: Invalid OpenAPI 3.0 schema
Detail: Missing required field 'paths'
Action: Check system-architect output
```

### Type Generation Errors

**Unsupported type:**
```
ERROR: Unsupported OpenAPI type 'custom'
Action: Report to system-architect for ADT definition
```

**Reference resolution failed:**
```
ERROR: Cannot resolve $ref '#/components/schemas/Product'
Action: Check OpenAPI schema completeness
```

### Framework Adapter Errors

**Unsupported framework:**
```
ERROR: Framework 'angular' not supported
Supported: {platform}-remix, react, vue, vanilla
Action: Choose supported framework or add adapter
```

### Type Correspondence Errors

**Bijection failed:**
```
ERROR: Type correspondence verification failed
Missing TypeScript interface for OpenAPI schema 'Product'
Action: Check typescript-generator output
```

---

## Integration with Build Pipeline

**Build pipeline invokes frontend-prover:**

```bash
# build-pipeline/7-generate-frontend.sh

# Step 1: Parse OpenAPI
frontend-prover parse-openapi

# Step 2: Generate TypeScript types
frontend-prover generate-types

# Step 3: Generate framework bindings
frontend-prover generate-framework --framework={platform}-remix

# Step 4: Verify type correspondence
frontend-prover verify-correspondence

# Check verification passed
if [ "$(jq -r '.bijection' proofs/frontend/type-correspondence/openapi-to-typescript.proof)" != "true" ]; then
    echo "VERIFICATION FAILED: Type correspondence not proven"
    exit 1
fi

echo "✓ Frontend generation complete (type correspondence verified)"
```

---

## Critical Reminders

1. **Type correspondence ≠ composition verification** - Different verification problem
2. **OpenAPI is source of truth** - Backend contract defines frontend types
3. **TypeScript types are framework-agnostic** - Reusable across frameworks
4. **Bijection is mandatory** - No information loss allowed
5. **Framework adapter is thin layer** - Types do the heavy lifting

---

## Comparison: Backend vs Frontend Verification

| Aspect | Backend (backend-prover) | Frontend (frontend-prover) |
|--------|--------------------------|----------------------------|
| **Problem** | Composition verification | Type correspondence |
| **Input** | ADT, functors, composition | OpenAPI schema |
| **Output** | Services, composition utils | Types, API client, bindings |
| **Verification** | Composition laws (associativity) | Bijection (types match) |
| **Method** | Structural analysis (maps) | Type mapping (isomorphism) |
| **Proof** | Composition correctness | Type correspondence |
| **Why different?** | Services compose | Data flows through framework |

---

## When You (frontend-prover) Finish

1. **Log results** in thread:
   ```
   threads/engineering/{requirement}/5-actions/action-3-frontend.md
   
   Status: Complete
   Types: artifacts/engineering/code/frontend/types/api.ts
   Framework: {platform}-remix
   Client: artifacts/engineering/code/frontend/client/api-client.ts
   Bindings: artifacts/engineering/code/frontend/framework/{platform}-remix/
   Proof: artifacts/engineering/proofs/frontend/type-correspondence/
   Verification: PASSED (bijection: true)
   ```

2. **Notify infrastructure-prover** (skill #5):
   - Frontend code ready for deployment config
   - Location: artifacts/engineering/code/frontend/

3. **Update engineering thread Stage 5**:
   - Action 3 complete ✓
   - Ready for Action 4 (infrastructure-prover)

---

**You are an orchestrator. Coordinate sub-skills, ensure type correspondence, prove bijection.**