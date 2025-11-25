---
name: adt-analyzer
description: Parse natural language requirements into algebraic data type expressions. Identify products (×), coproducts (+), and apply distributive law to expand paths. Generates canonical sum-of-products form.
allowed-tools: Read, Write, Bash
version: 1.0.0
---

# ADT Analyzer

## Purpose

Parse natural language requirements from `threads/engineering/{requirement}/1-input.md` into algebraic expressions and enumerate all implementation paths.

## Input Format

Natural language requirements describing:
- Entities (nouns → types)
- Choices (OR → coproducts +)
- Combinations (AND → products ×)
- Optionality (Maybe, Option)
- Collections (List, Set)

**Example Input:**
```
Build a {domain} service that:
- Supports multiple tenants (multi-tenant)
- Syncs from {Platform} OR {AltPlatform}
- Has V1 and V2 API versions
- Deploys to Dev, Staging, Prod environments
```

## Output Format

```yaml
# artifacts/engineering/specifications/v{X}/requirements.adt

expression: |
  {Domain}Service = Tenant × Environment × Version × Platform

type_definitions:
  Tenant:
    type: product
    fields:
      - tenant_id: String
      - config: TenantConfig
  
  Environment:
    type: coproduct
    variants:
      - Dev
      - Staging
      - Prod
  
  Version:
    type: coproduct
    variants:
      - V1
      - V2
  
  Platform:
    type: coproduct
    variants:
      - {Platform}
      - {AltPlatform}

expanded_expression: |
  = Tenant × (Dev + Staging + Prod) × (V1 + V2) × ({Platform} + {AltPlatform})
  
  Applying distributivity: a × (b + c) = (a × b) + (a × c)
  
  = (Tenant × Dev × V1 × {Platform}) +
    (Tenant × Dev × V1 × {AltPlatform}) +
    (Tenant × Dev × V2 × {Platform}) +
    (Tenant × Dev × V2 × {AltPlatform}) +
    (Tenant × Staging × V1 × {Platform}) +
    (Tenant × Staging × V1 × {AltPlatform}) +
    (Tenant × Staging × V2 × {Platform}) +
    (Tenant × Staging × V2 × {AltPlatform}) +
    (Tenant × Prod × V1 × {Platform}) +
    (Tenant × Prod × V1 × {AltPlatform}) +
    (Tenant × Prod × V2 × {Platform}) +
    (Tenant × Prod × V2 × {AltPlatform})

path_count: 12

paths:
  - path_id: 1
    configuration: [Tenant, Dev, V1, {Platform}]
    description: "Development environment, API v1, {Platform} integration"
  
  - path_id: 2
    configuration: [Tenant, Dev, V1, {AltPlatform}]
    description: "Development environment, API v1, {AltPlatform} integration"
  
  # ... (10 more paths)

complexity_analysis:
  total_paths: 12
  coproduct_branches: 2 × 3 × 2 = 12
  implementation_strategy: "Factor common tenant handling, specialize by platform"
```

## Execution Steps

### Step 1: Read Requirements

```bash
REQ_FILE="threads/engineering/{requirement}/1-input.md"
cat "$REQ_FILE" | python {baseDir}/scripts/parse_requirements.py
```

### Step 2: Extract Entities

Identify nouns representing types:
- "Multi-tenant" → `Tenant` (product type)
- "{Platform} OR {AltPlatform}" → `Platform` (coproduct)
- "V1 and V2 API" → `Version` (coproduct)
- "Dev, Staging, Prod" → `Environment` (coproduct)

### Step 3: Identify Algebraic Structures

**Products (×):** Things that MUST exist together
- "Multi-tenant {domain} service" → `Tenant × {Domain}Service`
- "User with address" → `User × Address`

**Coproducts (+):** Things that are choices (ONE of)
- "{Platform} OR {AltPlatform}" → `{Platform} + {AltPlatform}`
- "Payment via card OR bank transfer" → `Card + BankTransfer`

**Exponentials (→):** Functions
- "Given credentials, return products" → `Credentials → Products`

### Step 4: Construct Algebraic Expression

Combine into nested expression:
```
{Domain}Service = Tenant × Environment × Version × Platform
```

Where:
```
Platform = {Platform} + {AltPlatform} (2 choices)
Version = V1 + V2 (2 choices)
Environment = Dev + Staging + Prod (3 choices)
```

### Step 5: Apply Distributivity

Expand using: `a × (b + c) = (a × b) + (a × c)`

```python
# Run expansion script
python {baseDir}/scripts/expand_adt.py \
  --expression "Tenant × (Dev + Staging + Prod) × (V1 + V2) × ({Platform} + {AltPlatform})" \
  --output artifacts/engineering/specifications/v{VERSION}/requirements.adt
```

Script outputs canonical sum-of-products form:
```
(Tenant × Dev × V1 × {Platform}) + 
(Tenant × Dev × V1 × {AltPlatform}) + 
... (10 more terms)
```

### Step 6: Enumerate Paths

For each term in sum-of-products, create path entry:
```yaml
paths:
  - path_id: 1
    configuration: [Tenant, Dev, V1, {Platform}]
    type_signature: "Tenant → Environment → Version → Platform → Result"
    implementation_note: "{Platform} sync for dev env, v1 API"
```

### Step 7: Count Complexity

```python
path_count = product(len(variants) for each coproduct)
```

Example:
```
Environments: 3 (Dev, Staging, Prod)
Versions: 2 (V1, V2)
Platforms: 2 ({Platform}, {AltPlatform})

Total: 3 × 2 × 2 = 12 paths
```

### Step 8: Write Output

```bash
python {baseDir}/scripts/generate_adt_yaml.py \
  --paths $PATHS \
  --types $TYPES \
  --expression "$EXPRESSION" \
  --output artifacts/engineering/specifications/v{VERSION}/requirements.adt
```

## Parsing Rules

### Rule 1: Multi-Tenant Pattern
**Input:** "supports multiple tenants", "multi-tenant", "per-customer"
**Output:** Add `Tenant` or `TenantConfig` as first product term

### Rule 2: Platform Choices
**Input:** "{Platform} OR {AltPlatform}", "supports X and Y platforms"
**Output:** Coproduct: `Platform = {Platform} + {AltPlatform}`

### Rule 3: Feature Flags
**Input:** "optional feature X", "can enable/disable Y"
**Output:** Coproduct: `Feature = Enabled + Disabled`

### Rule 4: API Versions
**Input:** "v1 and v2 API", "versioned endpoints"
**Output:** Coproduct: `Version = V1 + V2`

### Rule 5: Environments
**Input:** "deploys to dev, staging, prod", "multiple environments"
**Output:** Coproduct: `Environment = Dev + Staging + Prod`

### Rule 6: Async Operations
**Input:** "background job", "async processing", "queue"
**Output:** Functor: `IO[Result]` (handled by functor-generator)

### Rule 7: Optional Fields
**Input:** "optional email", "may have address"
**Output:** Coproduct: `Maybe[Email] = Some Email + None`

### Rule 8: Collections
**Input:** "list of products", "multiple orders"
**Output:** Type constructor: `List[Product]`, `Set[Order]`

## Validation Checks

Before outputting ADT:

1. **No undefined types**: All referenced types have definitions
2. **Coproducts non-empty**: Each + has at least 2 variants
3. **Products non-trivial**: Each × has at least 2 components
4. **No circular dependencies**: Type graph is acyclic
5. **Void elimination**: No terms multiply by Void (× Void = Void)

## Error Cases

### Error 1: Ambiguous Requirements
```
Input: "Build a sync service"
Error: "Insufficient detail - what syncs? from where? to where?"
Action: Request clarification in ops/today.md
```

### Error 2: Contradictory Choices
```
Input: "Supports {Platform} only, and also {AltPlatform}"
Error: "Contradiction - 'only' conflicts with 'and also'"
Action: Flag for human review
```

### Error 3: Impossible Combinations
```
Expression: Tenant × Void
Error: "Void type detected - a × Void = Void (impossible path)"
Action: Remove Void paths, document why
```

## Examples

### Example 1: Simple Service
```
Input: "Build a service that fetches data from {Platform}"

Output:
expression: |
  {Platform}Sync = Credentials → Entities

type_definitions:
  Credentials:
    type: product
    fields: [endpoint_url, access_token]

  Entities:
    type: List[Entity]

path_count: 1
paths:
  - path_id: 1
    configuration: [Credentials, Entities]
    type_signature: "Credentials → Entities"
```

### Example 2: Multi-Tenant with Choice
```
Input: "Build a recommendation service that supports multiple merchants and syncs from {Platform} OR {AltPlatform}"

Output:
expression: |
  RecommendationService = Tenant × ({Platform} + {AltPlatform})

expanded_expression: |
  = (Tenant × {Platform}) + (Tenant × {AltPlatform})

path_count: 2
paths:
  - path_id: 1
    configuration: [Tenant, {Platform}]
  - path_id: 2
    configuration: [Tenant, {AltPlatform}]
```

### Example 3: Complex Multi-Variant
```
Input: "Build a {domain} service that supports multiple tenants, syncs from {Platform} OR {AltPlatform}, has V1 and V2 APIs, and deploys to Dev/Staging/Prod"

Output:
expression: |
  {Domain}Service = Tenant × Environment × Version × Platform

expanded_expression: |
  = (Tenant × Dev × V1 × {Platform}) +
    (Tenant × Dev × V1 × {AltPlatform}) +
    (Tenant × Dev × V2 × {Platform}) +
    (Tenant × Dev × V2 × {AltPlatform}) +
    (Tenant × Staging × V1 × {Platform}) +
    (Tenant × Staging × V1 × {AltPlatform}) +
    (Tenant × Staging × V2 × {Platform}) +
    (Tenant × Staging × V2 × {AltPlatform}) +
    (Tenant × Prod × V1 × {Platform}) +
    (Tenant × Prod × V1 × {AltPlatform}) +
    (Tenant × Prod × V2 × {Platform}) +
    (Tenant × Prod × V2 × {AltPlatform})

path_count: 12
```

## Success Criteria

ADT is complete when:

1. ✅ All types defined (no undefined references)
2. ✅ Expression expanded to sum-of-products form
3. ✅ All paths enumerated (count matches formula)
4. ✅ Type signatures specified for each path
5. ✅ Complexity analysis documented

## Next Steps

After ADT generation:
1. Pass to **algebraic-structure-validator** for law verification
2. Use paths in **functor-generator** for pattern detection
3. Reference in **curry-howard-prover** for type proofs