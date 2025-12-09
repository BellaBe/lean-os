---
name: standardization-definer
version: 1.0.0
category: engineering
author: LeanOS
description: |
  Analyzes specifications to extract cross-cutting concerns and generates 
  standardization contract maps. Defines WHAT standards exist across the system.
tags: [category-theory, natural-transformations, standardization, contracts]
---

# Standardization Definer

## Purpose

Extract cross-cutting concerns from specifications and generate standardization contract maps that define system-wide standards. This skill answers: "What standards must all services follow?"

Standards are cross-cutting concerns that appear across multiple services:
- Authentication and authorization patterns
- Request/response formats
- Validation rules
- Rate limiting policies
- Error handling strategies
- Observability requirements

## Mathematical Foundation

### Natural Transformations as Standards

Each standard is a natural transformation α: F → G where:
- F is the identity functor (original service)
- G is the standardization functor (transformed service)
- α is the transformation that applies the standard

**Naturality condition ensures:** Standardizing then composing = Composing then standardizing

This means standards can be applied uniformly without breaking service composition.

### Derivability

All standards must be derivable from specifications:
- Auth requirements → Auth standard
- Validation constraints → Validation standard  
- Response patterns (OpenAPI) → Response format standard
- Observability needs (architecture) → Metrics/tracing standards

## Input

```
specifications/v{X}/
├── requirements.adt           # Business requirements
├── architecture.categorical   # System architecture
├── api.openapi.json          # API specifications
├── effects.yaml              # Effect system
└── types.curry-howard        # Type signatures
```

## Process

### 1. Analyze Specifications

**Extract patterns that appear across services:**

From `requirements.adt`:
- Authentication requirements (user auth, service-to-service, public endpoints)
- Performance constraints (latency, throughput, size limits)
- Security requirements (encryption, sanitization)

From `architecture.categorical`:
- Composition patterns needing observability
- Functor mappings requiring standard interfaces
- Error propagation strategies

From `api.openapi.json`:
- Response structure patterns
- Error format patterns
- Pagination patterns
- Common headers

From `effects.yaml`:
- Retry strategies for IO effects
- Circuit breaker patterns
- Fallback behaviors

### 2. Identify Cross-Cutting Concerns

**Determine which patterns are:**
- Consistent across multiple services
- Required by system properties
- Enforced by architectural decisions

**Common concerns:**
- Authentication/Authorization
- Request validation
- Response formatting
- Rate limiting
- Error handling
- Metrics collection
- Distributed tracing
- Logging format
- CORS policies
- Correlation ID propagation

### 3. Generate Contract Maps

**For each concern, generate a contract map specifying:**

- Contract name and purpose
- Type signature (morphism in category)
- Invariants that must hold
- Behavior specification
- Integration points in service code

**Contract maps are specifications, not implementations:**
- Define WHAT the contract is
- Define WHERE it applies
- Define WHEN it's enforced
- Do NOT define HOW it's implemented (that's for backend-prover or standardization-applier)

### 4. Generate Configuration

**Create standardization.yaml with:**
- Enabled standards
- Configuration parameters
- Application rules (which endpoints, which services)
- Natural transformation metadata

## Output

### Contract Maps

```
artifacts/engineering/maps/shared/
├── auth/
│   └── authentication.contract.yaml
├── validation/
│   └── request-validation.contract.yaml
├── responses/
│   └── standard-response.contract.yaml
├── rate-limiting/
│   └── token-bucket.contract.yaml
├── observability/
│   ├── metrics.contract.yaml
│   ├── tracing.contract.yaml
│   └── logging.contract.yaml
└── error-handling/
    ├── retry.contract.yaml
    └── circuit-breaker.contract.yaml
```

### Configuration

```
artifacts/engineering/specifications/v{X}/
└── standardization.yaml
```

## Contract Map Format

Each contract map follows this structure:

```yaml
contract:
  name: <StandardName>
  category: <auth|validation|response|observability|error-handling>
  version: <semantic-version>
  
  purpose: |
    <What this standard does and why it exists>
  
  mathematical_model:
    functor: <F → G transformation>
    naturality_condition: |
      <How naturality is verified>
  
  type_signature:
    input: <Input type>
    output: <Output type>
    effects: [<list of effects>]
  
  invariants:
    - <Property that must hold>
    - <Another invariant>
  
  behavior:
    description: |
      <What the standard does>
    
    steps:
      - <Step 1>
      - <Step 2>
  
  application_rules:
    applies_to: <all|specific endpoints|specific services>
    exclude: [<list of exclusions>]
    conditions: [<when to apply>]
  
  dependencies:
    contracts: [<other contracts this depends on>]
    shared_types: [<shared types needed>]
  
  verification:
    properties: [<properties to verify>]
    test_strategy: <how to test this>
```

## Standardization Configuration Format

```yaml
standardization:
  version: <semantic-version>
  generated_from: specifications/v{X}/
  
  standards:
    authentication:
      enabled: <bool>
      contract: maps/shared/auth/authentication.contract.yaml
      config:
        <contract-specific config>
    
    validation:
      enabled: <bool>
      contract: maps/shared/validation/request-validation.contract.yaml
      config:
        <contract-specific config>
    
    response_format:
      enabled: <bool>
      contract: maps/shared/responses/standard-response.contract.yaml
      config:
        <contract-specific config>
    
    # ... other standards
  
  natural_transformations:
    - name: <transformation name>
      source_category: <original category>
      target_category: <standardized category>
      preserves: [<composition|identity|associativity>]
```

## Verification

Generate proof that all standards are derivable:

```
artifacts/engineering/proofs/standardization/definition/
├── derivability.proof          # Each standard derived from specs
├── completeness.proof          # All concerns covered
├── consistency.proof           # No conflicting standards
└── minimality.proof            # No redundant standards
```

**Derivability proof structure:**
```json
{
  "standard": "authentication",
  "derived_from": [
    {
      "specification": "requirements.adt",
      "clause": "User authentication required for protected endpoints",
      "implies": "JWT authentication standard"
    }
  ],
  "verification": "valid"
}
```

## Examples

### Example: Authentication Contract

```yaml
contract:
  name: JWTAuthentication
  category: auth
  version: 1.0.0
  
  purpose: |
    Verify user identity using JWT tokens for protected endpoints.
    Ensures only authenticated users can access sensitive operations.
  
  mathematical_model:
    functor: Identity → Authenticated
    naturality_condition: |
      For any service morphism f: A → B,
      Authenticated(f) ∘ auth_A = auth_B ∘ Identity(f)
  
  type_signature:
    input: Request
    output: Either[Unauthorized, AuthenticatedRequest]
    effects: [IO]
  
  invariants:
    - "Valid token → User context attached"
    - "Invalid token → 401 Unauthorized"
    - "Public endpoints → Skip authentication"
  
  behavior:
    description: |
      Extract JWT from Authorization header, validate signature and expiry,
      attach user context to request if valid, reject if invalid.
    
    steps:
      - Extract token from Authorization header
      - Validate token signature using secret
      - Check token expiry
      - Extract user claims from token
      - Attach user context to request state
  
  application_rules:
    applies_to: all
    exclude: [/health, /metrics]
    conditions:
      - "endpoint not in exclude list"
  
  dependencies:
    contracts: []
    shared_types: [User, AuthContext]
  
  verification:
    properties:
      - "Naturality: auth preserves composition"
      - "Type safety: AuthenticatedRequest has User context"
      - "Security: Invalid tokens rejected"
    test_strategy: property-based (10K examples)
```

### Example: Standard Response Contract

```yaml
contract:
  name: StandardResponse
  category: response
  version: 1.0.0
  
  purpose: |
    Uniform response format across all API endpoints for consistent
    client experience and error handling.
  
  mathematical_model:
    functor: ServiceResponse → StandardizedResponse
    naturality_condition: |
      Wrapping domain responses in standard format preserves composition
  
  type_signature:
    input: T | Error
    output: StandardResponse[T]
    effects: []
  
  invariants:
    - "success XOR error (exactly one is set)"
    - "success=true → data != None"
    - "success=false → error != None"
    - "meta always present"
  
  behavior:
    description: |
      Wrap service response (success or error) in standard envelope
      with metadata (correlation_id, request_id, timestamp).
    
    steps:
      - Determine if response is success or error
      - Extract data or error details
      - Generate metadata (correlation_id, timestamp, etc)
      - Construct StandardResponse envelope
  
  application_rules:
    applies_to: all
    exclude: []
    conditions: []
  
  dependencies:
    contracts: []
    shared_types: [ErrorDetail, ResponseMeta]
  
  verification:
    properties:
      - "Naturality: wrapping preserves composition"
      - "Type safety: Generic type T preserved"
      - "Completeness: All responses wrapped"
    test_strategy: structural (schema validation)
```

## Key Properties

1. **Derivability:** All standards trace back to specifications
2. **Completeness:** All cross-cutting concerns identified
3. **Consistency:** No conflicting standards
4. **Minimality:** No redundant standards
5. **Naturality:** Standards are natural transformations
6. **Composability:** Standards compose without interference

## Integration

**Consumed by:**
- `backend-prover/code-map-generator` - References contracts when generating service maps
- `standardization-applier` - Implements contracts and injects into code

**Dependencies:**
- `system-architect` - Provides specifications to analyze

## Success Criteria

- [ ] All cross-cutting concerns extracted from specifications
- [ ] Each concern has a contract map
- [ ] All contracts have proper type signatures
- [ ] Naturality conditions specified
- [ ] Configuration file generated
- [ ] Derivability proofs complete
- [ ] No conflicting or redundant standards