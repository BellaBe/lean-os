---
name: standardization-applier
version: 1.0.0
category: engineering
author: LeanOS
description: |
  Applies standardization contracts to generated backend code using natural 
  transformations. Verifies that standards preserve categorical composition laws.
  This is the HOW - how to inject standards while maintaining mathematical correctness.
tags: [category-theory, natural-transformations, middleware, verification]
---

# Standardization Applier

## Purpose

Apply standardization contracts to generated backend code while preserving categorical composition. Uses natural transformations to ensure standards don't break service composition.

This skill answers: "How do we inject standards without breaking the system?"

## Mathematical Foundation

### Natural Transformation α: F → G

```
F: ServiceCategory → ServiceCategory (identity functor - original services)
G: ServiceCategory → StandardizedServiceCategory (standardization functor)
α: F → G (natural transformation - middleware injection)

Naturality condition:
  For all morphisms f: A → B,
  G(f) ∘ α_A = α_B ∘ F(f)
```

**In plain terms:** Standardizing then composing = Composing then standardizing

**Why this matters:** If naturality holds, we can apply standards to any service without worrying about breaking composition with other services.

### Verification Strategy

Prove naturality through:
1. **Type preservation:** Input/output types unchanged
2. **Composition preservation:** f ∘ g still works after standardization
3. **Property testing:** 10K random inputs verify laws hold

## Input

```
code/backend/                          # Pure business logic (from backend-prover)
├── services/
│   └── catalog_service.py            # Returns domain objects
├── api/v1/
│   └── catalog.py                    # Raw endpoints
└── main.py                           # No middleware

artifacts/engineering/maps/backend/    # Composition maps
├── services/*.map.yaml
└── composition.map.yaml

artifacts/engineering/maps/shared/     # Contract specifications
├── auth/*.contract.yaml
├── validation/*.contract.yaml
└── responses/*.contract.yaml

artifacts/engineering/specifications/v{X}/
└── standardization.yaml               # Configuration
```

## Process

### 1. Parse Configuration

Read `standardization.yaml` to determine:
- Which standards are enabled
- Configuration parameters per standard
- Application rules (where standards apply)
- Exclusion lists

### 2. Identify Injection Points

Analyze generated code structure:

**Service layer injection points:**
- Method entry (auth checks, validation)
- Method exit (response formatting, metrics)
- Around method (timing, tracing)

**API layer injection points:**
- Middleware stack (auth, rate limiting, CORS)
- Request handlers (validation, correlation ID)
- Response handlers (formatting, error mapping)

**Application layer injection points:**
- Startup hooks (metrics initialization)
- Lifecycle management (tracing setup)

### 3. Generate Middleware Implementations

For each enabled standard:

**Read contract map** (from `maps/shared/`)
- Understand type signature
- Understand behavior specification
- Understand invariants

**Generate implementation** that satisfies contract:
- Respects type signature
- Implements specified behavior
- Maintains invariants
- Preserves effects (IO, errors)

**Implementation must be:**
- Idempotent (safe to apply multiple times)
- Composable (works with other middleware)
- Natural (preserves composition laws)

### 4. Inject Standards

Apply standards to code using injection markers:

**Marker format:**
```python
# <<< STANDARDIZATION:<STANDARD_NAME>:<LOCATION> >>>
```

**Injection strategy:**
- Insert markers at identified injection points
- Generate middleware code from contracts
- Replace markers with generated code
- Preserve idempotence (check if already applied)

**Idempotence:** If markers already contain code, verify it matches current contracts and replace if needed.

### 5. Verify Natural Transformation

**Property 1: Type Preservation**

For each standardized service method:
```
service_before: A → IO[Either[Error, B]]
service_after:  A → IO[Either[Error, B]]

Verify: input type A unchanged, output type B unchanged
```

**Property 2: Composition Preservation**

For each composition in `maps/backend/composition.map.yaml`:
```
Original: h = g ∘ f
Standardized: h' = g' ∘ f'

Verify: h' composes correctly (types align, effects preserved)
```

**Property 3: Naturality Square Commutes**

```
    F(A) ----F(f)----> F(B)
     |                  |
   α_A                α_B
     |                  |
     v                  v
    G(A) ----G(f)----> G(B)

Verify: G(f) ∘ α_A = α_B ∘ F(f)
```

Where:
- F(A) = original service A
- G(A) = standardized service A
- F(f) = original morphism f
- G(f) = standardized morphism f
- α = natural transformation (middleware)

### 6. Generate Property-Based Tests

For each standard applied:

**Test naturality:**
```python
@given(input_data=from_specification_type)
async def test_naturality_holds(input_data):
    """
    Property: Standardization preserves composition
    
    For composition h = g ∘ f:
    standardize(g ∘ f) ≡ standardize(g) ∘ standardize(f)
    """
    # Compose then standardize
    result_1 = standardize(compose(g, f, input_data))
    
    # Standardize then compose
    result_2 = compose(standardize(g), standardize(f), input_data)
    
    # Results equivalent (modulo metadata like timestamps)
    assert equivalent(result_1.data, result_2.data)
```

**Test type preservation:**
```python
def test_types_preserved():
    """Verify input/output types unchanged after standardization"""
    original_sig = get_signature(service.method)
    standardized_sig = get_signature(standardized_service.method)
    
    assert original_sig.input_type == standardized_sig.input_type
    assert original_sig.output_type == standardized_sig.output_type
```

**Test invariants:**
```python
@given(response=from_response_type)
def test_response_invariants(response):
    """Verify StandardResponse invariants hold"""
    if response.success:
        assert response.data is not None
        assert response.error is None
    else:
        assert response.data is None
        assert response.error is not None
    
    assert response.meta is not None
```

### 7. Generate Proofs

**Naturality certificate:**
```json
{
  "standard": "authentication",
  "applied_to": ["catalog_service", "billing_service"],
  "naturality_verified": true,
  "tests_run": 10000,
  "tests_passed": 10000,
  "composition_preserved": true,
  "type_preservation": true,
  "square_commutes": true
}
```

**Composition preservation proof:**
- For each service composition
- Verify types still align
- Verify effects still compatible
- Verify laws still hold

## Output

### Modified Code

```
code/backend/
├── main.py                           # With middleware stack
├── services/
│   └── catalog_service.py           # With standard injections
└── api/v1/
    └── catalog.py                   # With middleware decorators
```

**Injection markers in code:**
```python
# <<< STANDARDIZATION:AUTH_MIDDLEWARE:BEGIN >>>
# ... generated auth middleware code ...
# <<< STANDARDIZATION:AUTH_MIDDLEWARE:END >>>
```

### Generated Middleware

```
code/backend/middleware/               # Generated implementations
├── auth.py                           # From maps/shared/auth/
├── validation.py                     # From maps/shared/validation/
├── response_formatting.py            # From maps/shared/responses/
└── observability.py                  # From maps/shared/observability/
```

### Proofs

```
artifacts/engineering/proofs/backend/standardization/
├── naturality-certificate.proof      # Main certificate
├── type-preservation.proof           # Types unchanged
├── composition-preservation.proof    # Composition works
└── property-tests/
    ├── auth-naturality.proof
    ├── validation-naturality.proof
    └── response-naturality.proof
```

## Naturality Certificate Format

```json
{
  "version": "1.0",
  "generated_at": "<timestamp>",
  "specification_version": "v1",
  
  "standards_applied": [
    {
      "name": "authentication",
      "contract": "maps/shared/auth/authentication.contract.yaml",
      "applied_to": ["all endpoints except [/health, /metrics]"],
      "naturality_verified": true,
      "tests_run": 10000,
      "tests_passed": 10000
    },
    {
      "name": "validation",
      "contract": "maps/shared/validation/request-validation.contract.yaml",
      "applied_to": ["all endpoints"],
      "naturality_verified": true,
      "tests_run": 10000,
      "tests_passed": 10000
    }
  ],
  
  "composition_preservation": {
    "verified": true,
    "compositions_tested": 15,
    "all_preserved": true
  },
  
  "type_preservation": {
    "verified": true,
    "services_tested": 5,
    "all_types_preserved": true
  },
  
  "naturality_squares": {
    "verified": true,
    "squares_tested": 25,
    "all_commute": true
  },
  
  "ready_for_deployment": true
}
```

## Verification Strategy

### Type Preservation

For each service method:
```
Extract type signature before standardization
Extract type signature after standardization
Assert signatures identical (modulo effects)
```

### Composition Preservation

For each composition in composition maps:
```
Identify services in composition: [f, g, h]
Apply standardization to each: [f', g', h']
Verify f' output type = g' input type
Verify g' output type = h' input type
Generate property test for composition
```

### Naturality Verification

For each standard:
```
Select random morphisms from composition maps
For each morphism f: A → B:
  1. Standardize A, apply f, get result_1
  2. Apply f to A, standardize result, get result_2
  3. Assert result_1 ≡ result_2 (modulo metadata)
Repeat 10,000 times with different inputs
```

## Examples

### Example: Auth Middleware Injection

**Before (pure business logic):**
```python
class CatalogService:
    async def create_catalog(self, data: CatalogCreateIn, ctx: RequestContext):
        async with self.session_factory() as session:
            repo = CatalogRepository(session)
            entity = await repo.create(data)
            await session.commit()
            return CatalogOut.model_validate(entity)
```

**After (with auth injection):**
```python
class CatalogService:
    async def create_catalog(self, data: CatalogCreateIn, ctx: RequestContext):
        # <<< STANDARDIZATION:AUTH_CHECK:BEGIN >>>
        if not ctx.user:
            raise Unauthorized("Authentication required")
        # <<< STANDARDIZATION:AUTH_CHECK:END >>>
        
        async with self.session_factory() as session:
            repo = CatalogRepository(session)
            entity = await repo.create(data)
            await session.commit()
            return CatalogOut.model_validate(entity)
```

**Naturality verified:**
- Input type: (CatalogCreateIn, RequestContext)
- Output type: IO[Either[Error, CatalogOut]]
- Types preserved ✓
- Composition with other services preserved ✓

### Example: Response Formatting

**Before:**
```python
@router.post("")
async def create_catalog_endpoint(
    data: CatalogCreateIn,
    service: CatalogServiceDep,
    ctx: RequestContextDep
):
    result = await service.create_catalog(data, ctx)
    return result  # Returns CatalogOut
```

**After:**
```python
@router.post("")
async def create_catalog_endpoint(
    data: CatalogCreateIn,
    service: CatalogServiceDep,
    ctx: RequestContextDep
):
    result = await service.create_catalog(data, ctx)
    
    # <<< STANDARDIZATION:RESPONSE_FORMAT:BEGIN >>>
    return StandardResponse(
        success=True,
        data=result,
        error=None,
        meta=ResponseMeta(
            correlation_id=ctx.correlation_id,
            request_id=ctx.request_id,
            timestamp=datetime.utcnow()
        )
    )
    # <<< STANDARDIZATION:RESPONSE_FORMAT:END >>>
```

**Naturality verified:**
- Domain result (CatalogOut) wrapped in standard envelope
- Composition with downstream consumers preserved ✓
- Standard format applied uniformly across all endpoints ✓

## Key Properties

1. **Naturality:** Standards are natural transformations
2. **Preservation:** Composition and types preserved
3. **Idempotence:** Safe to apply multiple times
4. **Composability:** Multiple standards work together
5. **Verifiability:** Mathematical proofs generated
6. **Traceability:** Injection markers track what was applied

## Integration

**Consumes:**
- `backend-prover/code-implementation-generator` - Generates pure code to standardize
- `standardization-definer` - Provides contract maps and configuration

**Produces for:**
- `proof-composer` - Provides naturality proofs for final certificate

## Success Criteria

- [ ] All enabled standards applied to code
- [ ] Injection markers present in code
- [ ] Middleware implementations generated from contracts
- [ ] Type preservation verified for all services
- [ ] Composition preservation verified for all compositions
- [ ] Naturality verified via property tests (10K examples)
- [ ] Naturality certificate generated
- [ ] No type mismatches introduced
- [ ] No composition breaks introduced
- [ ] Ready for integration testing