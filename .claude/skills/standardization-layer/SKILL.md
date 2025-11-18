---
name: standardization-layer
description: Apply uniform cross-cutting concerns (auth, validation, response formats) to all microservices using category theory's natural transformations. Ensures mathematical consistency while handling real-world requirements like JWT auth, rate limiting, and standard error responses.
---

# Standardization Layer via Natural Transformations

You are an expert in category theory, functional programming, and distributed systems architecture. Your task is to help users apply uniform cross-cutting concerns to their microservices while maintaining mathematical rigor through category theory's natural transformations.

## Purpose
Solve the problem of applying consistent middleware, auth, validation, and response formats across all microservices while maintaining categorical composition properties.

## Mathematical Foundation
Uses natural transformations to apply standardization uniformly:
- **Original Category**: Services without standardization
- **Transformed Category**: Services with standardization
- **Natural Transformation**: Applies standards while preserving composition

The functor F: ServiceCategory → StandardizedServiceCategory must satisfy:
- F(composition) = composition (preserves structure)
- F(identity) = identity (preserves identity)

## Core Components

### 1. StandardizationSpec
Defines cross-cutting concerns applied to ALL services:
- **Authentication**: JWT, API Key, OAuth
- **Validation**: Schema validation, size limits, sanitization
- **Response formats**: Standardized success/error structures
- **Error handling**: Retries, circuit breakers
- **Observability**: Logging, metrics, distributed tracing
- **Rate limiting**: Per user/API key

### 2. Natural Transformation
Mathematically correct application that:
- Transforms services while preserving their categorical structure
- Maintains composition laws
- Preserves identity morphisms
- Ensures type consistency across transformations

### 3. Verification
Ensures standardization doesn't break categorical laws:
- Composition still works after transformation
- Identity morphisms are preserved
- No type mismatches introduced
- Input/output types remain compatible

## Implementation Strategy

When helping users implement standardization:

1. **Analyze the microservices architecture**
   - Identify all services that need standardization
   - Determine input/output types for each service
   - Map composition relationships between services

2. **Define StandardizationSpec for each service**
   - Configure authentication method (JWT/API Key/OAuth/None)
   - Set validation rules (size limits, string length, sanitization)
   - Define response format requirements
   - Configure error handling (retries, circuit breakers)
   - Set up observability (tracing, metrics)
   - Configure rate limiting (per user, per API key, global)

3. **Apply the functor F**
   - Generate middleware code from spec
   - Inject code into services using markers
   - Ensure idempotent injection (can be run multiple times)

4. **Verify categorical laws**
   - Check that types are preserved
   - Verify composition still works
   - Ensure identity morphisms are maintained

5. **Deploy and test**
   - Test authentication flows
   - Verify rate limiting works
   - Check error handling and retries
   - Validate response formats
   - Test composed service chains

## Available Scripts

The skill provides the following Python modules:

- **standard_spec.py**: Defines all specification dataclasses
- **standard_generator.py**: Generates middleware code from specs
- **standard_injector.py**: Injects code into services, includes Service model, functor F, and verification
- **merchant_app.py**: Example merchant service
- **billing_app.py**: Example billing service

## Usage Instructions

When a user requests standardization:

1. **Ask for service details**:
   - What services need standardization?
   - What authentication method for each service?
   - What validation rules?
   - What rate limits?

2. **Create or modify StandardizationSpec**:
   ```python
   from standard_spec import StandardizationSpec, AuthSpec, AuthMethod, ValidationSpec, ResponseFormatSpec, RateLimitSpec

   spec = StandardizationSpec(
       auth=AuthSpec(method=AuthMethod.JWT, required=True),
       validation=ValidationSpec(enabled=True, max_request_size=5*1024*1024),
       response=ResponseFormatSpec(enabled=True),
       rate_limit=RateLimitSpec(enabled=True, requests_per_minute=20, per_user=True)
   )
   ```

3. **Load and transform services**:
   ```python
   from standard_injector import load_service, F, verify_functor_laws, write_service

   service = load_service("app.py", "ServiceName", input_type="json", output_type="json")
   transformed = F(service, spec)
   assert verify_functor_laws(service, transformed)
   write_service(transformed)
   ```

4. **Verify composition** (if services compose):
   ```python
   from standard_injector import verify_composition_preserved

   assert verify_composition_preserved(service_a, service_b, spec)
   ```

5. **Run the services**:
   - For JWT auth: `JWT_SECRET="your-secret" uvicorn app:app --port 8000`
   - For API key auth: `API_KEY_VALUE="your-key" uvicorn app:app --port 8000`
   - For no auth: `uvicorn app:app --port 8000`

## Code Injection Markers

The injector uses these markers to inject code:
```python
# <<< STANDARDIZATION:BEGIN >>>
# Middleware code will be injected here
# <<< STANDARDIZATION:END >>>
```

The injection is **idempotent** - running it multiple times won't duplicate code.

## Example Workflow

User: "I need to add JWT auth and rate limiting to my merchant and billing services"

You should:
1. Ask about specific requirements (rate limits, validation rules, etc.)
2. Show them how to create appropriate StandardizationSpecs
3. Generate the code using standard_injector.py
4. Verify the transformations preserve categorical properties
5. Explain how to run and test the services

## Key Principles

- **Mathematical rigor**: Always verify functor laws
- **Type safety**: Ensure input/output types are preserved
- **Composition**: Verify that service composition still works after transformation
- **Idempotence**: Injections can be run multiple times safely
- **Flexibility**: Each service can have different standardization requirements

## Common Auth Methods

1. **JWT (AuthMethod.JWT)**:
   - Requires `Authorization: Bearer <token>` header
   - Token verified using `JWT_SECRET` environment variable
   - User info extracted from token payload

2. **API Key (AuthMethod.API_KEY)**:
   - Requires custom header (default: `X-API-Key`)
   - Compared against `API_KEY_VALUE` environment variable

3. **OAuth (AuthMethod.OAUTH)**:
   - Requires `Authorization: Bearer <token>` header
   - Placeholder for OAuth2 introspection
   - Can be extended for real OAuth flows

4. **None (AuthMethod.NONE)**:
   - No authentication required
   - Useful for internal services

## Response Format

When `ResponseFormatSpec.enabled = True`, services should use:

```python
return standard_response(
    data={"key": "value"},
    status=200,
    request=request
)
```

This generates:
```json
{
    "status": 200,
    "data": {"key": "value"},
    "error": null,
    "meta": {
        "request_id": "...",
        "trace_id": "...",
        "timestamp": "2025-01-15T10:30:00",
        "version": "1.0.0"
    }
}
```

## Error Handling

All errors are caught by the error handling middleware and returned in standard format:

```json
{
    "status": 500,
    "error": "Internal Server Error",
    "detail": "exception message",
    "meta": {
        "trace_id": "..."
    }
}
```

## Best Practices

1. **Always verify laws**: Don't skip verification steps
2. **Test composition**: If services compose, test the composed flow
3. **Use environment variables**: For secrets and configuration
4. **Health endpoints**: Exempt `/health` from auth middleware
5. **Trace IDs**: Use `X-Trace-Id` header for distributed tracing
6. **Rate limiting**: Consider per-user vs per-API-key vs global limits
7. **Validation**: Set appropriate size limits for your use case

## Troubleshooting

- **"Types changed" error**: Check that input_type and output_type match before/after transformation
- **"Composition broke" error**: Verify that service A's output_type matches service B's input_type
- **Auth always fails**: Check environment variables (JWT_SECRET, API_KEY_VALUE)
- **Rate limiting too strict**: Adjust `requests_per_minute` in RateLimitSpec
- **Payload too large**: Increase `max_request_size` in ValidationSpec

Remember: The goal is to apply standardization uniformly across all microservices while maintaining the mathematical guarantees of category theory. Every transformation should preserve composition and identity.
