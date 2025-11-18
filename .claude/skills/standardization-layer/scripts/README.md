# Standardization Layer Scripts

Apply uniform cross-cutting concerns to microservices using category theory's natural transformations.

## Quick Start

1. **Install dependencies**:
```bash
pip install fastapi uvicorn pyjwt pydantic
```

2. **Review the example services**:
   - `merchant_app.py` - Example merchant service
   - `billing_app.py` - Example billing service

3. **Run the injector**:
```bash
python standard_injector.py
```

This will inject standardization middleware into both services.

4. **Run the services**:

Merchant service (JWT auth required):
```bash
JWT_SECRET="super-secret" uvicorn merchant_app:app --port 8001 --reload
```

Billing service (no auth):
```bash
uvicorn billing_app:app --port 8002 --reload
```

## Files

- **standard_spec.py**: Defines all specification dataclasses
  - `StandardizationSpec`: Main spec containing all cross-cutting concerns
  - `AuthSpec`: Authentication configuration (JWT/API Key/OAuth)
  - `ValidationSpec`: Request validation rules
  - `ResponseFormatSpec`: Standard response format
  - `ErrorHandlingSpec`: Error handling and retry logic
  - `ObservabilitySpec`: Logging, metrics, tracing
  - `RateLimitSpec`: Rate limiting configuration

- **standard_generator.py**: Generates middleware code from specs
  - `generate_standard_block()`: Converts spec to FastAPI middleware

- **standard_injector.py**: Injects code into services
  - `Service`: Data model for services
  - `F()`: Functor that transforms services
  - `verify_functor_laws()`: Verifies type preservation
  - `verify_composition_preserved()`: Verifies composition works
  - `load_service()`, `write_service()`: File I/O

- **merchant_app.py**: Example merchant service
- **billing_app.py**: Example billing service

## Usage Example

```python
from standard_spec import StandardizationSpec, AuthSpec, AuthMethod
from standard_injector import load_service, F, verify_functor_laws, write_service

# Define spec
spec = StandardizationSpec(
    auth=AuthSpec(method=AuthMethod.JWT, required=True),
    validation=ValidationSpec(enabled=True),
    response=ResponseFormatSpec(enabled=True),
    rate_limit=RateLimitSpec(enabled=True, requests_per_minute=60)
)

# Load service
service = load_service("my_app.py", "MyService", input_type="json", output_type="json")

# Transform
transformed = F(service, spec)

# Verify
assert verify_functor_laws(service, transformed)

# Write back
write_service(transformed)
```

## Testing

### Test Merchant Service (JWT)

Generate a JWT token:
```python
import jwt
token = jwt.encode({"user_id": "123", "username": "test"}, "super-secret", algorithm="HS256")
print(token)
```

Test the endpoint:
```bash
curl -H "Authorization: Bearer YOUR_TOKEN" http://localhost:8001/merchants/123
```

### Test Billing Service (No Auth)

```bash
curl -X POST http://localhost:8002/billing/invoice \
  -H "Content-Type: application/json" \
  -d '{"amount": 100}'
```

### Test Rate Limiting

```bash
# Send 25 requests quickly
for i in {1..25}; do
  curl -H "Authorization: Bearer YOUR_TOKEN" http://localhost:8001/merchants/123
done
```

After 20 requests/minute, you should see:
```json
{"status": 429, "error": "Rate limit exceeded"}
```

## Environment Variables

- `JWT_SECRET`: Secret for JWT verification (default: "change-me")
- `API_KEY_VALUE`: API key for API key auth (default: "change-me")
- `MAX_REQUEST_SIZE`: Maximum request body size in bytes (default: 10MB)
- `REQS_PER_MINUTE`: Rate limit per minute (default: 60)

## Category Theory Verification

The injector verifies:

1. **Functor Laws**:
   - F preserves types (input_type and output_type unchanged)
   - F preserves identity

2. **Composition**:
   - If service A composes with service B (A.output = B.input)
   - Then F(A) composes with F(B) after transformation

This ensures standardization doesn't break your service architecture.

## Customization

To apply different standardization to your services:

1. Create your own `StandardizationSpec` with desired settings
2. Load your service files using `load_service()`
3. Apply transformation with `F(service, spec)`
4. Verify with `verify_functor_laws()`
5. Write back with `write_service()`

The injection is **idempotent** - running multiple times won't duplicate middleware.

## Injection Markers

The code is injected between these markers:
```python
# <<< STANDARDIZATION:BEGIN >>>
# middleware code here
# <<< STANDARDIZATION:END >>>
```

If markers don't exist, they're added at the end of the file.
