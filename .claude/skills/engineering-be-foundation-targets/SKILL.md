---
name: engineering-foundation-targets
description: Configure deployment targets and external resources. Invoked by engineering-setup agent. Creates or reviews targets.yaml.
---

# Foundation Targets

Configure deployment targets and external resource requirements for code generation.

## Purpose

Targets define implementation choices and external dependencies. Created once per `{name}`, reviewed/adjusted on subsequent iterations.

## Input

| Source | Location |
|--------|----------|
| PM Handoff | `artifacts/{product}/features/{feature-slug}/v{N}/handoff.md` |
| Existing Targets | `artifacts/engineering/{name}/targets.yaml` (if exists) |

## Output

| File | Schema |
|------|--------|
| `artifacts/engineering/{name}/targets.yaml` | [targets.schema.json](references/targets.schema.json) |

## Instructions

### 1. Check Existing Targets

```
IF exists(artifacts/engineering/{name}/targets.yaml):
  MODE = "review"
  LOAD existing targets
ELSE:
  MODE = "create"
```

### 2. Extract Requirements from Handoff

Read `handoff.md` and extract:
- Technology constraints mentioned
- External services referenced (Stripe, Twilio, AWS S3, etc.)
- SDK/API requirements
- Integration points

### 3. Determine Language

| Constraint | Language |
|------------|----------|
| Shopify app | typescript |
| FastAPI mentioned | python |
| Go requirement | go |
| Default | python |

### 4. Identify External Resources

For each external service in handoff:

```yaml
external:
  - id: stripe
    type: sdk
    package: stripe
    version: "^5.0.0"
    purpose: "Payment processing"
    
  - id: twilio
    type: api
    base_url: "https://api.twilio.com"
    auth: api_key
    purpose: "SMS notifications"
    
  - id: s3
    type: sdk
    package: boto3
    version: "^1.28.0"
    purpose: "File storage"
```

### 5. Configure Targets

Apply language-specific defaults:

**Python:**
```yaml
language:
  primary: python
  version: "3.11"
api:
  framework: fastapi
persistence:
  orm: sqlalchemy
```

**TypeScript:**
```yaml
language:
  primary: typescript
  version: "5.0"
api:
  framework: hono  # or remix for Shopify
persistence:
  orm: prisma
```

### 6. Review Mode (if existing)

When MODE = "review":

```
FOR each section in existing targets:
  IF handoff introduces new requirements:
    ADD to targets
  IF handoff conflicts with existing:
    PROMPT: "Conflict detected: {description}. Update? [y/n]"
  IF section unchanged:
    KEEP existing
```

### 7. Validate Against Schema

Validate output against [targets.schema.json](references/targets.schema.json):

| Field | Required | Validation |
|-------|----------|------------|
| `version` | yes | Pattern: `^\d+\.\d+$` |
| `name` | yes | Pattern: `^[a-z][a-z0-9-]*$` |
| `language.primary` | yes | Enum: python, typescript, go |
| `external[].id` | yes | Unique identifier |
| `external[].type` | yes | Enum: sdk, api, service |

### 8. Write Output

Write to `artifacts/engineering/{name}/targets.yaml`

## Output Format

Per [targets.schema.json](references/targets.schema.json):

```yaml
version: "1.0"
name: "{name}"
created_at: "{ISO8601}"
updated_at: "{ISO8601}"
source_handoff: "artifacts/{product}/features/{feature-slug}/v{N}/handoff.md"

language:
  primary: python
  version: "3.11"

api:
  enabled: true
  style: rest
  framework: fastapi

persistence:
  enabled: true
  type: sql
  provider: postgresql
  orm: sqlalchemy

events:
  enabled: false
  style: null
  broker: null

topology:
  style: monolith

external:
  - id: stripe
    type: sdk
    package: stripe
    version: "^5.0.0"
    purpose: "Payment processing"
    config:
      env_vars:
        - STRIPE_SECRET_KEY
        - STRIPE_WEBHOOK_SECRET
    
  - id: sendgrid
    type: api
    base_url: "https://api.sendgrid.com/v3"
    auth: bearer
    purpose: "Email delivery"
    config:
      env_vars:
        - SENDGRID_API_KEY

  - id: redis
    type: service
    purpose: "Caching and sessions"
    config:
      env_vars:
        - REDIS_URL

standardization:
  auth:
    enabled: true
    type: jwt
  logging:
    enabled: true
    format: json
    level: info
  validation:
    enabled: true
  error_handling:
    enabled: true
  tracing:
    enabled: false
  rate_limiting:
    enabled: false
```

## External Resource Types

| Type | Description | Required Fields |
|------|-------------|-----------------|
| `sdk` | Installable package | package, version |
| `api` | HTTP API integration | base_url, auth |
| `service` | Infrastructure service | purpose |

## Language-Specific Defaults

### Python
```yaml
api.framework: fastapi
persistence.orm: sqlalchemy
external[type=sdk].package: PyPI package name
```

### TypeScript
```yaml
api.framework: hono | express | remix
persistence.orm: prisma | drizzle
external[type=sdk].package: npm package name
```

## Errors

| Error | Cause | Resolution |
|-------|-------|------------|
| `missing_name` | Name not provided | Extract from handoff or prompt |
| `unknown_language` | Invalid language | Use: python, typescript, go |
| `invalid_external_type` | Bad resource type | Use: sdk, api, service |
| `missing_package` | SDK without package | Add package field |
| `missing_base_url` | API without URL | Add base_url field |
| `schema_violation` | Output fails validation | Fix per schema requirements |

## Do NOT

- Create targets without reading handoff
- Ignore existing targets in review mode
- Skip external resource extraction
- Output without schema validation