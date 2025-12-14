---
name: foundation-targets
description: |
  Target configuration for code generation. Defines deployment choices:
  API style, persistence, events, topology, language, standardization.
  Use when: starting new system, changing deployment targets, understanding
  generation options. These are CHOICES, not categorical structure.
---

# Foundation Targets

Configure deployment targets. Targets are implementation choices that don't affect categorical structure.

## Principle

```
Categorical Structure (FIXED)     Deployment Targets (CONFIGURABLE)
├── Objects                       ├── API style (REST, GraphQL, none)
├── Morphisms                     ├── Persistence (SQL, NoSQL, none)
├── Composition                   ├── Events (sync, async, none)
├── Effects                       ├── Topology (monolith, microservices)
└── Laws                          ├── Language (Python, TypeScript)
                                  └── Standardization (auth, logging)
```

The same categorical specification can generate different systems based on targets.

## Input

- User requirements specifying deployment preferences
- Existing targets.yaml to modify
- Defaults if nothing specified

## Output

`artifacts/v{N}/targets.yaml`

## Schema

```yaml
version: string

targets:
  api:
    enabled: boolean               # Whether to generate API layer
    style: rest | graphql | grpc | none
    framework: string | null       # Language-specific: fastapi, express, etc.
    prefix: string                 # API path prefix, e.g., "/api/v1"
    
  persistence:
    enabled: boolean               # Whether to generate persistence layer
    type: sql | nosql | memory | none
    provider: string | null        # postgresql, mongodb, sqlite, redis, etc.
    migrations: boolean            # Generate migration files
    
  events:
    enabled: boolean               # Whether to use event-driven patterns
    style: sync | async            # Synchronous calls or async events
    broker: string | null          # nats, kafka, rabbitmq, or null for sync
    
  topology:
    style: monolith | microservices | serverless | library
    # monolith: single deployable unit
    # microservices: multiple services
    # serverless: function-based
    # library: no entry point, just importable code
    
  language:
    primary: python | typescript | go
    version: string                # e.g., "3.11", "5.0", "1.21"
    
  standardization:
    auth:
      enabled: boolean
      type: jwt | session | apikey | oauth | none
      
    logging:
      enabled: boolean
      format: json | text
      level: debug | info | warn | error
      
    tracing:
      enabled: boolean
      provider: string | null      # opentelemetry, jaeger, zipkin
      
    metrics:
      enabled: boolean
      provider: string | null      # prometheus, statsd
      
    resilience:
      retry:
        enabled: boolean
        max_attempts: integer
        backoff: constant | exponential | fibonacci
        
      circuit_breaker:
        enabled: boolean
        threshold: integer         # Failure count to open
        timeout_ms: integer        # Time before half-open
        
      timeout:
        enabled: boolean
        default_ms: integer
        
    validation:
      enabled: boolean
      style: pydantic | zod | manual
```

## Defaults

```yaml
version: "1.0"

targets:
  api:
    enabled: true
    style: rest
    framework: fastapi
    prefix: "/api/v1"
    
  persistence:
    enabled: true
    type: sql
    provider: postgresql
    migrations: true
    
  events:
    enabled: false
    style: sync
    broker: null
    
  topology:
    style: monolith
    
  language:
    primary: python
    version: "3.11"
    
  standardization:
    auth:
      enabled: true
      type: jwt
      
    logging:
      enabled: true
      format: json
      level: info
      
    tracing:
      enabled: false
      provider: null
      
    metrics:
      enabled: false
      provider: null
      
    resilience:
      retry:
        enabled: true
        max_attempts: 3
        backoff: exponential
        
      circuit_breaker:
        enabled: false
        threshold: 5
        timeout_ms: 30000
        
      timeout:
        enabled: true
        default_ms: 5000
        
    validation:
      enabled: true
      style: pydantic
```

## Target Presets

### Minimal (Library)

```yaml
targets:
  api:
    enabled: false
  persistence:
    enabled: false
  events:
    enabled: false
  topology:
    style: library
  standardization:
    auth:
      enabled: false
    logging:
      enabled: false
    tracing:
      enabled: false
    resilience:
      retry:
        enabled: false
      circuit_breaker:
        enabled: false
      timeout:
        enabled: false
```

### Production Monolith

```yaml
targets:
  api:
    enabled: true
    style: rest
    framework: fastapi
  persistence:
    enabled: true
    type: sql
    provider: postgresql
  events:
    enabled: false
  topology:
    style: monolith
  standardization:
    auth:
      enabled: true
      type: jwt
    logging:
      enabled: true
      format: json
    tracing:
      enabled: true
      provider: opentelemetry
    metrics:
      enabled: true
      provider: prometheus
    resilience:
      retry:
        enabled: true
      circuit_breaker:
        enabled: true
      timeout:
        enabled: true
```

### Event-Driven Microservices

```yaml
targets:
  api:
    enabled: true
    style: grpc
  persistence:
    enabled: true
    type: sql
    provider: postgresql
  events:
    enabled: true
    style: async
    broker: nats
  topology:
    style: microservices
  standardization:
    auth:
      enabled: true
      type: jwt
    logging:
      enabled: true
    tracing:
      enabled: true
      provider: opentelemetry
    resilience:
      retry:
        enabled: true
      circuit_breaker:
        enabled: true
      timeout:
        enabled: true
```

### Serverless

```yaml
targets:
  api:
    enabled: true
    style: rest
    framework: aws_lambda
  persistence:
    enabled: true
    type: nosql
    provider: dynamodb
  events:
    enabled: true
    style: async
    broker: sqs
  topology:
    style: serverless
```

## Impact on Pipeline

| Target | Affects |
|--------|---------|
| `api.enabled` | build-functors creates F_api, gen-morphisms creates handlers |
| `api.style` | gen-morphisms generates REST routes vs GraphQL resolvers |
| `persistence.enabled` | build-functors creates F_persist, gen-morphisms includes repo |
| `persistence.type` | gen-types generates appropriate model decorators |
| `events.enabled` | build-functors creates F_events, gen-morphisms emits events |
| `events.style` | sync = direct calls, async = message publishing |
| `topology.style` | gen-wiring creates single vs multiple entry points |
| `language.primary` | All gen-* skills output in this language |
| `standardization.*` | build-transformations creates nat trans, gen-wiring applies |

## Validation Rules

```yaml
validation:
  errors:
    - condition: "persistence.enabled && !persistence.provider"
      message: "persistence.provider required when persistence.enabled"
      
    - condition: "events.style == 'async' && !events.broker"
      message: "events.broker required for async events"
      
    - condition: "topology.style == 'microservices' && !events.enabled"
      message: "microservices typically require events.enabled"
      level: warning
      
    - condition: "api.enabled && !api.framework"
      message: "api.framework recommended when api.enabled"
      level: warning
      
  warnings:
    - condition: "standardization.tracing.enabled && !standardization.logging.enabled"
      message: "tracing without logging may miss context"
      
    - condition: "topology.style == 'serverless' && persistence.type == 'sql'"
      message: "SQL with serverless may have cold start issues"
```

## Language-Specific Frameworks

### Python
```yaml
api:
  rest: [fastapi, flask, django]
  graphql: [strawberry, graphene, ariadne]
  grpc: [grpcio]
  
persistence:
  sql: [sqlalchemy, tortoise-orm, sqlmodel]
  nosql: [motor, beanie]
  
validation: [pydantic, attrs, marshmallow]
```

### TypeScript
```yaml
api:
  rest: [express, fastify, nestjs, hono]
  graphql: [apollo, type-graphql, pothos]
  grpc: [grpc-js]
  
persistence:
  sql: [prisma, typeorm, drizzle]
  nosql: [mongoose]
  
validation: [zod, yup, io-ts]
```

### Go
```yaml
api:
  rest: [gin, echo, fiber, chi]
  graphql: [gqlgen]
  grpc: [grpc-go]
  
persistence:
  sql: [gorm, sqlx, ent]
  nosql: [mongo-driver]
```

## Process

1. **Read existing targets.yaml** if present
2. **Parse user requirements** for deployment preferences
3. **Apply defaults** for unspecified values
4. **Validate** configuration
5. **Write targets.yaml**

## Example Interaction

```
User: Build a REST API with PostgreSQL, add JWT auth

Process:
  1. Start with defaults
  2. Confirm: api.style = rest ✓
  3. Confirm: persistence.provider = postgresql ✓
  4. Confirm: auth.type = jwt ✓
  5. Write targets.yaml
  
Output: artifacts/v1/targets.yaml with above configuration
```

```
User: Make it event-driven with NATS

Process:
  1. Load existing targets.yaml
  2. Set: events.enabled = true
  3. Set: events.style = async
  4. Set: events.broker = nats
  5. Validate: OK
  6. Write updated targets.yaml
  
Output: Updated targets.yaml, re-run build-functors onwards
```

## Do NOT

- Change categorical structure based on targets
- Generate different morphisms for different targets
- Skip verification based on targets
- Assume targets affect what the system DOES (only HOW)
