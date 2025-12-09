---
name: bootstrap-generator
description: |
  Generate application bootstrap components: entry point, configuration, database
  setup, and project files. Language-agnostic specification of what makes a
  generated codebase runnable. References language-specific templates for
  implementation details.
  Input: All generated code, standards/configuration/*.std.yaml
  Output: Entry point, config, database setup, project manifest, scripts
---

# Bootstrap Generator

Generate application entry point and infrastructure wiring.

## Purpose

Create the bootstrap layer that makes generated code runnable:
1. Project manifest (dependencies, entry points, metadata)
2. Application entry point (CLI, server startup)
3. Configuration loading (environment, secrets, defaults)
4. Database lifecycle (connection pool, session factory, migrations)
5. Dependency injection container
6. Startup/shutdown hooks
7. Development scripts

## Input

- All generated code from other skills
- `standards/configuration/config.std.yaml` - Configuration structure
- `standards/categories/storage.std.yaml` - Database configuration
- `maps/modules/services.map.yaml` - Service dependencies
- Target language from `code-architect` configuration

## Output Structure

```
generated/{language}/
├── {manifest}              # pyproject.toml / package.json / go.mod
├── src/{project}/
│   ├── {entry_point}       # __main__.py / index.ts / main.go
│   ├── {config_module}     # config.py / config.ts / config.go
│   └── infrastructure/
│       └── {database}      # database.py / database.ts / database.go
├── {migration_dir}/        # alembic/ / prisma/ / migrations/
├── scripts/
│   ├── run.{ext}
│   ├── migrate.{ext}
│   └── test.{ext}
├── {env_example}           # .env.example
└── {build_file}            # Makefile / justfile
```

## Bootstrap Components

### 1. Project Manifest

Declares dependencies, metadata, and entry points.

```yaml
manifest:
  metadata:
    name: "{project_name}"
    version: "0.1.0"
    description: "{from specifications}"
    
  entry_points:
    cli: "{project}.__main__:main"
    
  dependencies:
    # Core
    - web_framework      # FastAPI / Express / Gin
    - server             # Uvicorn / Node / Go stdlib
    - validation         # Pydantic / Zod / validator
    
    # Database
    - orm                # SQLAlchemy / Prisma / GORM
    - db_driver          # asyncpg / pg / pgx
    - migrations         # Alembic / Prisma / golang-migrate
    
    # HTTP client
    - http_client        # httpx / axios / net/http
    - retry              # tenacity / axios-retry / built-in
    
    # Observability
    - logging            # structlog / pino / zap
    - metrics            # prometheus / prom-client / prometheus
    - tracing            # opentelemetry / opentelemetry / otel
    
  dev_dependencies:
    - test_framework     # pytest / vitest / go test
    - type_checker       # mypy / typescript / go vet
    - linter             # ruff / eslint / golangci-lint
    - formatter          # ruff / prettier / gofmt
```

### 2. Application Entry Point

The main entry point for the application.

```yaml
entry_point:
  responsibilities:
    - Parse CLI arguments
    - Load configuration
    - Initialize logging
    - Initialize database
    - Create application
    - Start server
    - Handle shutdown gracefully
    
  cli_commands:
    - name: serve
      description: "Start the HTTP server"
      options:
        - "--host: Host to bind (default: 0.0.0.0)"
        - "--port: Port to bind (default: 8000)"
        - "--reload: Enable hot reload (dev only)"
        
    - name: migrate
      description: "Run database migrations"
      subcommands:
        - "up: Apply pending migrations"
        - "down: Rollback last migration"
        - "generate: Create new migration"
        
    - name: shell
      description: "Interactive shell with app context"
      
  lifecycle:
    startup:
      - load_config
      - init_logging
      - init_tracing
      - init_metrics
      - init_database
      - create_app
      - start_server
      
    shutdown:
      - drain_connections
      - close_database
      - flush_metrics
      - flush_traces
```

### 3. Configuration Module

Typed configuration loading from environment.

```yaml
configuration:
  sources:
    - environment_variables
    - dotenv_file
    - config_file (optional)
    - cli_arguments (override)
    
  structure:
    app:
      name: "{PROJECT_NAME}"
      env: "{APP_ENV:development}"  # development | staging | production
      debug: "{DEBUG:false}"
      secret_key: "{SECRET_KEY}"  # Required, no default
      
    server:
      host: "{HOST:0.0.0.0}"
      port: "{PORT:8000}"
      workers: "{WORKERS:1}"
      
    database:
      url: "{DATABASE_URL}"  # Required
      pool_size: "{DB_POOL_SIZE:5}"
      pool_max_overflow: "{DB_POOL_MAX_OVERFLOW:10}"
      echo: "{DB_ECHO:false}"
      
    redis:  # Optional
      url: "{REDIS_URL:}"
      
    external:
      shopify:
        api_key: "{SHOPIFY_API_KEY:}"
        api_secret: "{SHOPIFY_API_SECRET:}"
      groq:
        api_key: "{GROQ_API_KEY:}"
        
    observability:
      log_level: "{LOG_LEVEL:INFO}"
      log_format: "{LOG_FORMAT:json}"  # json | console
      metrics_enabled: "{METRICS_ENABLED:true}"
      tracing_enabled: "{TRACING_ENABLED:true}"
      tracing_endpoint: "{OTEL_ENDPOINT:}"
      
  validation:
    required_in_production:
      - secret_key
      - database.url
    
    constraints:
      - "pool_size > 0"
      - "port in range(1, 65536)"
```

### 4. Database Module

Database lifecycle management.

```yaml
database:
  responsibilities:
    - Create async engine
    - Configure connection pool
    - Provide session factory
    - Handle connection lifecycle
    - Support transactions
    
  components:
    engine:
      type: async
      pool_class: AsyncAdaptedQueuePool
      pool_pre_ping: true
      
    session_factory:
      type: async_sessionmaker
      expire_on_commit: false
      
    session_context:
      type: async_context_manager
      description: "Provides session for request lifecycle"
      
  lifecycle:
    init:
      - create_engine
      - verify_connection
      - run_migrations (if configured)
      
    get_session:
      - acquire_from_pool
      - yield_session
      - commit_or_rollback
      - return_to_pool
      
    close:
      - drain_pool
      - close_engine
      
  migration:
    tool: "{from standards}"  # Alembic / Prisma / golang-migrate
    auto_migrate: "{from config}"
    directory: "{migration_dir}"
```

### 5. Dependency Injection

Wiring all components together.

```yaml
dependency_injection:
  container:
    description: "Central registry for dependencies"
    
  registrations:
    # Configuration
    - name: config
      type: singleton
      factory: load_config
      
    # Database
    - name: engine
      type: singleton
      factory: create_engine
      depends: [config]
      
    - name: session_factory
      type: singleton
      factory: create_session_factory
      depends: [engine]
      
    # Repositories (request-scoped)
    - name: merchant_repository
      type: scoped
      factory: create_merchant_repository
      depends: [session]
      
    # External clients (singleton)
    - name: shopify_client
      type: singleton
      factory: create_shopify_client
      depends: [config]
      
    - name: groq_client
      type: singleton
      factory: create_groq_client
      depends: [config]
      
    # Services (request-scoped)
    - name: merchant_service
      type: scoped
      factory: create_merchant_service
      depends: [merchant_repository, shopify_client]
      
  injection_strategy:
    web_framework: "framework-native"  # FastAPI Depends / NestJS / Wire
```

### 6. Startup/Shutdown Hooks

Application lifecycle events.

```yaml
lifecycle_hooks:
  on_startup:
    - name: init_logging
      order: 1
      action: "Configure structured logging"
      
    - name: init_telemetry
      order: 2
      action: "Initialize OpenTelemetry"
      
    - name: init_database
      order: 3
      action: "Create engine, verify connection"
      
    - name: init_cache
      order: 4
      condition: "config.redis.url is set"
      action: "Connect to Redis"
      
    - name: warmup
      order: 5
      condition: "config.app.env == production"
      action: "Warm caches, preload data"
      
  on_shutdown:
    - name: drain_requests
      order: 1
      timeout: 30s
      action: "Stop accepting, finish in-flight"
      
    - name: close_database
      order: 2
      action: "Drain pool, close connections"
      
    - name: close_cache
      order: 3
      condition: "cache initialized"
      action: "Close Redis connection"
      
    - name: flush_telemetry
      order: 4
      action: "Flush pending spans/metrics"
```

### 7. Development Scripts

Helper scripts for common operations.

```yaml
scripts:
  run:
    description: "Start development server"
    commands:
      - load_dotenv
      - start_server(reload=true)
      
  migrate:
    description: "Run database migrations"
    subcommands:
      up: "Apply all pending migrations"
      down: "Rollback last migration"
      generate: "Create migration from model changes"
      
  test:
    description: "Run test suite"
    commands:
      - set_test_env
      - run_tests(coverage=true)
      
  lint:
    description: "Run linters"
    commands:
      - type_check
      - lint
      - format_check
      
  format:
    description: "Format code"
    commands:
      - format
      
  shell:
    description: "Interactive shell with app context"
    commands:
      - load_config
      - init_database
      - start_repl
```

## Language-Specific Templates

Reference templates for each target language:

```yaml
templates:
  python:
    manifest: "pyproject.toml.j2"
    entry_point: "__main__.py.j2"
    config: "config.py.j2"
    database: "database.py.j2"
    di_framework: "FastAPI Depends"
    migration_tool: "Alembic"
    reference: "/templates/python/"
    
  typescript:
    manifest: "package.json.j2"
    entry_point: "index.ts.j2"
    config: "config.ts.j2"
    database: "database.ts.j2"
    di_framework: "tsyringe or NestJS"
    migration_tool: "Prisma"
    reference: "/templates/typescript/"
    
  go:
    manifest: "go.mod.j2"
    entry_point: "main.go.j2"
    config: "config.go.j2"
    database: "database.go.j2"
    di_framework: "Wire"
    migration_tool: "golang-migrate"
    reference: "/templates/go/"
```

## Categorical Correspondence

```yaml
categorical:
  configuration:
    interpretation: "Reader monad environment"
    certificate: "monad.cert.yaml#reader_left_identity"
    
  dependency_injection:
    interpretation: "Reader monad composition"
    certificate: "monad.cert.yaml#reader_associativity"
    
  session_factory:
    interpretation: "IO monad - deferred effect"
    certificate: "monad.cert.yaml#io_left_identity"
    
  lifecycle:
    interpretation: "Bracket pattern (acquire/use/release)"
    certificate: "monad.cert.yaml#io_associativity"
```

## Validation Checks

```yaml
validation:
  manifest_complete:
    check: "All dependencies declared"
    
  entry_point_exists:
    check: "Main entry point created"
    
  config_typed:
    check: "All config fields have types"
    
  required_vars_documented:
    check: ".env.example lists all required vars"
    
  migrations_configured:
    check: "Migration tool properly set up"
    
  di_complete:
    check: "All services have factories"
```

## Integration with code-architect

```yaml
execution_order:
  # After all other generators, before validator
  position: 8
  after:
    - entity-generator
    - dto-generator
    - repository-generator
    - client-generator
    - service-generator
    - handler-generator
    - middleware-generator
  before:
    - code-validator
    
  inputs:
    - "generated/{language}/src/{project}/**"
    - "standards/configuration/*.std.yaml"
    - "maps/modules/services.map.yaml"
    
  outputs:
    - "generated/{language}/{manifest}"
    - "generated/{language}/src/{project}/{entry_point}"
    - "generated/{language}/src/{project}/{config}"
    - "generated/{language}/src/{project}/infrastructure/{database}"
    - "generated/{language}/scripts/*"
    - "generated/{language}/.env.example"
```
