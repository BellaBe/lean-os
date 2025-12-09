---
name: level-10-bootstrap
description: |
  Level 10: Bootstrap. Wire all generated code into a runnable application.
  Entry point, configuration, dependency injection, lifecycle management.
  
  Input: level-9.manifest.yaml (all generated code)
  Output: level-10.manifest.yaml + bootstrap code
  
  UNIVERSAL: Works for any domain. Multi-language support.
---

# Level 10: Bootstrap

Application wiring and entry point.

## CRITICAL: Generate Actual Files

**Level 10 produces ACTUAL BOOTSTRAP FILES, not manifest descriptions.**

```yaml
output_distinction:
  manifest_file:
    path: "level-10.manifest.yaml"
    contains: "References to generated files, NOT code itself"
    
  actual_files_required:
    - "generated/python/src/project/main.py"
    - "generated/python/src/project/container.py"  
    - "generated/python/src/project/config.py"
    - "generated/python/src/project/lifecycle.py"
    
  action: |
    USE FILE CREATION TOOL to create actual .py files
    DO NOT just describe what files would contain in YAML
    
  validation: |
    After L10 execution:
      ls generated/python/src/project/main.py  # Must exist
      python -c "from project.main import app"  # Must import
```

## Principle

Bootstrap is the Reader monad applied - dependency injection at the application level.

```
Bootstrap = Reader[Config, Application]

run: Config → Application
  where Application = composed system from Level 9 code
  
Dependencies flow inward:
  Config → Repositories → Services → Handlers → Application
```

## Components

```yaml
bootstrap_components:
  entry_point:
    description: "Main function / CLI"
    responsibilities:
      - Parse arguments
      - Load configuration
      - Initialize application
      - Start server
      - Handle shutdown
      
  configuration:
    description: "Typed configuration from environment"
    pattern: "Reader monad"
    sources:
      - environment_variables
      - config_files
      - cli_arguments
      
  dependency_injection:
    description: "Wire dependencies"
    pattern: "Reader monad composition"
    layers:
      - database: "Connection pool, session factory"
      - repositories: "Depend on database"
      - external_clients: "Depend on config"
      - services: "Depend on repositories, clients"
      - handlers: "Depend on services"
      
  lifecycle:
    description: "Startup and shutdown"
    pattern: "Bracket (acquire/use/release)"
    hooks:
      startup:
        - init_logging
        - init_tracing
        - init_database
        - run_migrations
        - warmup
      shutdown:
        - drain_requests
        - close_database
        - flush_telemetry
```

## Process

```yaml
process:
  step_1_load_inputs:
    inputs:
      - "level-9.manifest.yaml"
    action: "Load generated code manifest"
    
  step_2_identify_components:
    action: "Identify all components to wire"
    algorithm: |
      components = {
          repositories: level_9.where(kind="repository"),
          services: level_9.where(kind="service"),
          handlers: level_9.where(kind="handler"),
          middleware: level_9.where(kind="middleware"),
      }
      
  step_3_generate_config:
    action: "Generate configuration module"
    includes:
      - app_settings: "Name, env, debug"
      - server_settings: "Host, port, workers"
      - database_settings: "URL, pool size"
      - external_settings: "API keys, endpoints"
      
  step_4_generate_di:
    action: "Generate dependency injection container"
    pattern: "Language-appropriate DI"
    wiring:
      - "Config → Database"
      - "Database → Repositories"
      - "Config → ExternalClients"
      - "Repositories + Clients → Services"
      - "Services → Handlers"
      
  step_5_generate_entry:
    action: "Generate entry point"
    includes:
      - cli_parsing
      - config_loading
      - app_creation
      - server_startup
      - graceful_shutdown
      
  step_6_generate_lifecycle:
    action: "Generate lifecycle hooks"
    startup: "Ordered initialization"
    shutdown: "Reverse order cleanup"
    
  step_7_validate:
    action: "Validate bootstrap"
    checks:
      - all_dependencies_wired
      - no_circular_dependencies
      - config_complete
      - entry_point_works
      
  step_8_produce_manifest:
    action: "Write level-10.manifest.yaml"
```

## Output Structure by Language

### Python

```
generated/python/
├── pyproject.toml
├── src/{project}/
│   ├── __init__.py
│   ├── __main__.py          # Entry point
│   ├── config.py            # Configuration
│   ├── container.py         # DI container
│   ├── lifecycle.py         # Startup/shutdown
│   └── infrastructure/
│       └── database.py      # Session factory
└── scripts/
    ├── run.sh
    ├── migrate.sh
    └── test.sh
```

### TypeScript

```
generated/typescript/
├── package.json
├── src/
│   ├── index.ts             # Entry point
│   ├── config.ts            # Configuration
│   ├── container.ts         # DI container
│   └── infrastructure/
│       └── database.ts
└── scripts/
    ├── run.sh
    └── migrate.sh
```

## Configuration Schema

```yaml
config_schema:
  app:
    name: "string (from project)"
    env: "development | staging | production"
    debug: "boolean"
    secret_key: "string (required in production)"
    
  server:
    host: "string (default: 0.0.0.0)"
    port: "integer (default: 8000)"
    workers: "integer (default: 1)"
    
  database:
    url: "string (required)"
    pool_size: "integer (default: 5)"
    pool_max_overflow: "integer (default: 10)"
    echo: "boolean (default: false)"
    
  # External services (from specification)
  external:
    "{service_name}":
      api_key: "string"
      base_url: "string"
      timeout: "integer"
```

## Dependency Graph

```yaml
dependency_graph:
  config:
    depends_on: []
    
  database:
    depends_on: [config]
    provides: [engine, session_factory]
    
  repositories:
    depends_on: [database]
    provides: ["{entity}_repository" for entity in entities]
    
  external_clients:
    depends_on: [config]
    provides: ["{service}_client" for service in external_services]
    
  services:
    depends_on: [repositories, external_clients]
    provides: ["{module}_service" for module in modules]
    
  handlers:
    depends_on: [services]
    provides: ["router"]
    
  middleware:
    depends_on: [config]
    provides: ["middleware_chain"]
    
  application:
    depends_on: [handlers, middleware]
    provides: ["app"]
```

## Manifest Item Schema

```yaml
bootstrap_item:
  id: "bootstrap.{component}"
  name: "{ComponentName}"
  kind: "bootstrap"
  traces:
    - ref: "level-9.code.*.{dependent_item}"
      role: "wires"
  definition:
    type: "{config|database|container|entry|lifecycle}"
    dependencies: ["list of dependencies"]
  artifacts:
    - path: "generated/{lang}/..."
  status: "generated|validated"
```

## Validation Rules

```yaml
validation:
  all_dependencies_wired:
    rule: "Every component has its dependencies injected"
    critical: true
    
  no_circular:
    rule: "Dependency graph is acyclic"
    critical: true
    
  config_complete:
    rule: "All required config has defaults or is documented"
    critical: true
    
  entry_point_valid:
    rule: "Entry point can be executed"
    critical: true
    
  lifecycle_ordered:
    rule: "Startup order respects dependencies"
    critical: true
```

## Output

```
level-10.manifest.yaml
generated/{language}/
├── {manifest}            # pyproject.toml / package.json
├── src/{project}/
│   ├── {entry_point}     # __main__.py / index.ts
│   ├── {config}          # config.py / config.ts
│   ├── {container}       # container.py / container.ts
│   └── {lifecycle}       # lifecycle.py / lifecycle.ts
├── scripts/
│   └── ...
└── .env.example
```

## Invariant

```
∀ service ∈ Level9.services:
  ∃ wiring ∈ Level10: wiring.injects(service.dependencies)

dependency_graph.is_acyclic = true
entry_point.executable = true

Violation is FATAL. Pipeline MUST NOT proceed to Level 11.
```

## Example (Illustrative Only)

```yaml
# level-10.manifest.yaml
items:
  - id: "bootstrap.config"
    kind: "bootstrap"
    traces:
      - ref: "level-9.code.python.*"
        role: "configures"
    definition:
      type: "config"
      fields:
        - {name: "app", required: true}
        - {name: "database", required: true}
        - {name: "server", required: false}
    artifacts:
      - path: "generated/python/src/project/config.py"
      
  - id: "bootstrap.database"
    kind: "bootstrap"
    traces:
      - ref: "bootstrap.config"
        role: "depends_on"
    definition:
      type: "database"
      provides: ["engine", "session_factory"]
    artifacts:
      - path: "generated/python/src/project/infrastructure/database.py"
      
  - id: "bootstrap.container"
    kind: "bootstrap"
    traces:
      - ref: "bootstrap.database"
        role: "wires"
      - ref: "level-9.code.python.level-6.*"
        role: "wires"
      - ref: "level-9.code.python.level-3.*"
        role: "wires"
    definition:
      type: "container"
      registrations:
        - {name: "customer_repository", depends: ["session"]}
        - {name: "customer_service", depends: ["customer_repository"]}
    artifacts:
      - path: "generated/python/src/project/container.py"
      
  - id: "bootstrap.entry"
    kind: "bootstrap"
    traces:
      - ref: "bootstrap.container"
        role: "uses"
    definition:
      type: "entry"
      commands: ["serve", "migrate", "shell"]
    artifacts:
      - path: "generated/python/src/project/__main__.py"

counts:
  total: 5
  
validation:
  dependencies_wired: true
  no_circular: true
  entry_valid: true
  complete: true
```
