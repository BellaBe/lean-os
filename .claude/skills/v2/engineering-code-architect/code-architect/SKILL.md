---
name: code-architect
description: |
  Orchestrator for the code layer. Takes validated maps and proofs to generate
  production-ready code. Coordinates 8 sub-skills covering entities, repositories,
  services, handlers, middleware, clients, and DTOs. Generates Python by default
  with TypeScript/Go templates available.
  Use after proofs-architect completes successfully.
---

# Code Architect

Entry point for the Code Layer. Generates executable implementations.

## Purpose

Orchestrate the complete code generation pipeline:
1. Generate domain entities from type maps
2. Generate repositories from adjunction maps
3. Generate services from module maps
4. Generate HTTP handlers from functor maps
5. Generate middleware from transformation maps
6. Generate external clients from external maps
7. Generate DTOs from HTTP maps
8. Validate all generated code

## Input

Validated maps, proofs, and certificates:

```
maps/
├── primitives/*.map.yaml
├── kleisli/*.map.yaml
├── adjunctions/*.map.yaml
├── functors/*.map.yaml
├── transformations/*.map.yaml
├── monads/*.map.yaml
├── modules/*.map.yaml
└── versions.yaml

proofs/
├── certificates/
│   └── manifest.yaml
└── versions.yaml

specifications/v{X}/
├── requirements.adt
├── services.spec.yaml
└── ...
```

## Output

Production-ready code:

```
generated/
├── python/
│   ├── pyproject.toml
│   ├── src/
│   │   └── {project}/
│   │       ├── __init__.py
│   │       ├── domain/
│   │       │   ├── __init__.py
│   │       │   ├── entities/
│   │       │   │   ├── __init__.py
│   │       │   │   ├── merchant.py
│   │       │   │   ├── profile.py
│   │       │   │   └── analysis.py
│   │       │   ├── value_objects/
│   │       │   │   ├── __init__.py
│   │       │   │   └── identifiers.py
│   │       │   └── events/
│   │       │       └── __init__.py
│   │       ├── application/
│   │       │   ├── __init__.py
│   │       │   ├── services/
│   │       │   │   ├── __init__.py
│   │       │   │   ├── merchant_service.py
│   │       │   │   ├── profile_service.py
│   │       │   │   └── analysis_service.py
│   │       │   ├── dtos/
│   │       │   │   ├── __init__.py
│   │       │   │   ├── requests.py
│   │       │   │   └── responses.py
│   │       │   └── ports/
│   │       │       ├── __init__.py
│   │       │       ├── repositories.py
│   │       │       └── external.py
│   │       ├── infrastructure/
│   │       │   ├── __init__.py
│   │       │   ├── repositories/
│   │       │   │   ├── __init__.py
│   │       │   │   ├── merchant_repository.py
│   │       │   │   ├── profile_repository.py
│   │       │   │   └── analysis_repository.py
│   │       │   ├── models/
│   │       │   │   ├── __init__.py
│   │       │   │   └── database.py
│   │       │   ├── external/
│   │       │   │   ├── __init__.py
│   │       │   │   ├── shopify_client.py
│   │       │   │   └── groq_client.py
│   │       │   └── cache/
│   │       │       └── __init__.py
│   │       └── api/
│   │           ├── __init__.py
│   │           ├── main.py
│   │           ├── routes/
│   │           │   ├── __init__.py
│   │           │   ├── merchant_routes.py
│   │           │   ├── profile_routes.py
│   │           │   └── analysis_routes.py
│   │           ├── middleware/
│   │           │   ├── __init__.py
│   │           │   ├── auth.py
│   │           │   ├── metrics.py
│   │           │   └── logging.py
│   │           └── dependencies.py
│   └── tests/
│       └── ...
├── typescript/  # Templates
│   └── ...
├── go/          # Templates
│   └── ...
├── versions.yaml
└── validation-report.yaml
```

## Pipeline

```
                               CODE ARCHITECT
┌─────────────────────────────────────────────────────────────────────────────┐
│                                                                             │
│  ┌─────────────────────┐                                                    │
│  │  Maps + Proofs      │                                                    │
│  │   (from Phase 2+3)  │                                                    │
│  └──────────┬──────────┘                                                    │
│             │                                                               │
│             ▼                                                               │
│  ┌─────────────────────┐                                                    │
│  │  entity-generator   │ ← Domain entities from primitives                  │
│  └──────────┬──────────┘                                                    │
│             │                                                               │
│     ┌───────┴───────┐                                                       │
│     │               │                                                       │
│     ▼               ▼                                                       │
│  ┌────────┐  ┌────────────┐                                                 │
│  │  dto   │  │ repository │                                                 │
│  │-gen    │  │   -gen     │                                                 │
│  └───┬────┘  └─────┬──────┘                                                 │
│      │             │                                                        │
│      └──────┬──────┘                                                        │
│             │                                                               │
│     ┌───────┴───────┐                                                       │
│     │               │                                                       │
│     ▼               ▼                                                       │
│  ┌────────┐  ┌────────────┐                                                 │
│  │client  │  │  service   │                                                 │
│  │-gen    │  │   -gen     │                                                 │
│  └───┬────┘  └─────┬──────┘                                                 │
│      │             │                                                        │
│      └──────┬──────┘                                                        │
│             │                                                               │
│             ▼                                                               │
│  ┌─────────────────────┐                                                    │
│  │  handler-generator  │                                                    │
│  └──────────┬──────────┘                                                    │
│             │                                                               │
│             ▼                                                               │
│  ┌──────────────────────┐                                                   │
│  │ middleware-generator │                                                   │
│  └──────────┬───────────┘                                                   │
│             │                                                               │
│             ▼                                                               │
│  ┌───────────────────────┐                                                  │
│  │  bootstrap-generator  │                                                  │
│  └──────────┬────────────┘                                                  │
│             │                                                               │
│             ▼                                                               │
│  ┌────────────────┐                                                         │
│  │ code-validator │                                                         │
│  └────────┬───────┘                                                         │
│           │                                                                 │
│     ┌─────┴─────┐                                                           │
│     │           │                                                           │
│     ▼           ▼                                                           │
│  [PASS]      [FAIL]                                                         │
│     │           │                                                           │
│     ▼           ▼                                                           │
│ Infra Layer  Fix & Retry                                                    │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Sub-Skills

| Order | Skill | Purpose | Dependencies |
|-------|-------|---------|--------------|
| 1 | entity-generator | Domain entities + value objects | primitives maps |
| 2a | dto-generator | Request/Response DTOs | HTTP functor maps |
| 2b | repository-generator | Repository implementations | adjunction maps, entities |
| 3a | client-generator | External API clients | external functor maps |
| 3b | service-generator | Application services | module maps, repos |
| 4 | handler-generator | HTTP route handlers | HTTP maps, services |
| 5 | middleware-generator | Auth, metrics, logging | transformation maps |
| 6 | bootstrap-generator | Entry point, config, DI | all code, standards |
| 7 | code-validator | Gate to infra layer | All code |

**Parallel execution:** Steps 2a-2b and 3a-3b can run in parallel.

## Execution Modes

### Mode 1: Full Generation

Generate complete codebase:

```yaml
mode: full
maps_version: 1
proofs_version: 1
target: python
project_name: glamyouup
output_dir: generated/
```

### Mode 2: Incremental

Update code when maps change:

```yaml
mode: incremental
maps_version: 2
base_code_version: 1
changes:
  - modified: modules/services.map.yaml
```

### Mode 3: Single Module

Generate specific module:

```yaml
mode: single_module
module: merchant
target: python
```

### Mode 4: Multi-Target

Generate for multiple languages:

```yaml
mode: multi_target
targets:
  - python
  - typescript
```

## Code Generation Principles

### 1. Categorical Correspondence

Every generated component corresponds to a categorical structure:

```yaml
correspondence:
  Entity: Object in Domain category
  Repository: Adjunction implementation (Free ⊣ Repository)
  Service: Morphism composition in Kleisli category
  Handler: HTTP functor application
  Middleware: Natural transformation component
  DTO: Functor object mapping
```

### 2. Onion Architecture

Generated code follows strict layer dependencies:

```
┌─────────────────────────────────────┐
│           API (Handlers)            │  ← Depends on Application
├─────────────────────────────────────┤
│    Infrastructure (Repos, Clients)  │  ← Depends on Domain + Application
├─────────────────────────────────────┤
│   Application (Services, DTOs)      │  ← Depends on Domain
├─────────────────────────────────────┤
│          Domain (Entities)          │  ← No dependencies
└─────────────────────────────────────┘
```

### 3. Effect Handling

All effects use monadic patterns:

```python
# From monad maps
async def create_merchant(self, data: CreateMerchantDTO) -> Result[Merchant, MerchantError]:
    """
    Effect: IO[Either[MerchantError, Merchant]]
    Certificate: monad.cert.yaml#io_associativity
    """
```

### 4. Type Safety

Generated code preserves type relationships:

```python
# From primitives map
MerchantId = NewType("MerchantId", UUID)
ProfileId = NewType("ProfileId", UUID)
# MerchantId ≠ ProfileId at type level
```

## Dependency Resolution

```yaml
dependencies:
  entity-generator: [primitives_maps]
  dto-generator: [http_functor_maps, entity-generator]
  repository-generator: [adjunction_maps, entity-generator]
  client-generator: [external_functor_maps, entity-generator]
  service-generator: [module_maps, repository-generator, client-generator]
  handler-generator: [http_maps, service-generator, dto-generator]
  middleware-generator: [transformation_maps]
  bootstrap-generator: [ALL_CODE, standards/configuration]
  code-validator: [ALL]
```

## Configuration

```yaml
code_architect:
  # Target settings
  primary_target: python
  additional_targets: []
  
  # Python settings
  python:
    version: "3.11"
    package_manager: "poetry"
    async_framework: "asyncio"
    web_framework: "fastapi"
    orm: "sqlalchemy"
    
  # Project settings
  project_name: "glamyouup"
  output_dir: "generated"
  
  # Generation settings
  generate_tests: true
  generate_docs: true
  include_certificates: true
  
  # Validation settings
  type_check: true
  lint: true
  format: true
```

## Inter-Skill Validation

```yaml
inter_skill_validation:
  strategy: halt_on_error
  
  after_each_skill:
    - name: syntax_valid
      check: "Python syntax is valid"
      command: "python -m py_compile {file}"
      
    - name: imports_resolve
      check: "All imports resolve"
      
    - name: types_valid
      check: "Type hints are valid"
      command: "mypy {file}"
      
  on_halt:
    present_to_human:
      context: "Generated code + error"
      suggestions:
        - "Fix map template"
        - "Add missing type"
        - "Resolve import cycle"
```

## Validation Gates

```yaml
validation_gates:
  post_entities:
    skill: entity-generator
    checks:
      - all_entities_generated
      - no_circular_imports
    blocking: true
    
  post_infrastructure:
    skills:
      - repository-generator
      - client-generator
    checks:
      - adjunction_implementations_complete
      - functor_implementations_complete
    blocking: true
    
  post_application:
    skill: service-generator
    checks:
      - all_services_generated
      - ports_implemented
    blocking: true
    
  post_api:
    skills:
      - handler-generator
      - middleware-generator
    checks:
      - all_routes_generated
      - middleware_chain_complete
    blocking: true
    
  post_bootstrap:
    skill: bootstrap-generator
    checks:
      - entry_point_exists
      - config_complete
      - database_lifecycle_defined
      - di_wired
    blocking: true
    
  final:
    skill: code-validator
    checks:
      - code_compiles
      - types_valid
      - tests_pass
      - no_lint_errors
    blocking: true
    gate_to: infrastructure_layer
```

## Certificate Integration

Generated code includes certificate references:

```python
class MerchantRepository(IMerchantRepository):
    """
    Implements Free ⊣ Repository adjunction.
    
    Proofs:
    - repository_left_triangle: certificates/adjunction.cert.yaml
    - repository_right_triangle: certificates/adjunction.cert.yaml
    
    Invariants:
    - save(entity) → get(id) returns equivalent entity
    - Round-trip preserves identity (up to iso)
    """
```

## Checklist

Before marking code complete:

- [ ] All entities generated from type maps
- [ ] All repositories implement adjunctions
- [ ] All services compose correctly (Kleisli)
- [ ] All handlers apply HTTP functor
- [ ] All middleware are natural transformations
- [ ] Entry point and CLI configured
- [ ] Configuration loading implemented
- [ ] Database lifecycle managed
- [ ] Dependency injection wired
- [ ] Code passes type checking
- [ ] Code passes linting
- [ ] Tests generated and passing
- [ ] Certificate references included

## Next Phase

On successful validation, hand off to Infrastructure Layer:

```
Code Architect (complete)
         │
         ▼
┌─────────────────────────┐
│  infra-architect        │ ← Next orchestrator
└─────────────────────────┘
```
