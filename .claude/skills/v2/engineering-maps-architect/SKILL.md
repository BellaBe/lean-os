---
name: maps-architect
description: |
  Orchestrator for the maps layer. Takes validated standards and produces language-agnostic
  implementation maps. Coordinates 8 sub-skills covering primitives, Kleisli composition,
  adjunctions, functors, natural transformations, monads, and module structure.
  Use after standards-architect completes successfully.
---

# Maps Architect

Entry point for the Maps Layer. Transforms categorical standards into implementation maps.

## Purpose

Orchestrate the complete mapping pipeline:
1. Map primitive types to abstract representations
2. Map Kleisli composition patterns
3. Map adjunctions to paired operations
4. Map functors to transformations
5. Map natural transformations to middleware/adapters
6. Map monads to effect handlers
7. Map to module/service structure
8. Validate and gate to proofs layer

## Input

Validated standards and specifications:

```
specifications/v{X}/
├── domain-concepts.yaml
├── requirements.adt
├── services.spec.yaml
├── architecture.categorical
└── types.curry-howard

standards/
├── categories/*.std.yaml
├── security/*.std.yaml
├── observability/*.std.yaml
├── caching/*.std.yaml
├── transactions/*.std.yaml
├── configuration/*.std.yaml
└── api-versioning/*.std.yaml
```

## Output

Language-agnostic implementation maps:

```
maps/
├── primitives/
│   ├── types.map.yaml           # Type mappings
│   └── identifiers.map.yaml     # ID type mappings
├── kleisli/
│   ├── effects.map.yaml         # Effect composition
│   └── interpreters.map.yaml    # Effect interpreters
├── adjunctions/
│   ├── repository.map.yaml      # Free ⊣ Repository
│   ├── cache.map.yaml           # Forget ⊣ Cache
│   └── external.map.yaml        # Domain ⊣ External
├── functors/
│   ├── http.map.yaml            # Domain → HTTP
│   ├── storage.map.yaml         # Domain → Storage
│   └── external.map.yaml        # Domain → External
├── transformations/
│   ├── middleware.map.yaml      # HTTP transformations
│   ├── auth.map.yaml            # Auth transformation
│   └── observability.map.yaml   # Metrics/tracing
├── monads/
│   ├── io.map.yaml              # IO monad
│   ├── either.map.yaml          # Error handling
│   ├── reader.map.yaml          # Configuration
│   └── transaction.map.yaml     # Transactions
├── modules/
│   ├── services.map.yaml        # Service structure
│   ├── repositories.map.yaml    # Repository structure
│   └── handlers.map.yaml        # HTTP handlers
├── generators/
│   ├── abstract/                # Language-agnostic patterns
│   ├── python/                  # Python-specific
│   ├── typescript/              # TypeScript-specific
│   └── go/                      # Go-specific
├── versions.yaml                # Version tracking
└── validation-report.yaml       # Validation results
```

## Pipeline

```
                               MAPS ARCHITECT
┌─────────────────────────────────────────────────────────────────────────────┐
│                                                                             │
│  ┌─────────────────────┐                                                    │
│  │ Standards + Specs   │                                                    │
│  │   (from Phase 1)    │                                                    │
│  └──────────┬──────────┘                                                    │
│             │                                                               │
│             ▼                                                               │
│  ┌─────────────────────┐                                                    │
│  │  primitives-mapper  │                                                    │
│  └──────────┬──────────┘                                                    │
│             │                                                               │
│     ┌───────┴───────┬───────────────┬───────────────┐                      │
│     │               │               │               │                      │
│     ▼               ▼               ▼               ▼                      │
│  ┌────────┐  ┌────────────┐  ┌──────────┐  ┌───────────────┐               │
│  │kleisli │  │ adjunction │  │ functor  │  │ transformation│               │
│  │-mapper │  │  -mapper   │  │ -mapper  │  │    -mapper    │               │
│  └───┬────┘  └─────┬──────┘  └────┬─────┘  └───────┬───────┘               │
│      │             │              │                │                       │
│      └─────────────┴──────────────┴────────────────┘                       │
│                    │                                                        │
│                    ▼                                                        │
│           ┌────────────────┐                                                │
│           │  monad-mapper  │                                                │
│           └───────┬────────┘                                                │
│                   │                                                         │
│                   ▼                                                         │
│           ┌────────────────┐                                                │
│           │ module-mapper  │                                                │
│           └───────┬────────┘                                                │
│                   │                                                         │
│                   ▼                                                         │
│           ┌────────────────┐                                                │
│           │ maps-validator │                                                │
│           └───────┬────────┘                                                │
│                   │                                                         │
│          ┌────────┴────────┐                                                │
│          │                 │                                                │
│          ▼                 ▼                                                │
│       [PASS]            [FAIL]                                              │
│          │                 │                                                │
│          ▼                 ▼                                                │
│    Proofs Layer       Fix & Retry                                           │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Sub-Skills

| Order | Skill | Purpose | Dependencies |
|-------|-------|---------|--------------|
| 1 | primitives-mapper | Map types | Standards |
| 2a | kleisli-mapper | Effect composition | primitives |
| 2b | adjunction-mapper | Paired operations | primitives |
| 2c | functor-mapper | Structure-preserving maps | primitives |
| 2d | transformation-mapper | Natural transformations | primitives |
| 3 | monad-mapper | Effect handlers | kleisli, adjunction |
| 4 | module-mapper | Service structure | All above |
| 5 | maps-validator | Gate to proofs | All maps |

**Parallel execution:** Steps 2a-2d can run in parallel after step 1.

## Execution Modes

### Mode 1: Full Generation

Generate all maps from standards:

```yaml
mode: full
standards_version: 1
specification_version: 1
target_languages:
  - python
  - typescript
output_dir: maps/
```

### Mode 2: Incremental Update

Update maps when standards change:

```yaml
mode: incremental
standards_version: 2
base_maps_version: 1
changes:
  - modified: security/authentication.std.yaml
  - added: caching/cache.std.yaml
```

### Mode 3: Single Target

Generate for specific language only:

```yaml
mode: single_target
target: python
version: "3.11"
```

### Mode 4: Validation Only

Re-validate existing maps:

```yaml
mode: validate
maps_version: 1
```

## Language Abstraction

Maps are language-agnostic by design. Each map defines:

```yaml
# Abstract pattern
pattern:
  name: repository_get
  categorical: "Free ⊣ Repository counit application"
  abstract:
    signature: "Id[A] → IO[Either[NotFound, A]]"
    steps:
      - build_query
      - execute_query
      - map_result
      
# Target-specific implementations
targets:
  python:
    file: "{module}/repositories/{entity}_repository.py"
    template: |
      async def get(self, id: {Entity}Id) -> Either[NotFound, {Entity}]:
          query = select({Entity}).where({Entity}.id == id)
          result = await self.session.execute(query)
          return result.scalar_one_or_none() |> to_either
          
  typescript:
    file: "{module}/repositories/{entity}.repository.ts"
    template: |
      async get(id: {Entity}Id): Promise<Either<NotFound, {Entity}>> {
        return this.prisma.{entity}.findUnique({ where: { id } })
          .then(toEither);
      }
```

## Orchestration Logic

### Dependency Resolution

```yaml
dependencies:
  primitives-mapper: [standards, specifications]
  kleisli-mapper: [primitives-mapper]
  adjunction-mapper: [primitives-mapper]
  functor-mapper: [primitives-mapper]
  transformation-mapper: [primitives-mapper]
  monad-mapper:
    - kleisli-mapper
    - adjunction-mapper
  module-mapper:
    - monad-mapper
    - functor-mapper
    - transformation-mapper
  maps-validator:
    - ALL
```

### Change Propagation

```yaml
change_propagation:
  primitives/*.map.yaml:
    invalidates: [ALL]
    action: full_regeneration
    
  kleisli/*.map.yaml:
    invalidates:
      - monads/*.map.yaml
      - modules/*.map.yaml
    action: re-run affected mappers
    
  functors/*.map.yaml:
    invalidates:
      - modules/*.map.yaml
    action: re-run module-mapper
```

## Inter-Skill Validation

```yaml
inter_skill_validation:
  strategy: halt_on_error
  
  after_each_skill:
    - name: schema_valid
      check: "Map output matches schema"
      on_failure: halt
      
    - name: categorical_correspondence
      check: "Maps preserve categorical structure"
      on_failure: halt
      
    - name: target_consistency
      check: "All targets have same abstract pattern"
      on_failure: halt
      
  on_halt:
    present_to_human:
      context: "Standards + current maps"
      error: "What validation failed"
      suggestions:
        - "Adjust standard definition"
        - "Fix map pattern"
        - "Override with warning"
    await_decision:
      options:
        - retry
        - fix_upstream
        - override
        - abort
```

## Feedback Loops

```yaml
feedback_loops:
  enabled: true
  
  patterns:
    - from: adjunction-mapper
      to: category-standard-definer
      triggers:
        - "Adjunction unit/counit missing"
        - "Triangle identities don't translate"
      action:
        notify: true
        suggest_fix: true
        
    - from: monad-mapper
      to: kleisli-mapper
      triggers:
        - "Kleisli composition pattern missing"
        - "Effect type not mapped"
      action:
        notify: true
        suggest_fix: true
        
    - from: module-mapper
      to: functor-mapper
      triggers:
        - "Functor mapping incomplete"
        - "Service boundary unclear"
      action:
        notify: true
        suggest_fix: true
        
  human_escalation:
    trigger: "Cannot auto-resolve after 2 iterations"
    present:
      - error_context
      - affected_maps
      - standards_source
    await: human_decision
```

## Validation Gates

```yaml
validation_gates:
  # Gate 1: After primitives
  post_primitives:
    skill: primitives-mapper
    checks:
      - all_adt_types_mapped
      - identifiers_have_representations
      - no_unmapped_primitives
    blocking: true
    
  # Gate 2: After categorical mappings
  post_categorical:
    skills:
      - kleisli-mapper
      - adjunction-mapper
      - functor-mapper
      - transformation-mapper
    checks:
      - all_effects_have_interpreters
      - all_adjunctions_have_implementations
      - all_functors_preserve_structure
      - all_transformations_are_natural
    blocking: true
    
  # Gate 3: After monad mapping
  post_monads:
    skill: monad-mapper
    checks:
      - monad_laws_implementable
      - bind_has_implementation
      - effects_compose
    blocking: true
    
  # Gate 4: Final validation
  final:
    skill: maps-validator
    checks:
      - all_standards_covered
      - all_morphisms_mapped
      - target_code_generates
      - no_categorical_violations
    blocking: true
    gate_to: proofs_layer
```

## Configuration

```yaml
maps_architect:
  # Execution settings
  parallel_execution: true
  max_iterations: 5
  
  # Output settings
  output_dir: "maps"
  version_strategy: semantic
  
  # Target settings
  default_targets:
    - python
  available_targets:
    - python
    - typescript
    - go
    
  # Validation settings
  strict_mode: true
  require_all_targets: false
  
  # Sub-skill settings
  skills:
    primitives-mapper:
      include_newtypes: true
    kleisli-mapper:
      default_effect: "IO[Either[E, A]]"
    module-mapper:
      structure: onion  # or: hexagonal, clean
```

## Categorical Correspondence

Maps preserve categorical structure:

```
Standards            Maps                    Generated Code
─────────           ─────                   ──────────────
Category     ──►    Module structure  ──►   Package/namespace
Object       ──►    Type mapping      ──►   Class/type/interface
Morphism     ──►    Function pattern  ──►   Method/function
Functor      ──►    Transformer       ──►   Adapter/mapper class
Adjunction   ──►    Paired operations ──►   Repository pattern
Monad        ──►    Effect handler    ──►   Async/Result pattern
Nat. Trans.  ──►    Middleware        ──►   Decorator/wrapper
```

## Checklist

Before marking maps complete:

- [ ] All ADT types have primitive mappings
- [ ] All effects have Kleisli interpreters
- [ ] All adjunctions have unit/counit implementations
- [ ] All functors have object and morphism maps
- [ ] All natural transformations have component implementations
- [ ] All monads have bind/pure implementations
- [ ] Module structure covers all services
- [ ] At least one target language fully mapped
- [ ] Validation passes

## Next Phase

On successful validation, hand off to Proofs Layer:

```
Maps Architect (complete)
         │
         ▼
┌─────────────────────┐
│  proofs-architect   │ ← Next orchestrator
└─────────────────────┘
```
