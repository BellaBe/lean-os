# LeanOS Skills

Categorical system builder pipeline. **48 skills** transform natural language requirements through mathematical specifications, standards, maps, and proofs into verified, production-ready code.

## Overview

```
┌─────────────────────────────────────────────────────────────────────────────┐
│ PHASE 0: SPECIFICATIONS (11 skills)                                         │
│   NL requirements → ADTs, constraints, morphisms, state machines            │
└─────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ PHASE 1: STANDARDS (9 skills)                                               │
│   Categorical structure → universal properties, cross-cutting concerns      │
└─────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ PHASE 2: MAPS (9 skills)                                                    │
│   Standards → language-agnostic implementation patterns                     │
└─────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ PHASE 3: PROOFS (9 skills)                                                  │
│   Maps → Lean 4 verification, runtime certificates                          │
└─────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ PHASE 4: CODE (10 skills)                                                   │
│   Maps + Certificates → production code (Python/TypeScript/Go)              │
└─────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ PHASE 5: INFRASTRUCTURE (future)                                            │
│   Docker, NATS, Caddy, monitoring, deployment                               │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Phase 0: Specification Layer

**Entry point:** `specifications-architect`

Transforms natural language requirements into validated, mathematically structured specifications.

### Skills

| # | Skill | Purpose | Output |
|---|-------|---------|--------|
| 0 | specifications-architect | Orchestrator | `specifications/v{X}/` |
| 1 | domain-extractor | Extract domain concepts | `domain-concepts.yaml` |
| 2 | type-synthesizer | Create ADTs | `requirements.adt` |
| 3 | constraint-specifier | Formalize rules | `constraints.yaml` |
| 4 | morphism-specifier | Define operations | `services.spec.yaml` |
| 5 | effect-analyzer | Tag with effects | `services.spec.yaml` |
| 6 | resilience-specifier | Add fault tolerance | `services.spec.yaml` |
| 7 | state-machine-extractor | Extract lifecycles | `state-machines.yaml` |
| 8 | categorical-structure-detector | Identify structure | `architecture.categorical` |
| 9 | proof-obligation-generator | Create proofs | `types.curry-howard` |
| 10 | specification-validator | Gate to standards | `versions.yaml` |

---

## Phase 1: Standards Layer

**Entry point:** `standards-architect`

Transforms specifications into universal property definitions and cross-cutting concerns.

### Skills

| # | Skill | Purpose | Output |
|---|-------|---------|--------|
| 0 | standards-architect | Orchestrator | `standards/` |
| 1 | category-standard-definer | Category structure | `categories/*.std.yaml` |
| 2 | security-standard-definer | Security patterns | `security/*.std.yaml` |
| 3 | observability-standard-definer | Metrics/tracing/logging | `observability/*.std.yaml` |
| 4 | caching-standard-definer | Cache adjunction | `caching/*.std.yaml` |
| 5 | transaction-standard-definer | Transaction monad | `transactions/*.std.yaml` |
| 6 | configuration-standard-definer | Config reader | `configuration/*.std.yaml` |
| 7 | api-versioning-standard-definer | Version management | `api-versioning/*.std.yaml` |
| 8 | standards-validator | Gate to maps | `versions.yaml` |

### Standards Output Structure

```
standards/
├── categories/
│   ├── domain.std.yaml         # Domain category laws
│   ├── storage.std.yaml        # Repository adjunction
│   ├── external.std.yaml       # External functor
│   └── http.std.yaml           # HTTP category
├── security/
│   ├── authentication.std.yaml # Identity verification
│   ├── authorization.std.yaml  # RBAC/ABAC model
│   ├── sanitization.std.yaml   # Input/output cleaning
│   └── tenant-isolation.std.yaml # Multi-tenancy
├── observability/
│   ├── metrics.std.yaml        # Metrics functor
│   ├── tracing.std.yaml        # Trace transformation
│   └── logging.std.yaml        # Logging side effect
├── caching/
│   ├── cache.std.yaml          # Forget ⊣ Cache adjunction
│   └── invalidation.std.yaml   # Invalidation strategies
├── transactions/
│   ├── transaction.std.yaml    # Transaction monad
│   └── saga.std.yaml           # Distributed saga
├── configuration/
│   ├── config.std.yaml         # Reader monad
│   └── feature-flags.std.yaml  # Conditional morphisms
├── api-versioning/
│   ├── versioning.std.yaml     # Version strategy
│   └── deprecation.std.yaml    # Migration paths
├── versions.yaml               # Version tracking
└── validation-report.yaml      # Validation results
```

---

## Phase 2: Maps Layer

**Entry point:** `maps-architect`

Transforms standards into language-agnostic implementation maps.

### Skills

| # | Skill | Purpose | Output |
|---|-------|---------|--------|
| 0 | maps-architect | Orchestrator | `maps/` |
| 1 | primitives-mapper | Type mappings | `primitives/*.map.yaml` |
| 2 | kleisli-mapper | Effect composition | `kleisli/*.map.yaml` |
| 3 | adjunction-mapper | Paired operations | `adjunctions/*.map.yaml` |
| 4 | functor-mapper | Structure transforms | `functors/*.map.yaml` |
| 5 | transformation-mapper | Middleware/adapters | `transformations/*.map.yaml` |
| 6 | monad-mapper | Effect handlers | `monads/*.map.yaml` |
| 7 | module-mapper | Service structure | `modules/*.map.yaml` |
| 8 | maps-validator | Gate to proofs | `versions.yaml` |

### Maps Output Structure

```
maps/
├── primitives/
│   ├── types.map.yaml          # Base and composite types
│   └── identifiers.map.yaml    # Typed ID newtypes
├── kleisli/
│   ├── effects.map.yaml        # IO, Either, composed
│   └── interpreters.map.yaml   # Effect execution
├── adjunctions/
│   ├── repository.map.yaml     # Free ⊣ Repository
│   ├── cache.map.yaml          # Forget ⊣ Cache
│   └── external.map.yaml       # Domain ⊣ External
├── functors/
│   ├── http.map.yaml           # Domain → HTTP
│   ├── storage.map.yaml        # Domain → Storage
│   └── external.map.yaml       # Domain → External
├── transformations/
│   ├── middleware.map.yaml     # HTTP middleware chain
│   ├── auth.map.yaml           # Auth transformations
│   └── observability.map.yaml  # Metrics/tracing/logging
├── monads/
│   ├── io.map.yaml             # Async/side effects
│   ├── either.map.yaml         # Error handling
│   ├── reader.map.yaml         # Dependency injection
│   └── transaction.map.yaml    # Database transactions
├── modules/
│   ├── services.map.yaml       # Service layer
│   ├── repositories.map.yaml   # Repository layer
│   └── handlers.map.yaml       # HTTP handlers
├── generators/
│   ├── abstract/               # Language-agnostic
│   ├── python/                 # Python targets
│   └── typescript/             # TypeScript targets
├── versions.yaml               # Version tracking
└── validation-report.yaml      # Validation results
```

---

## Phase 3: Proofs Layer

**Entry point:** `proofs-architect`

Generates Lean 4 proofs for all categorical laws.

### Skills

| # | Skill | Purpose | Output |
|---|-------|---------|--------|
| 0 | proofs-architect | Orchestrator | `proofs/` |
| 1 | identity-law-prover | id∘f = f = f∘id | `Identity.lean` |
| 2 | composition-law-prover | (h∘g)∘f = h∘(g∘f) | `Composition.lean` |
| 3 | functor-law-prover | F(id)=id, F(g∘f)=F(g)∘F(f) | `Functor.lean` |
| 4 | adjunction-law-prover | η, ε, triangles | `Adjunction.lean` |
| 5 | monad-law-prover | Monad laws | `Monad.lean` |
| 6 | naturality-prover | α_B∘F(f) = G(f)∘α_A | `NaturalTransformation.lean` |
| 7 | certificate-generator | Runtime certificates | `certificates/*.cert.yaml` |
| 8 | proofs-validator | Gate to code | `versions.yaml` |

### Proofs Output Structure

```
proofs/
├── lean/
│   ├── LeanOS.lean              # Main module
│   ├── LeanOS/
│   │   ├── Basic.lean           # Definitions
│   │   ├── Category.lean        # Category structure
│   │   ├── Identity.lean        # id∘f = f
│   │   ├── Composition.lean     # Associativity
│   │   ├── Functor.lean         # Functor laws
│   │   ├── Adjunction.lean      # Unit/counit/triangles
│   │   ├── Monad.lean           # Monad laws
│   │   └── NaturalTransformation.lean
│   ├── lakefile.lean
│   └── lean-toolchain
├── certificates/
│   ├── identity.cert.yaml
│   ├── composition.cert.yaml
│   ├── functor.cert.yaml
│   ├── adjunction.cert.yaml
│   ├── monad.cert.yaml
│   ├── naturality.cert.yaml
│   └── manifest.yaml
├── versions.yaml
└── validation-report.yaml
```

---

## Phase 4: Code Layer

**Entry point:** `code-architect`

Generates production-ready code from maps and proofs. Language-agnostic design with Python as default target.

### Skills

| # | Skill | Purpose | Output |
|---|-------|---------|--------|
| 0 | code-architect | Orchestrator | `generated/` |
| 1 | entity-generator | Domain entities | `domain/entities/` |
| 2 | dto-generator | Request/Response DTOs | `application/dtos/` |
| 3 | repository-generator | Repository implementations | `infrastructure/repositories/` |
| 4 | client-generator | External API clients | `infrastructure/external/` |
| 5 | service-generator | Application services | `application/services/` |
| 6 | handler-generator | HTTP route handlers | `api/routes/` |
| 7 | middleware-generator | Auth, metrics, logging | `api/middleware/` |
| 8 | bootstrap-generator | Entry point, config, DI | `__main__`, `config`, `database` |
| 9 | code-validator | Gate to infrastructure | `versions.yaml` |

### Generated Code Structure

```
generated/{language}/
├── {manifest}                  # pyproject.toml / package.json / go.mod
├── .env.example
├── scripts/
│   ├── run.{ext}
│   ├── migrate.{ext}
│   └── test.{ext}
├── src/{project}/
│   ├── {entry_point}           # __main__.py / index.ts / main.go
│   ├── {config}                # config.py / config.ts / config.go
│   ├── domain/
│   │   ├── entities/           # Product types → dataclasses
│   │   └── value_objects/      # NewTypes, Result
│   ├── application/
│   │   ├── services/           # Kleisli composition
│   │   ├── dtos/               # HTTP functor objects
│   │   └── ports/              # Adjunction interfaces
│   ├── infrastructure/
│   │   ├── database.py         # Session factory, lifecycle
│   │   ├── repositories/       # Free ⊣ Repository
│   │   ├── models/             # Storage functor objects
│   │   └── external/           # Domain ⊣ External
│   └── api/
│       ├── routes/             # HTTP functor application
│       ├── middleware/         # Natural transformations
│       ├── main.py             # App factory
│       └── dependencies.py     # Reader monad (DI)
└── {migration_dir}/            # alembic/ / prisma/ / migrations/
```

---

## Usage

### Full Pipeline

```
User: "Build a system for analyzing customer photos and recommending products"

Phase 0: specifications-architect
├── Extracts domain concepts
├── Synthesizes ADTs
├── Formalizes constraints
├── Defines morphisms with effects + resilience
├── Extracts state machines
├── Detects categorical structure
├── Generates proof obligations
└── Validates → specifications/v1/

Phase 1: standards-architect
├── Defines category standards (Domain, Storage, External, HTTP)
├── Defines security (auth, authz, sanitization)
├── Defines observability (metrics, tracing, logging)
├── Defines caching + transactions
├── Defines configuration + API versioning
└── Validates → standards/

Phase 2: maps-architect
├── Maps primitive types and identifiers
├── Maps Kleisli composition patterns
├── Maps adjunctions (repository, cache)
├── Maps functors (HTTP, storage, external)
├── Maps natural transformations (middleware)
├── Maps monads (IO, Either, Reader, Transaction)
├── Maps module structure (services, repositories, handlers)
└── Validates → maps/

Phase 3: proofs-architect
├── Proves identity laws (id∘f = f = f∘id)
├── Proves composition (associativity)
├── Proves functor laws (preserves id/composition)
├── Proves adjunction laws (triangles)
├── Proves monad laws
├── Proves naturality (squares commute)
├── Generates certificates
└── Validates → proofs/

Phase 4: code-architect
├── Generates domain entities from type maps
├── Generates DTOs from HTTP functor maps
├── Generates repositories from adjunction maps
├── Generates external clients from external maps
├── Generates services from module maps
├── Generates handlers from HTTP maps
├── Generates middleware from transformation maps
├── Generates bootstrap (entry point, config, DI)
└── Validates → generated/{language}/

Phase 5+: infrastructure-architect (future)
```

### Iterative Updates

```
# Add new requirement
→ Re-run domain-extractor
→ Re-run downstream specification skills
→ Re-run affected standards skills
→ Re-run affected map skills
→ Re-prove affected theorems
→ Re-generate affected code
→ Re-validate all layers
```

---

## Categorical Foundation

Each layer implements categorical structures:

| Layer | Objects | Morphisms | Key Structure |
|-------|---------|-----------|---------------|
| Specifications | Types (ADT) | Operations | Products, Coproducts |
| Standards | Categories | Functors | Adjunctions, Monads |
| Maps | Implementations | Transformers | Natural Transformations |
| Proofs | Propositions | Proofs | Curry-Howard |
| Code | Runtime Types | Functions | Kleisli Composition |

---

## Future Phases

- **Phase 5: Infrastructure Layer** - Docker, NATS, Caddy, monitoring, scaling, deployment
