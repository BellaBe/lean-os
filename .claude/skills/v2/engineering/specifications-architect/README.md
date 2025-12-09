# LeanOS Specification Layer Skills

Phase 0 of the categorical system builder pipeline. These skills transform natural language requirements into validated, mathematically structured specifications.

## Entry Point

**Use `specifications-architect`** - the orchestrator skill that coordinates all sub-skills automatically.

```
User: "Build a photo analysis system for Shopify merchants"
         │
         ▼
   specifications-architect (orchestrator)
         │
         ├── domain-extractor
         ├── type-synthesizer
         ├── constraint-specifier
         ├── morphism-specifier
         ├── effect-analyzer
         ├── resilience-specifier
         ├── state-machine-extractor
         ├── categorical-structure-detector
         ├── proof-obligation-generator
         └── specification-validator
         │
         ▼
   artifacts/engineering/v1/specifications/ (complete, validated)
```

Individual sub-skills can be invoked directly for targeted updates.

## Pipeline Overview

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         SPECIFICATION LAYER (Phase 0)                        │
│                                                                              │
│  Requirements ─► domain-extractor ─► type-synthesizer ─► constraint-specifier│
│       │                │                                        │           │
│       │                ▼                                        │           │
│       │         morphism-specifier                              │           │
│       │                │                                        │           │
│       │                ▼                                        │           │
│       │         effect-analyzer                                 │           │
│       │                │                                        │           │
│       │                ▼                                        │           │
│       │         resilience-specifier ──────────────────────────►│           │
│       │                                                         │           │
│       └────────► state-machine-extractor ◄──────────────────────┘           │
│                          │                                                   │
│                          ▼                                                   │
│                categorical-structure-detector                                │
│                          │                                                   │
│                          ▼                                                   │
│                proof-obligation-generator                                    │
│                          │                                                   │
│                          ▼                                                   │
│                specification-validator ─────► GATE TO STANDARDS LAYER       │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Skills

### 0. specifications-architect (Orchestrator)
**Entry point** - Coordinates all specification sub-skills.

| Aspect | Value |
|--------|-------|
| Input | Natural language requirements |
| Output | Complete `artifacts/engineering/v{X}/specifications/` directory |
| Modes | full, incremental, analyze, validate |
| Gate | Validates before proceeding to Standards Layer |

### 1. domain-extractor
Extracts structured domain concepts from natural language.

| Aspect | Value |
|--------|-------|
| Input | Natural language requirements |
| Output | `artifacts/engineering/v{X}/specifications/domain-concepts.yaml` |
| Extracts | Entities, value objects, aggregates, relationships, operations, external deps, business rules |

### 2. type-synthesizer
Converts domain concepts into algebraic data types.

| Aspect | Value |
|--------|-------|
| Input | `domain-concepts.yaml` |
| Output | `artifacts/engineering/v{X}/specifications/requirements.adt` |
| Produces | Products (×), coproducts (+), recursive types, identifiers, primitives |

### 3. constraint-specifier
Formalizes business rules as logical propositions.

| Aspect | Value |
|--------|-------|
| Input | `domain-concepts.yaml`, `requirements.adt` |
| Output | `artifacts/engineering/v{X}/specifications/constraints.yaml` |
| Captures | Invariants, pre-conditions, post-conditions, refinement types |

### 4. morphism-specifier
Defines operations as typed morphism signatures.

| Aspect | Value |
|--------|-------|
| Input | `domain-concepts.yaml`, `requirements.adt` |
| Output | `artifacts/engineering/v{X}/specifications/services.spec.yaml` (base) |
| Defines | Domain, codomain, properties (total, deterministic, idempotent), compositions |

### 5. effect-analyzer
Tags morphisms with effect types for Kleisli categories.

| Aspect | Value |
|--------|-------|
| Input | `services.spec.yaml`, `domain-concepts.yaml` |
| Output | `artifacts/engineering/v{X}/specifications/services.spec.yaml` (enriched) |
| Adds | IO, Either effects, error types, Kleisli category classification |

### 6. resilience-specifier
Adds fault tolerance patterns to IO morphisms.

| Aspect | Value |
|--------|-------|
| Input | `services.spec.yaml` |
| Output | `artifacts/engineering/v{X}/specifications/services.spec.yaml` (resilient) |
| Adds | Timeout, retry, circuit breaker, fallback, bulkhead |

### 7. state-machine-extractor
Extracts lifecycle state machines as finite categories.

| Aspect | Value |
|--------|-------|
| Input | `domain-concepts.yaml`, `requirements.adt`, `services.spec.yaml` |
| Output | `artifacts/engineering/v{X}/specifications/state-machines.yaml` |
| Produces | States, transitions, guards, actions, categorical structure |

### 8. categorical-structure-detector
Identifies mathematical structures from specifications.

| Aspect | Value |
|--------|-------|
| Input | All specification files |
| Output | `artifacts/engineering/v{X}/specifications/architecture.categorical` |
| Detects | Categories, functors, adjunctions, natural transformations, monads, limits/colimits |

### 9. proof-obligation-generator
Generates type-level proof obligations via Curry-Howard.

| Aspect | Value |
|--------|-------|
| Input | `constraints.yaml`, `architecture.categorical`, `requirements.adt` |
| Output | `artifacts/engineering/v{X}/specifications/types.curry-howard` |
| Creates | Dependent types, categorical laws, inhabitedness proofs, Lean 4 signatures |

### 10. specification-validator
**Gate skill** - Validates completeness and consistency.

| Aspect | Value |
|--------|-------|
| Input | All specification files |
| Output | `artifacts/engineering/v{X}/specifications/versions.yaml`, `validation-report.yaml` |
| Checks | Completeness, consistency, references, categorical laws, proof coverage |
| Gate | Must pass to proceed to Standards Layer |

## Output Files

After running all skills, `artifacts/engineering/v{X}/specifications/` contains:

```
artifacts/engineering/v{X}/specifications/
├── domain-concepts.yaml      # From domain-extractor
├── requirements.adt          # From type-synthesizer
├── constraints.yaml          # From constraint-specifier
├── services.spec.yaml        # From morphism/effect/resilience
├── state-machines.yaml       # From state-machine-extractor
├── architecture.categorical  # From categorical-structure-detector
├── types.curry-howard        # From proof-obligation-generator
├── versions.yaml             # From specification-validator
└── validation-report.yaml    # From specification-validator
```

## Usage

### Primary: Use Specifications Architect

```
User: "Build a system for analyzing customer photos and recommending products"

Specifications Architect handles everything:
1. Extracts domain concepts (Merchant, Profile, Analysis, Recommendation)
2. Synthesizes ADTs
3. Formalizes constraints
4. Defines morphisms with effects
5. Adds resilience patterns
6. Extracts state machines
7. Detects categorical structure
8. Generates proof obligations
9. Validates and gates

Output: artifacts/engineering/v1/specifications/ (complete)
```

### Alternative: Direct Sub-Skill Invocation

For targeted updates or debugging:

```
User: "Build a system for analyzing customer photos and recommending products"

1. Run domain-extractor → identifies Merchant, Profile, Analysis, Recommendation
2. Run type-synthesizer → creates ADTs for each entity
3. Run constraint-specifier → formalizes "analysis requires photo"
4. Run morphism-specifier → defines analyze_photo, generate_recommendations
5. Run effect-analyzer → tags with IO[Either[E, A]]
6. Run resilience-specifier → adds AI service circuit breaker
7. Run state-machine-extractor → extracts AnalysisLifecycle
8. Run categorical-structure-detector → identifies Free ⊣ Repository adjunction
9. Run proof-obligation-generator → creates Lean 4 proof requirements
10. Run specification-validator → validates and gates to next phase
```

### Iterative Refinement

Skills can be re-run when upstream changes:

```
# User adds new requirement
→ Re-run domain-extractor
→ Re-run downstream skills
→ Re-validate
```

## Next Phase

On successful validation, specifications feed into:

- **standardization-definer** → extracts universal properties
- **map generators** → create implementation strategies
- **proof-composer** → generates Lean 4 proofs

## Categorical Foundation

These skills implement the specification layer of a 6-layer architecture:

1. **Specifications** (this layer) - Business intent as mathematical structures
2. **Standards** - Universal properties and laws
3. **Maps** - Implementation strategies
4. **Proofs** - Lean 4 verification
5. **Generated Code** - Executable implementations
6. **Runtime** - Production monitoring

Each specification file has categorical interpretation:
- `requirements.adt` → Objects in Domain category
- `services.spec.yaml` → Morphisms in Kleisli categories
- `architecture.categorical` → Category/functor/adjunction structure
- `types.curry-howard` → Proof obligations via Curry-Howard
