# LeanOS Skills v2

Compositional system builder. 12 levels from primitives to deployed system.

## Architecture

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         SPECIFICATIONS (Input)                              │
│                    Natural language requirements                            │
└────────────────────────────────┬────────────────────────────────────────────┘
                                 │
                                 ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ Level 0: PRIMITIVES                                                         │
│   Base types, identifiers, effects, constraints                             │
│   Output: level-0.manifest.yaml                                             │
└────────────────────────────────┬────────────────────────────────────────────┘
                                 │ compose
                                 ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ Level 1: ENTITIES                                                           │
│   Product types from primitives                                             │
│   Output: level-1.manifest.yaml                                             │
└────────────────────────────────┬────────────────────────────────────────────┘
                                 │ typed by
                                 ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ Level 2: MORPHISMS                                                          │
│   Arrows between entities with effects                                      │
│   Output: level-2.manifest.yaml                                             │
└────────────────────────────────┬────────────────────────────────────────────┘
                                 │ grouped into
                                 ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ Level 3: MODULES                                                            │
│   Coherent operation groups                                                 │
│   Output: level-3.manifest.yaml                                             │
└────────────────────────────────┬────────────────────────────────────────────┘
                                 │ form
                                 ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ Level 4: CATEGORIES AND MONADS                                              │
│   Objects + morphisms + laws + monads + Kleisli                             │
│   Output: level-4.manifest.yaml                                             │
└────────────────────────────────┬────────────────────────────────────────────┘
                                 │ mapped by
                                 ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ Level 5: FUNCTORS                                                           │
│   Structure-preserving maps                                                 │
│   Output: level-5.manifest.yaml                                             │
└────────────────────────────────┬────────────────────────────────────────────┘
                                 │ paired into
                                 ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ Level 6: ADJUNCTIONS                                                        │
│   Optimal translations (L ⊣ R)                                              │
│   Output: level-6.manifest.yaml                                             │
└────────────────────────────────┬────────────────────────────────────────────┘
                                 │ connected by
                                 ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ Level 7: TRANSFORMATIONS                                                    │
│   Natural transformations (middleware)                                      │
│   Output: level-7.manifest.yaml                                             │
└────────────────────────────────┬────────────────────────────────────────────┘
                                 │ verified by
                                 ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ Level 8: PROOFS                                                             │
│   Lean 4 verification of all laws                                           │
│   Output: level-8.manifest.yaml + certificates                              │
└────────────────────────────────┬────────────────────────────────────────────┘
                                 │ generates
                                 ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ Level 9: CODE                                                               │
│   Executable implementations                                                │
│   Output: level-9.manifest.yaml + generated code                            │
└────────────────────────────────┬────────────────────────────────────────────┘
                                 │ wired by
                                 ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ Level 10: BOOTSTRAP                                                         │
│   Entry point, DI, lifecycle                                                │
│   Output: level-10.manifest.yaml + bootstrap code                           │
└────────────────────────────────┬────────────────────────────────────────────┘
                                 │ deployed by
                                 ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ Level 11: INFRASTRUCTURE                                                    │
│   Containers, orchestration, monitoring                                     │
│   Output: level-11.manifest.yaml + infra code                               │
└────────────────────────────────┬────────────────────────────────────────────┘
                                 │
                                 ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                         DEPLOYED SYSTEM (Output)                            │
│                    Running, verified, traceable                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Core Principles

### 1. Complete Enumeration

Every level MUST process ALL items from its input.

```
|Level N output| == |Level N-1 input items that produce output|
```

No gaps. No missing items. 100% coverage.

### 2. Manifest Flow

Each level produces a manifest that is the source of truth.

```yaml
level-N.manifest.yaml:
  items: [all items at this level]
  traces: [references to Level N-1 items]
  counts: [verified counts]
  validation: [completeness proof]
```

### 3. Trace to Source

Every item traces back to its origins.

```
Level 9 code item 
  → traces to Level 1 entity 
  → traces to Level 0 primitives
```

Full lineage from deployed code to requirements.

### 4. Validation Gates

Each level validates before allowing next level.

```yaml
validation:
  completeness: |output| == |expected|
  traces_valid: all references exist
  laws_verified: categorical laws hold (where applicable)
```

Pipeline halts on validation failure.

### 5. Functor Preservation

Each level's manifest + traces defines a **free category on the dependency graph**:

```yaml
Level as Category:
  Objects:     Items in level-N.manifest.yaml
  Morphisms:   Trace/dependency edges (x → y if y.traces includes x)
  Identity:    id_x for each item x
  Composition: Path composition (if x → y → z, then x → z exists)
```

Generation is a functor F: C_N → C_{N+1}:

```
F(id_x) = id_{F(x)}           # Identity preserved
F(g ∘ f) = F(g) ∘ F(f)        # Composition preserved
```

Enforced by:
- `traces_valid` → edges preserved
- `completeness` → objects preserved
- `dependency lifting` → if N has x → y, then N+1 has F(x) → F(y)

This makes "system generation is functorial" a precise mathematical claim,
not just marketing language.

## Skills

| Level | Skill | Input | Output |
|-------|-------|-------|--------|
| - | manifest-schema | - | Schema definition |
| - | shared-modules | - | Cross-cutting constructs |
| - | **system-orchestrator** | specifications OR requirements | **Complete system (L0-L11)** |
| 0 | level-0-primitives | specifications | level-0.manifest.yaml |
| 1 | level-1-entities | level-0 | level-1.manifest.yaml |
| 2 | level-2-morphisms | level-1 | level-2.manifest.yaml |
| 3 | level-3-modules | level-2 | level-3.manifest.yaml |
| 4 | level-4-categories | level-1,2,3 + level-0.effects | level-4.manifest.yaml (categories + monads) |
| 5 | level-5-functors | level-4 | level-5.manifest.yaml |
| 6 | level-6-adjunctions | level-5 | level-6.manifest.yaml |
| 7 | level-7-transformations | level-5,6 | level-7.manifest.yaml |
| 8 | level-8-proofs | level-4,5,6,7 | level-8.manifest.yaml + proofs |
| 9 | level-9-code | level-0..8 | level-9.manifest.yaml + code |
| 10 | level-10-bootstrap | level-9 | level-10.manifest.yaml + bootstrap |
| 11 | level-11-infrastructure | level-10 | level-11.manifest.yaml + infra |

## Usage

### Full Pipeline

```
User: "Build a system for [requirements]"

Claude executes:
  1. Extract specifications from requirements
  2. Level 0: Extract primitives
  3. Level 1: Generate entities (validate: count matches spec)
  4. Level 2: Generate morphisms (validate: count matches spec)
  5. Level 3: Generate modules (validate: all morphisms covered)
  6. Level 4: Define categories (validate: laws stated)
  7. Level 5: Define functors (validate: complete mappings)
  8. Level 6: Define adjunctions (validate: unit/counit defined)
  9. Level 7: Define transformations (validate: naturality stated)
  10. Level 8: Generate proofs (validate: all obligations discharged)
  11. Level 9: Generate code (validate: all items have artifacts)
  12. Level 10: Generate bootstrap (validate: all wired)
  13. Level 11: Generate infrastructure (validate: deployable)
```

### Incremental Update

```
User: "Add new entity X"

Claude executes:
  1. Add to Level 1 (entity)
  2. Add identifier to Level 0 (primitive)
  3. Add morphisms to Level 2
  4. Add to module in Level 3
  5. Update category in Level 4
  6. Update functors in Level 5
  7. Update adjunctions in Level 6
  8. Update transformations in Level 7
  9. Add proofs in Level 8
  10. Generate code in Level 9
  11. Update bootstrap in Level 10
  12. Update infrastructure in Level 11
  
  Validate at each level before proceeding.
```

### Validation Query

```
User: "Verify the system is complete"

Claude checks:
  ∀ level N:
    |manifest.items| == |expected from spec|
    all traces valid
    all proofs verified
    all code generated
    
  Report any gaps.
```

## Categorical Foundation

| Level | Objects | Morphisms | Structure |
|-------|---------|-----------|-----------|
| 0 | Types | - | Signature (syntax only) |
| 1 | Entities | - | Products |
| 2 | Entities | Operations | Typed arrows (Kleisli) |
| 3 | Modules | - | Groupings |
| 4 | Objects | Arrows + Kleisli | Categories + Monads |
| 5 | Categories | Functors | Func(C,D) |
| 6 | Functors | Adjunctions | L ⊣ R |
| 7 | Functors | Nat Trans | F ⟹ G |
| 8 | Propositions | Proofs | Curry-Howard |
| 9 | Types | Functions | Executable |
| 10 | Components | Wiring | DI |
| 11 | Containers | Deployment | Operations |

## Why Monads Matter

Most Level 2 morphisms are NOT `A → B`. They are `A → M[B]`:

```
get_customer: CustomerId → IO[Either[Error, Customer]]
                           ^^^^^^^^^^^^^^^^^^^^^^^^
                           This is the App monad!
```

Without explicit monad structure:
- Code generators don't know HOW to compose services
- Service chains fail to type-check
- Error handling is ad-hoc

With explicit monad structure:
- Kleisli composition (`>=>`) is well-defined
- Service chains compose associatively (proven in Level 8)
- Error propagation is automatic

## Shared Modules

Items used by 2+ modules get `scope: shared`:

```yaml
# Detected automatically from usage patterns
- id: "entity.shared.Pagination"
  scope: "shared"
  used_by:
    - {ref: "customers.list", module: "customers"}
    - {ref: "orders.list", module: "orders"}
```

**What's shared:**

| Level | Shared Items |
|-------|--------------|
| 0 | All primitives (universal) |
| 1 | Pagination, AuditInfo, AppError |
| 2 | validate_email, paginate, map_error |
| 3 | IRepository[E], ICRUDService[E] |
| 4 | App monad (stacked effect type) |
| 7 | All middleware (Auth, Logging, etc.) |

**Code location:**
```
generated/python/src/project/
├── shared/          # scope: shared
│   ├── types/
│   ├── errors/
│   ├── validation/
│   ├── interfaces/
│   └── middleware/
└── modules/         # scope: module
    ├── customers/
    └── orders/
```

**Generics:**
```yaml
# Type parameters for polymorphic shared items
- id: "entity.shared.PaginatedResult"
  type_params:
    - {name: "A"}  # Generic over item type
  definition:
    fields:
      - {name: "items", type: "List[A]"}
```

## Comparison with v1

| Aspect | v1 (48 skills) | v2 (12 skills) |
|--------|----------------|----------------|
| Structure | Phases (5) | Levels (12) |
| Execution | Template-driven | Manifest-driven |
| Validation | Syntax only | Completeness + coverage |
| Traceability | None | Full lineage |
| Coverage guarantee | No | Yes (100%) |
| Domain-specific | Yes (hardcoded) | No (universal) |

## Files

```
skills/v2/
├── README.md                       # This file
├── manifest-schema/SKILL.md        # Universal manifest schema
├── shared-modules/SKILL.md         # Cross-cutting constructs
├── level-0-primitives/SKILL.md     # Primitives
├── level-1-entities/SKILL.md       # Entities
├── level-2-morphisms/SKILL.md      # Morphisms
├── level-3-modules/SKILL.md        # Modules
├── level-4-categories/SKILL.md     # Categories + Monads
├── level-5-functors/SKILL.md       # Functors
├── level-6-adjunctions/SKILL.md    # Adjunctions
├── level-7-transformations/SKILL.md # Natural transformations
├── level-8-proofs/SKILL.md         # Proofs
├── level-9-code/SKILL.md           # Code generation
├── level-10-bootstrap/SKILL.md     # Bootstrap
└── level-11-infrastructure/SKILL.md # Infrastructure
```

## Guarantees

1. **Completeness**: Every specified item produces output
2. **Traceability**: Every output traces to its source
3. **Verification**: Categorical laws are formally proven
4. **Consistency**: Manifests form coherent chain
5. **Deployability**: End result is runnable system

## Next Steps

1. Test with a real specification
2. Verify 100% coverage achieved
3. Refine templates based on actual generation
4. Add language-specific template libraries
5. Integrate with existing tools (Docker, K8s, etc.)
