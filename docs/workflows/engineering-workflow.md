# Engineering Workflow

Engineering in LeanOS operates through a 4-phase categorical verification pipeline: SPEC → BUILD → VERIFY → GEN.

**Reasoning mode:** Causal (enforced) - all engineering threads use 6-stage causal flow.

**Orchestrator:** `.claude/agents/lean-os.md`

---

## LeanOS Flow

```
USER REQUEST
     │
     ▼
┌─────────────────────────────────────────────────────────────┐
│  ORCHESTRATOR (lean-os)                                     │
│  "Build me a system for X"                                  │
└─────────────────────────────────────────────────────────────┘
     │
     ▼
┌─────────────────────────────────────────────────────────────┐
│  PHASE 1: SPEC (lean-os-spec)                               │
│                                                             │
│  Skills:                                                    │
│    1. spec-objects     → spec/objects.yaml                  │
│    2. spec-morphisms   → spec/morphisms.yaml                │
│    3. spec-effects     → spec/effects.yaml                  │
│    4. spec-constraints → spec/constraints.yaml              │
│                                                             │
│  Gate G1:                                                   │
│    ls spec/{objects,morphisms,effects,constraints}.yaml     │
│                                                             │
│  FAIL? → Fix missing files. Do not proceed.                 │
└─────────────────────────────────────────────────────────────┘
     │ PASS
     ▼
┌─────────────────────────────────────────────────────────────┐
│  PHASE 2: BUILD (lean-os-build)                             │
│                                                             │
│  Skills:                                                    │
│    1. build-category        → build/category.yaml           │
│    2. build-effects         → build/effects.yaml            │
│    3. build-functors        → build/functors.yaml           │
│    4. build-transformations → build/transformations.yaml    │
│                                                             │
│  Gate G2-G4:                                                │
│    - All morphisms have domain/codomain from objects        │
│    - All effects have monad structure                       │
│    - All functors preserve composition                      │
│                                                             │
│  FAIL? → Fix build artifacts. Do not proceed.               │
└─────────────────────────────────────────────────────────────┘
     │ PASS
     ▼
┌─────────────────────────────────────────────────────────────┐
│  PHASE 3: VERIFY (lean-os-verify)                           │
│                                                             │
│  Skills:                                                    │
│    1. verify-laws        → verify/laws-report.yaml          │
│    2. verify-constraints → verify/constraints-report.yaml   │
│    3. verify-coverage    → verify/coverage-report.yaml      │
│                                                             │
│  Gate G5-G6:                                                │
│    - Laws pass (Lean or Hypothesis)                         │
│    - 100% morphism coverage                                 │
│                                                             │
│  FAIL? → Fix proofs/coverage. Do not proceed.               │
└─────────────────────────────────────────────────────────────┘
     │ PASS
     ▼
┌─────────────────────────────────────────────────────────────┐
│  PHASE 4: GEN (lean-os-gen)                                 │
│                                                             │
│  Skills (IN ORDER):                                         │
│    1. gen-types      → effects/ FIRST, then types/          │
│    2. gen-maps       → maps/*.map.yaml                      │
│    3. verify-maps    → maps-verification.yaml               │
│       ├─ FAIL? → Fix maps. Do not run gen-code.             │
│       └─ PASS ↓                                             │
│    4. gen-code       → operations/, handlers/               │
│    5. apply-standards→ middleware/                          │
│    6. gen-wiring     → main.py, Dockerfile, docker-compose  │
│                                                             │
│  Gate G7:                                                   │
│    python -c "from src.domain.effects import App"           │
│    python -c "from src.main import create_app"              │
│    docker-compose config                                    │
│                                                             │
│  FAIL? → Fix code. Do not deliver.                          │
└─────────────────────────────────────────────────────────────┘
     │ PASS
     ▼
   DONE → Runnable system in gen/python/
```

---

## Quick Reference

| Phase | Agent | Skills | Output |
|-------|-------|--------|--------|
| SPEC | lean-os-spec | engineering-spec-* | spec/*.yaml |
| BUILD | lean-os-build | engineering-build-* | build/*.yaml |
| VERIFY | lean-os-verify | engineering-verify-* | verify/*.yaml |
| GEN | lean-os-gen | engineering-gen-*, engineering-apply-standards | gen/python/src/ |

---

## Phase 1: SPEC

**Agent:** `.claude/agents/lean-os-spec.md`

**Purpose:** Transform business requirements into categorical specifications.

### Skills

| Skill | Purpose | Output |
|-------|---------|--------|
| `engineering-spec-objects` | Define domain objects (types, entities) | `spec/objects.yaml` |
| `engineering-spec-morphisms` | Define transformations between objects | `spec/morphisms.yaml` |
| `engineering-spec-effects` | Define side effects (IO, DB, API) | `spec/effects.yaml` |
| `engineering-spec-constraints` | Define invariants and business rules | `spec/constraints.yaml` |

### Gate G1

```bash
ls spec/{objects,morphisms,effects,constraints}.yaml
```

All four files must exist before proceeding.

---

## Phase 2: BUILD

**Agent:** `.claude/agents/lean-os-build.md`

**Purpose:** Build categorical structure from specifications.

### Skills

| Skill | Purpose | Output |
|-------|---------|--------|
| `engineering-build-category` | Assemble category from objects/morphisms | `build/category.yaml` |
| `engineering-build-effects` | Build effect system with monad structure | `build/effects.yaml` |
| `engineering-build-functors` | Define functors between categories | `build/functors.yaml` |
| `engineering-build-transformations` | Define natural transformations | `build/transformations.yaml` |

### Gates G2-G4

- **G2:** All morphisms have domain/codomain from objects
- **G3:** All effects have monad structure (unit, bind, laws)
- **G4:** All functors preserve composition

---

## Phase 3: VERIFY

**Agent:** `.claude/agents/lean-os-verify.md`

**Purpose:** Verify categorical laws and coverage.

### Skills

| Skill | Purpose | Output |
|-------|---------|--------|
| `engineering-verify-laws` | Verify category laws (identity, associativity) | `verify/laws-report.yaml` |
| `engineering-verify-constraints` | Verify business rule satisfaction | `verify/constraints-report.yaml` |
| `engineering-verify-coverage` | Ensure 100% morphism coverage | `verify/coverage-report.yaml` |

### Gates G5-G6

- **G5:** Laws pass (Lean proofs or Hypothesis property tests)
- **G6:** 100% morphism coverage (all paths tested)

---

## Phase 4: GEN

**Agent:** `.claude/agents/lean-os-gen.md`

**Purpose:** Generate runnable code from verified specifications.

### Skills (Executed in Order)

| Order | Skill | Purpose | Output |
|-------|-------|---------|--------|
| 1 | `engineering-gen-types` | Generate effect types FIRST, then domain types | `effects/`, `types/` |
| 2 | `engineering-gen-maps` | Generate code structure maps | `maps/*.map.yaml` |
| 3 | `engineering-verify-maps` | Verify maps before code generation | `maps-verification.yaml` |
| 4 | `engineering-gen-code` | Generate operations and handlers | `operations/`, `handlers/` |
| 5 | `engineering-apply-standards` | Apply middleware and cross-cutting concerns | `middleware/` |
| 6 | `engineering-gen-wiring` | Generate entry point and deployment | `main.py`, `Dockerfile`, `docker-compose.yaml` |

### Gate G7

```bash
python -c "from src.domain.effects import App"
python -c "from src.main import create_app"
docker-compose config
```

All three commands must succeed.

---

## Foundation Skills

Two skills establish project structure before the pipeline runs:

| Skill | Purpose | Output |
|-------|---------|--------|
| `engineering-foundation-schema` | Define project schema and conventions | Project structure |
| `engineering-foundation-targets` | Define build targets and dependencies | Build configuration |

---

## Commands

### Start Full Flow

```
"Build a system for [requirements]"
```

### Check Status

```
"What's the status?"
```

### Resume After Failure

```
"Continue" or "Resume from verify"
```

### Force Rebuild

```
"Rebuild from spec"
```

---

## Output Structure

```
gen/python/
├── src/
│   ├── domain/
│   │   ├── types/          # From gen-types
│   │   ├── effects/        # From gen-types (effects first)
│   │   ├── operations/     # From gen-code
│   │   └── handlers/       # From gen-code
│   ├── middleware/         # From apply-standards
│   └── main.py             # From gen-wiring
├── maps/                   # From gen-maps
│   └── *.map.yaml
├── Dockerfile              # From gen-wiring
└── docker-compose.yaml     # From gen-wiring
```

---

## Error Handling

### Phase 1 (SPEC) Failures

- Missing objects → Define all domain entities
- Missing morphisms → Define all transformations
- Missing effects → Identify all side effects
- Missing constraints → Document business rules

### Phase 2 (BUILD) Failures

- Invalid morphisms → Check domain/codomain types
- Invalid effects → Ensure monad laws hold
- Invalid functors → Verify composition preservation

### Phase 3 (VERIFY) Failures

- Laws don't hold → Fix category structure
- Constraints violated → Adjust spec or implementation
- Coverage gaps → Add missing morphism tests

### Phase 4 (GEN) Failures

- Type errors → Fix type definitions
- Map validation fails → Correct map structure
- Import errors → Check wiring dependencies
- Docker fails → Fix deployment config

---

## Relationship to Business Threads

Engineering begins when a business thread spawns an engineering requirement:

```
threads/operations/{feature}/
├── 4-decision.md           # Decision to build
└── 5-actions/
    └── action-spawn-engineering.md
        │
        └── Creates: threads/engineering/{requirement}/
```

The engineering thread uses the LeanOS pipeline to produce verified code.

---

## Related Documentation

- [Causal Flow](causal-flow.md) - 6-stage decision framework
- [Architecture](../reference/architecture.md) - System layers
- [All Skills](../reference/all-skills.md) - Complete skills reference
