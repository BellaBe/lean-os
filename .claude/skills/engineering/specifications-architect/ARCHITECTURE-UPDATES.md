# Architecture Updates - Addressing Blind Spots

## Summary of Decisions

| Concern | Decision | When |
|---------|----------|------|
| Specification validation | Address when gaps identified | Future |
| Migration | After generation operational, before infra | Future |
| External functor resilience | Review and enhance now | Now |
| Incremental generation | Pattern established, refine later | Future |
| Testing | After full flow complete | Future |
| Skill granularity | Pattern established, apply forward | Ongoing |
| Generator language independence | Address in maps layer | Now |
| Inter-skill validation | Stop and ask human | Now |
| Security category | Add to standards | Now |
| Deployment | With infra layer | Future |
| Observability as objects | Add to standards | Now |
| Config management | Add to standards | Now |
| Caching strategy | Add to standards | Now |
| Transaction boundaries | Add to standards | Now |
| API versioning | Add to standards | Now |
| Domain-specific leakage | Use as examples only | Now |
| DSL format | Formalize | Now |

---

## 1. External Functor Resilience - Enhancement

Current `resilience-specifier` covers:
- ✓ Timeout
- ✓ Retry (exponential, linear, immediate)
- ✓ Circuit breaker
- ✓ Fallback (cached, default, degrade)
- ✓ Bulkhead

**Missing:**
- ❌ Hedged requests (parallel calls, take fastest)
- ❌ Adaptive timeouts (adjust based on latency)
- ❌ Load shedding (drop low-priority under load)
- ❌ Backpressure propagation

**Action:** Enhance resilience-specifier with these patterns.

---

## 2. Standards Layer - New Standards Required

### 2.1 Security Standards

```yaml
# standards/security/
├── authentication.std.yaml    # Identity verification
├── authorization.std.yaml     # Permission checks (RBAC/ABAC)
├── input-sanitization.std.yaml # Input cleaning
├── output-encoding.std.yaml   # Output escaping
├── secrets.std.yaml           # Secret management
└── tenant-isolation.std.yaml  # Multi-tenancy
```

**Categorical interpretation:**
- Authentication: Natural transformation `HTTP → AuthenticatedHTTP`
- Authorization: Morphism guard `Permission × Request → Either[Forbidden, Request]`
- Sanitization: Endofunctor on input types
- Tenant isolation: Slice category per tenant

### 2.2 Observability Standards

```yaml
# standards/observability/
├── metrics.std.yaml      # Metric types as objects
├── tracing.std.yaml      # Distributed tracing
├── logging.std.yaml      # Structured logging
├── alerting.std.yaml     # Alert definitions
└── dashboards.std.yaml   # Dashboard specs
```

**Categorical interpretation:**
- Metrics: Functor `Domain → Metrics` preserving morphism execution
- Tracing: Natural transformation injecting trace context
- Logging: Side effect captured in IO monad

### 2.3 Caching Standards

```yaml
# standards/caching/
├── cache.std.yaml           # Cache adjunction (Forget ⊣ Cache)
├── invalidation.std.yaml    # Invalidation strategies
├── consistency.std.yaml     # Consistency models
└── ttl.std.yaml             # Time-to-live policies
```

**Categorical interpretation:**
- Cache: Adjunction `Forget ⊣ Cache` where:
  - `Forget: CachedDomain → Domain` (strip cache)
  - `Cache: Domain → CachedDomain` (add cache)
  - Unit η: `d → Cache(Forget(d))` (cache lookup)
  - Counit ε: `Forget(Cache(d)) → d` (cache hit)

### 2.4 Transaction Standards

```yaml
# standards/transactions/
├── transaction.std.yaml     # Transaction monad
├── saga.std.yaml            # Distributed saga pattern
├── compensation.std.yaml    # Rollback morphisms
└── isolation.std.yaml       # Isolation levels
```

**Categorical interpretation:**
- Transaction: Monad with `begin`, `commit`, `rollback`
- Saga: Sequence of morphisms with compensation inverses
- Compensation: `f: A → B` has `f⁻¹: B → A` (pseudo-inverse)

### 2.5 Configuration Standards

```yaml
# standards/configuration/
├── config.std.yaml          # Configuration as product type
├── environment.std.yaml     # Environment-specific overrides
├── feature-flags.std.yaml   # Conditional morphisms
├── validation.std.yaml      # Config validation
└── secrets.std.yaml         # Secret injection
```

**Categorical interpretation:**
- Config: Reader monad `Reader[Config, A]`
- Feature flags: Coproduct of enabled/disabled paths
- Environment: Functor `Config[Env] → Config[Resolved]`

### 2.6 API Versioning Standards

```yaml
# standards/api-versioning/
├── versioning.std.yaml      # Version strategies (URL, header)
├── compatibility.std.yaml   # Breaking vs non-breaking
├── deprecation.std.yaml     # Deprecation morphisms
└── migration.std.yaml       # Client migration paths
```

**Categorical interpretation:**
- Versions: Category where objects are API versions
- Migration: Natural transformation `API_v1 ⟹ API_v2`
- Deprecation: Morphism `deprecated → successor`

---

## 3. Generator Language Independence

### Current Issue
Maps layer assumes Python:
- `async/await` in Kleisli interpreter
- `FastAPI` in HTTP functor
- `SQLAlchemy` in repository functor

### Solution

**Abstract intermediate representation:**

```yaml
# maps/categories/domain/morphisms.map.yaml

morphisms:
  - name: create_merchant
    signature: "CreateMerchantInput → IO[Either[Error, Merchant]]"
    
    # Abstract implementation (language-agnostic)
    implementation:
      pattern: kleisli_composition
      steps:
        - validate: "input → Either[ValidationError, ValidInput]"
        - execute: "ValidInput → IO[Either[DbError, Merchant]]"
        - log: "side_effect(logging)"
      
    # Language-specific targets (in separate files)
    targets:
      python:
        file: "generators/python/service.py.jinja"
        runtime: "asyncio"
      typescript:
        file: "generators/typescript/service.ts.jinja"
        runtime: "async/await"
      go:
        file: "generators/go/service.go.jinja"
        runtime: "goroutines"
```

**Generator structure:**

```
generators/
├── abstract/           # Language-agnostic patterns
│   ├── patterns.yaml
│   └── templates/
├── python/             # Python-specific
│   ├── config.yaml
│   └── templates/
├── typescript/         # TypeScript-specific
│   ├── config.yaml
│   └── templates/
└── go/                 # Go-specific
    ├── config.yaml
    └── templates/
```

---

## 4. Inter-Skill Validation

### Strategy: Stop and Ask Human

```yaml
# In each skill orchestrator

inter_skill_validation:
  strategy: halt_on_error
  
  checks:
    - name: output_schema_valid
      action: validate output against schema
      on_failure: halt
      
    - name: references_resolve
      action: check all type/morphism references exist
      on_failure: halt
      
    - name: categorical_laws_satisfiable
      action: quick check laws are consistent
      on_failure: halt
      
  on_halt:
    - log_error: "Validation failed at {skill}: {error}"
    - present_to_human:
        context: "Previous outputs"
        error: "What went wrong"
        suggestions: "Possible fixes"
    - await_human_decision:
        options:
          - retry: "Re-run skill with modifications"
          - skip: "Continue anyway (warning)"
          - abort: "Stop pipeline"
```

---

## 5. Feedback Loops

### Upstream Feedback

When downstream skill detects issue with upstream output:

```yaml
feedback_loops:
  - from: categorical-structure-detector
    to: type-synthesizer
    trigger: "Detected non-composable types"
    action: "Suggest type modifications"
    
  - from: proof-obligation-generator
    to: constraint-specifier
    trigger: "Unprovable constraint"
    action: "Suggest constraint relaxation"
    
  - from: specification-validator
    to: domain-extractor
    trigger: "Missing entity relationships"
    action: "Suggest relationship additions"
```

### Human-in-the-Loop

```
┌─────────────────┐
│   Skill N       │
└────────┬────────┘
         │ output
         ▼
┌─────────────────┐
│   Validation    │
└────────┬────────┘
         │
    ┌────┴────┐
    │         │
  PASS      FAIL
    │         │
    ▼         ▼
┌────────┐ ┌─────────────────┐
│Skill N+1│ │ Present to Human │
└────────┘ └────────┬────────┘
                    │
              ┌─────┴─────┐
              │           │
            FIX        OVERRIDE
              │           │
              ▼           ▼
         Re-run N    Continue with
                     warning
```

---

## 6. DSL Format Definition

### Formalize Specification Formats

```yaml
# specifications/formats/

formats:
  domain-concepts.yaml:
    schema: schemas/domain-concepts.schema.json
    description: "Domain model extraction"
    
  requirements.adt:
    schema: schemas/adt.schema.json
    syntax: |
      Products: Name = Field1 × Field2 × ...
      Coproducts: Name = Variant1 + Variant2 + ...
      Recursive: Name = Base | Recursive(Name)
      Identifiers: Name wraps Primitive
    description: "Algebraic data types"
    
  constraints.yaml:
    schema: schemas/constraints.schema.json
    notation:
      universal: "∀x: Type. P(x)"
      existential: "∃x: Type. P(x)"
      implication: "P → Q"
      conjunction: "P ∧ Q"
      disjunction: "P ∨ Q"
      negation: "¬P"
      dependent_sum: "Σ(x: A). P(x)"
      dependent_product: "Π(x: A). B(x)"
    description: "Formal propositions"
    
  services.spec.yaml:
    schema: schemas/services.schema.json
    description: "Morphism signatures with effects"
    
  state-machines.yaml:
    schema: schemas/state-machines.schema.json
    description: "Finite categories for lifecycles"
    
  architecture.categorical:
    schema: schemas/architecture.schema.json
    description: "Categorical structure"
    
  types.curry-howard:
    schema: schemas/curry-howard.schema.json
    description: "Proof obligations"
```

### Generic Principle

All skills should:
1. Use domain-agnostic terminology in skill definitions
2. Use Glam/Shopify only in examples
3. Accept any domain as input
4. Produce domain-specific output based on input

---

## 7. Updated Layer Architecture

```
┌─────────────────────────────────────────────────────────────────────────────┐
│ LAYER 1: SPECIFICATIONS                                                     │
│                                                                             │
│ specifications-architect (orchestrator)                                     │
│   ├── domain-extractor                                                      │
│   ├── type-synthesizer                                                      │
│   ├── constraint-specifier                                                  │
│   ├── morphism-specifier                                                    │
│   ├── effect-analyzer                                                       │
│   ├── resilience-specifier  ← ENHANCED (hedging, adaptive, backpressure)   │
│   ├── state-machine-extractor                                              │
│   ├── categorical-structure-detector                                        │
│   ├── proof-obligation-generator                                            │
│   └── specification-validator ──► GATE                                      │
└─────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ LAYER 2: STANDARDS                                                          │
│                                                                             │
│ standards-architect (orchestrator)                                          │
│   ├── category-standards/                                                   │
│   │   ├── domain.std.yaml                                                  │
│   │   ├── storage.std.yaml                                                 │
│   │   ├── external.std.yaml                                                │
│   │   └── http.std.yaml                                                    │
│   ├── security-standards/        ← NEW                                     │
│   │   ├── authentication.std.yaml                                          │
│   │   ├── authorization.std.yaml                                           │
│   │   ├── input-sanitization.std.yaml                                      │
│   │   └── tenant-isolation.std.yaml                                        │
│   ├── observability-standards/   ← NEW                                     │
│   │   ├── metrics.std.yaml                                                 │
│   │   ├── tracing.std.yaml                                                 │
│   │   └── logging.std.yaml                                                 │
│   ├── caching-standards/         ← NEW                                     │
│   │   ├── cache.std.yaml                                                   │
│   │   └── invalidation.std.yaml                                            │
│   ├── transaction-standards/     ← NEW                                     │
│   │   ├── transaction.std.yaml                                             │
│   │   └── saga.std.yaml                                                    │
│   ├── configuration-standards/   ← NEW                                     │
│   │   ├── config.std.yaml                                                  │
│   │   └── feature-flags.std.yaml                                           │
│   ├── api-versioning-standards/  ← NEW                                     │
│   │   ├── versioning.std.yaml                                              │
│   │   └── deprecation.std.yaml                                             │
│   └── standards-validator ──► GATE                                         │
└─────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ LAYER 3: MAPS                                                               │
│                                                                             │
│ maps-architect (orchestrator)                                               │
│   ├── primitives-mapper                                                     │
│   ├── kleisli-mapper                                                        │
│   ├── adjunction-mapper                                                     │
│   ├── http-mapper                                                           │
│   ├── limits-mapper                                                         │
│   ├── module-mapper (per module)                                            │
│   └── maps-validator ──► GATE                                              │
│                                                                             │
│ generators/                      ← LANGUAGE-AGNOSTIC                        │
│   ├── abstract/                  # Patterns                                 │
│   ├── python/                    # Python target                            │
│   ├── typescript/                # TypeScript target                        │
│   └── go/                        # Go target                                │
└─────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ LAYER 4: PROOFS                                                             │
│                                                                             │
│ proofs-architect (orchestrator)                                             │
│   ├── proof-composer                                                        │
│   └── proofs-validator ──► GATE (lake build)                               │
└─────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ LAYER 5: GENERATED CODE                                                     │
│                                                                             │
│ code-architect (orchestrator)                                               │
│   ├── primitives-generator                                                  │
│   ├── kleisli-generator                                                     │
│   ├── adjunction-generator                                                  │
│   ├── http-generator                                                        │
│   ├── module-generator (per module)                                         │
│   ├── composition-assembler                                                 │
│   └── code-validator ──► GATE (type check)                                 │
└─────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│ LAYER 6: RUNTIME & INFRASTRUCTURE                                           │
│                                                                             │
│ infrastructure-architect (orchestrator)                                     │
│   ├── runtime-monitor-generator                                             │
│   ├── deployment-generator                                                  │
│   ├── migration-generator        ← ADDED LATER                             │
│   └── infrastructure-validator ──► GATE                                    │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 8. Validation Gates Summary

| Layer | Gate Skill | Checks | Blocking |
|-------|------------|--------|----------|
| Specifications | specification-validator | Completeness, consistency, references | Yes |
| Standards | standards-validator | Laws consistent, no contradictions | Yes |
| Maps | maps-validator | Maps cover all standards | Yes |
| Proofs | proofs-validator | `lake build` passes | Yes |
| Code | code-validator | Type checks, imports resolve | Yes |
| Infrastructure | infrastructure-validator | Configs valid | Yes |

---

## 9. Feedback Loop Implementation

```yaml
# Added to each orchestrator skill

feedback:
  upstream_issues:
    - detect: "Type reference not found"
      notify: type-synthesizer
      suggest: "Add missing type"
      
    - detect: "Morphism composition type mismatch"
      notify: morphism-specifier
      suggest: "Fix domain/codomain"
      
    - detect: "Unprovable constraint"
      notify: constraint-specifier
      suggest: "Relax or split constraint"
      
  human_escalation:
    trigger: "Cannot auto-resolve"
    present:
      - error_context
      - affected_files
      - suggested_fixes
    await: human_decision
    options:
      - fix_and_retry
      - skip_with_warning
      - abort
```
