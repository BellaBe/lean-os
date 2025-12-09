---
name: standards-architect
description: |
  Orchestrator for the standards layer. Takes validated specifications and produces 
  universal property definitions, categorical laws, and cross-cutting concerns as 
  reusable standards. Coordinates 8 sub-skills covering categories, security, 
  observability, caching, transactions, configuration, and API versioning.
  Use after specifications-architect completes successfully.
---

# Standards Architect

Entry point for the Standards Layer. Transforms specifications into universal standards that guide code generation.

## Purpose

Orchestrate the complete standards pipeline:
1. Define category standards (domain, storage, external, HTTP)
2. Define security standards (auth, authz, sanitization, isolation)
3. Define observability standards (metrics, tracing, logging)
4. Define caching standards (cache adjunction, invalidation)
5. Define transaction standards (transaction monad, saga)
6. Define configuration standards (config reader, feature flags)
7. Define API versioning standards (versions, deprecation)
8. Validate and gate to maps layer

## Input

Validated specifications from specifications-architect:

```
specifications/v{X}/
├── domain-concepts.yaml
├── requirements.adt
├── constraints.yaml
├── services.spec.yaml
├── state-machines.yaml
├── architecture.categorical
├── types.curry-howard
└── versions.yaml
```

## Output

Complete standards directory:

```
standards/
├── categories/
│   ├── domain.std.yaml         # Domain category laws
│   ├── storage.std.yaml        # Repository adjunction
│   ├── external.std.yaml       # External functor standards
│   └── http.std.yaml           # HTTP category
├── security/
│   ├── authentication.std.yaml # Identity verification
│   ├── authorization.std.yaml  # Permission model
│   ├── sanitization.std.yaml   # Input/output cleaning
│   └── tenant-isolation.std.yaml # Multi-tenancy
├── observability/
│   ├── metrics.std.yaml        # Metric definitions
│   ├── tracing.std.yaml        # Distributed tracing
│   └── logging.std.yaml        # Structured logging
├── caching/
│   ├── cache.std.yaml          # Cache adjunction
│   └── invalidation.std.yaml   # Invalidation strategies
├── transactions/
│   ├── transaction.std.yaml    # Transaction monad
│   └── saga.std.yaml           # Distributed saga
├── configuration/
│   ├── config.std.yaml         # Configuration reader
│   └── feature-flags.std.yaml  # Conditional morphisms
├── api-versioning/
│   ├── versioning.std.yaml     # Version strategy
│   └── deprecation.std.yaml    # Deprecation morphisms
├── versions.yaml               # Standards versioning
└── validation-report.yaml      # Validation results
```

## Pipeline

```
                              STANDARDS ARCHITECT
┌─────────────────────────────────────────────────────────────────────────────┐
│                                                                             │
│  ┌─────────────────────┐                                                    │
│  │   Specifications    │                                                    │
│  │   (from Phase 0)    │                                                    │
│  └──────────┬──────────┘                                                    │
│             │                                                               │
│             ▼                                                               │
│  ┌─────────────────────┐                                                    │
│  │ category-standard-  │                                                    │
│  │     definer         │ ─────────────────────────────────┐                 │
│  └──────────┬──────────┘                                  │                 │
│             │ categories/*.std.yaml                       │                 │
│             │                                             │                 │
│     ┌───────┴───────┬───────────────┬───────────────┐    │                 │
│     │               │               │               │    │                 │
│     ▼               ▼               ▼               ▼    │                 │
│  ┌────────┐  ┌────────────┐  ┌──────────┐  ┌──────────┐  │                 │
│  │security│  │observability│  │ caching  │  │transaction│  │                 │
│  │-definer│  │  -definer   │  │ -definer │  │ -definer  │  │                 │
│  └───┬────┘  └─────┬──────┘  └────┬─────┘  └────┬─────┘  │                 │
│      │             │              │             │        │                 │
│      │             │              │             │        │                 │
│      └─────────────┴──────────────┴─────────────┘        │                 │
│                    │                                     │                 │
│     ┌──────────────┴──────────────┐                      │                 │
│     │                             │                      │                 │
│     ▼                             ▼                      │                 │
│  ┌────────────┐            ┌──────────────┐              │                 │
│  │config-     │            │api-versioning│              │                 │
│  │definer     │            │   -definer   │              │                 │
│  └─────┬──────┘            └──────┬───────┘              │                 │
│        │                          │                      │                 │
│        └──────────────────────────┴──────────────────────┘                 │
│                                   │                                        │
│                                   ▼                                        │
│                    ┌──────────────────────────┐                             │
│                    │   standards-validator    │                             │
│                    └──────────────┬───────────┘                             │
│                                   │                                        │
│                          ┌───────┴────────┐                                │
│                          │                │                                │
│                          ▼                ▼                                │
│                       [PASS]           [FAIL]                              │
│                          │                │                                │
│                          ▼                ▼                                │
│                    Maps Layer        Fix & Retry                           │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Sub-Skills

| Order | Skill | Purpose | Dependencies |
|-------|-------|---------|--------------|
| 1 | category-standard-definer | Define categorical structure | Specifications |
| 2a | security-standard-definer | Security patterns | categories |
| 2b | observability-standard-definer | Observability patterns | categories |
| 2c | caching-standard-definer | Cache adjunction | categories |
| 2d | transaction-standard-definer | Transaction patterns | categories |
| 3a | configuration-standard-definer | Config reader monad | All above |
| 3b | api-versioning-standard-definer | Version management | All above |
| 4 | standards-validator | Validate & gate | All standards |

**Parallel execution:** Steps 2a-2d can run in parallel after step 1.

## Execution Modes

### Mode 1: Full Generation

Generate all standards from specifications:

```yaml
mode: full
specification_version: 1
output_dir: standards/
```

### Mode 2: Incremental Update

Update standards when specifications change:

```yaml
mode: incremental
specification_version: 2
base_standards_version: 1
changes:
  - added: Subscription entity
  - modified: Merchant type
```

### Mode 3: Selective Generation

Generate only specific standard categories:

```yaml
mode: selective
categories:
  - security
  - observability
```

### Mode 4: Validation Only

Re-validate existing standards:

```yaml
mode: validate
standards_version: 1
```

## Orchestration Logic

### Dependency Resolution

```yaml
dependencies:
  category-standard-definer: [specifications]
  security-standard-definer: [category-standard-definer]
  observability-standard-definer: [category-standard-definer]
  caching-standard-definer: [category-standard-definer]
  transaction-standard-definer: [category-standard-definer]
  configuration-standard-definer:
    - security-standard-definer
    - observability-standard-definer
    - caching-standard-definer
    - transaction-standard-definer
  api-versioning-standard-definer:
    - category-standard-definer
  standards-validator:
    - ALL
```

### Change Propagation

```yaml
change_propagation:
  categories/*.std.yaml:
    invalidates:
      - security/*.std.yaml
      - observability/*.std.yaml
      - caching/*.std.yaml
      - transactions/*.std.yaml
      - configuration/*.std.yaml
      - api-versioning/*.std.yaml
    action: re-run from affected skills
    
  security/*.std.yaml:
    invalidates:
      - configuration/*.std.yaml
    action: re-run configuration-standard-definer
```

## Inter-Skill Validation

```yaml
inter_skill_validation:
  strategy: halt_on_error
  
  after_each_skill:
    - name: schema_valid
      check: "Output matches standard schema"
      on_failure: halt
      
    - name: laws_consistent
      check: "Categorical laws don't contradict"
      on_failure: halt
      
    - name: references_resolve
      check: "Category/functor references exist"
      on_failure: halt
      
  on_halt:
    present_to_human:
      context: "Specification inputs + current standards"
      error: "What validation failed"
      suggestions:
        - "Modify specification upstream"
        - "Adjust standard definition"
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
    # Category issues bubble up to specifications
    - from: category-standard-definer
      to: specifications-architect
      triggers:
        - "Missing functor in architecture.categorical"
        - "Adjunction incomplete"
      action:
        notify: true
        suggest_fix: true
        
    # Security issues
    - from: security-standard-definer
      to: category-standard-definer
      triggers:
        - "Auth category missing"
        - "Permission model undefined"
      action:
        notify: true
        suggest_fix: true
        
    # Cross-cutting concerns
    - from: standards-validator
      to: category-standard-definer
      triggers:
        - "Standard contradicts categorical law"
        - "Missing natural transformation"
      action:
        notify: true
        suggest_fix: true
        
  human_escalation:
    trigger: "Cannot auto-resolve after 2 iterations"
    present:
      - error_context
      - affected_standards
      - specification_source
    await: human_decision
```

## Validation Gates

```yaml
validation_gates:
  # Gate 1: After category definitions
  post_categories:
    skill: category-standard-definer
    checks:
      - categories_have_identity
      - functors_preserve_composition
      - adjunctions_have_triangle_identities
    blocking: true
    
  # Gate 2: After security definitions
  post_security:
    skill: security-standard-definer
    checks:
      - auth_flow_complete
      - authz_model_consistent
      - sanitization_covers_inputs
    blocking: true
    
  # Gate 3: After cross-cutting concerns
  post_cross_cutting:
    skills:
      - observability-standard-definer
      - caching-standard-definer
      - transaction-standard-definer
    checks:
      - metrics_cover_morphisms
      - cache_invalidation_defined
      - saga_has_compensation
    blocking: true
    
  # Gate 4: Final validation
  final:
    skill: standards-validator
    checks:
      - all_standards_consistent
      - no_law_violations
      - complete_coverage
    blocking: true
    gate_to: maps_layer
```

## Configuration

```yaml
standards_architect:
  # Execution settings
  parallel_execution: true
  max_iterations: 5
  
  # Output settings
  output_dir: "standards"
  version_strategy: semantic
  
  # Validation settings
  strict_mode: false
  require_all_categories: true
  
  # Sub-skill settings
  skills:
    category-standard-definer:
      include_http: true
      include_external: true
    security-standard-definer:
      require_tenant_isolation: false  # Enable for multi-tenant
    caching-standard-definer:
      default_ttl_ms: 300000
    transaction-standard-definer:
      require_saga: true  # For distributed systems
```

## Categorical Foundation

Standards define universal properties that all implementations must satisfy:

```
Standards: Specifications → UniversalProperties

Where each standard defines:
- Objects: Types in the category
- Morphisms: Operations preserving structure
- Laws: Equations that must hold
- Natural transformations: Systematic conversions
```

### Key Categorical Structures

| Standard | Categorical Structure |
|----------|----------------------|
| Domain | Category with products/coproducts |
| Storage | Adjunction: Free ⊣ Repository |
| External | Functor: Domain → External |
| HTTP | Functor: Domain → HTTP |
| Cache | Adjunction: Forget ⊣ Cache |
| Transaction | Monad: Transaction with bind |
| Config | Monad: Reader[Config, _] |
| Auth | Natural transformation: HTTP ⟹ AuthHTTP |

## Checklist

Before marking standards complete:

- [ ] All categories have identity morphisms
- [ ] All functors preserve composition
- [ ] All adjunctions have unit and counit
- [ ] All monads satisfy laws
- [ ] Security covers auth + authz + sanitization
- [ ] Observability covers metrics + tracing + logging
- [ ] Cache has invalidation strategy
- [ ] Transactions have rollback/compensation
- [ ] Config has environment handling
- [ ] API versioning has migration path
- [ ] All standards reference specification types
- [ ] Validation passes

## Next Phase

On successful validation, hand off to Maps Layer:

```
Standards Architect (complete)
         │
         ▼
┌─────────────────────┐
│   maps-architect    │ ← Next orchestrator
└─────────────────────┘
```
