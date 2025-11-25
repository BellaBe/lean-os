# Engineering Workflow

Engineering in LeanOS operates in two phases: Specification (architecture design) and Build Pipeline (code generation with mathematical verification).

## Phase 1: Specification (System Architecture)

### Starting Point: Business Thread

Engineering begins when a business thread spawns an engineering requirement:

```
threads/business/{feature}/
├── 1-input.md              # Business requirement
├── 2-hypothesis.md         # Business hypothesis
├── 3-implication.md        # What this means
├── 4-decision.md           # Decision to build
├── 5-actions/
│   └── action-1-spawn-engineering-thread.md
└── 6-learning.md
```

**Example spawn action:**
```markdown
# Action: Spawn Engineering Thread

## Decision
Build multi-currency backend to support international expansion.

## Engineering Requirements
- Multi-tenant catalog service
- Support Shopify + WooCommerce platforms
- Redis caching for < 50ms p99 latency
- Event-driven architecture

## Spawn Thread
Create: threads/engineering/multi-currency-backend/
```

---

### Step 1: Create Engineering Thread

```
threads/engineering/{requirement}/
├── 1-input.md              # Technical requirements (from business)
├── 2-hypothesis.md         # Technical hypothesis
├── 3-implication.md        # Engineering effort, tech debt
├── 4-decision.md           # Architecture decision
├── 5-actions/              # Populated by skills
│   ├── action-1-architecture.md
│   ├── action-2-backend.md
│   ├── action-3-frontend.md
│   └── action-4-infrastructure.md
└── 6-learning.md
```

**1-input.md structure:**
```markdown
# Input: Multi-Currency Backend

## Business Requirement
From: threads/business/international-expansion/

Support multi-currency transactions for international customers.

## Technical Requirements

### Functional
- Multi-tenant catalog synchronization
- Platform support: Shopify, WooCommerce
- Real-time product sync
- Currency conversion API integration

### Non-Functional
- Latency: < 50ms p99
- Throughput: 10K requests/second
- Availability: 99.9%

### Constraints
- Use existing PostgreSQL + Redis infrastructure
- Event-driven architecture (NATS)
- FastAPI microservices
```

---

### Step 2: Generate Specifications (system-architect)

```
Skill: system-architecture
Input: threads/engineering/{requirement}/1-input.md
Output: artifacts/engineering/specifications/v1/
```

**Executes 9 sub-skills in sequence:**

| Step | Sub-skill | Purpose | Output |
|------|-----------|---------|--------|
| 1.1 | adt-analyzer | Parse requirements into algebraic expressions | requirements.adt |
| 1.2 | algebraic-structure-validator | Validate ADT structure, check impossible paths | validation report |
| 1.3 | functor-generator | Generate functors for patterns | architecture.categorical |
| 1.4 | natural-transformation-engine | Generate version migrations | versions.yaml |
| 1.5 | curry-howard-prover | Generate type signatures with proofs | types.curry-howard |
| 1.6 | system-optimizer | Apply semiring laws, factor common subexpressions | optimized plan |
| 1.7 | architecture-validator | Validate categorical laws, property-based tests | validation report |
| 1.8 | state-machine-validator | Extract and validate state machines | state-machines.yaml |
| 1.9 | version-compatibility-prover | Prove backward compatibility | versions.yaml |

**Output structure:**
```
artifacts/engineering/specifications/v1/
├── requirements.adt
├── types.curry-howard
├── architecture.categorical
├── api.openapi.json
├── services.spec.yaml
├── state-machines.yaml
└── versions.yaml

artifacts/engineering/specifications/manifest.json

artifacts/engineering/proofs/architecture/
├── adt-validation/
├── type-proofs/
├── composition-proofs/
├── functor-laws/
├── natural-transformations/
├── state-machine-proofs/
└── version-compatibility/
```

---

## Phase 2: Build Pipeline

Once specifications exist, execute the build pipeline through 6 phases.

### Phase 0: Generate Shared Standards

```
Skill: standardization-definer
Input: specifications/v1/
Output: shared/ + standardization.yaml
```

**Claude executes:**
- Reads specifications (requirements.adt, architecture.categorical, etc.)
- Analyzes cross-cutting concerns
- Generates shared contract definitions
- Generates standardization configuration

**Output:**
```
shared/
├── api/
│   ├── responses.py
│   ├── middleware.py
│   └── dependencies.py
├── messaging/
│   ├── publisher.py
│   └── listener.py
├── observability/
│   ├── metrics.py
│   └── tracing.py
└── utils/
    ├── exceptions.py
    └── logger.py

specifications/v1/standardization.yaml
```

**Verification checklist:**
- [ ] shared/ directory exists with all contract files
- [ ] standardization.yaml exists and is valid YAML
- [ ] All contracts have proper type annotations

---

### Phase 1: Generate Backend Maps

#### Step 1: Generate Maps

```
Skill: backend-prover / code-map-generator (2.1)
Input: specifications/v1/
Output: artifacts/engineering/maps/backend/
```

**Claude executes:**
- Reads all specification files
- Parses ADT, types, functors, composition rules
- Generates skeletal structure maps (~300 lines)
- Declares all types, classes, functions, methods
- Specifies composition structure
- Declares effects explicitly

**Output:**
```
artifacts/engineering/maps/backend/
├── services/
│   ├── catalog_service.map.yaml
│   ├── billing_service.map.yaml
│   └── ...
├── types.map.yaml
├── composition.map.yaml
├── effects.map.yaml
└── state-machines.map.yaml
```

**Verification checklist:**
- [ ] All expected .map.yaml files exist
- [ ] YAML is valid (can be parsed)
- [ ] Each service map has required fields: service, methods, composition
- [ ] composition.map.yaml references all services

---

#### Step 2: Verify Maps (GATE)

```
Skill: backend-prover / composition-map-validator (2.2)
Input: artifacts/engineering/maps/backend/
Output: artifacts/engineering/proofs/backend/map-validation/
```

**Claude executes:**
- Reads all maps
- Verifies type signatures compose
- Validates composition laws (associativity, identity)
- Checks effect system valid
- Verifies state machines referenced correctly
- Validates dependency graph acyclic
- Checks error handling consistent
- Generates validation report

**Output:**
```
artifacts/engineering/proofs/backend/map-validation/
├── validation-report.json
└── composition-laws.proof
```

**Verification checklist:**
- [ ] validation-report.json exists
- [ ] report.status == "valid"
- [ ] report.ready_for_code_generation == true
- [ ] No errors in report.errors[]

**⚠️ GATE: If validation fails, DO NOT proceed to code generation**
- Fix maps based on error messages
- Re-run Step 2 until valid

---

### Phase 2: Generate Backend Code

#### Step 3: Generate Code from Maps

```
Skill: backend-prover / code-implementation-generator (2.3)
Input: artifacts/engineering/maps/backend/
Output: artifacts/engineering/code/backend/
```

**Claude executes:**
- Reads verified maps
- Reads skeleton configuration
- Generates Python type definitions
- Generates FastAPI service classes
- Generates repositories
- Generates event publishers/listeners
- Generates tests (5000+ lines, mechanical)
- Verifies generated code matches maps structurally

**Output:**
```
artifacts/engineering/code/backend/
├── services/
│   ├── catalog_service.py
│   └── billing_service.py
├── repositories/
├── schemas/
├── db/models.py
├── events/
│   ├── publishers.py
│   └── listeners.py
└── tests/
```

**Verification checklist:**
- [ ] All service files exist
- [ ] Python syntax is valid
- [ ] Type hints present
- [ ] Composition structure matches maps

---

#### Step 4: Generate Runtime Monitors

```
Skill: backend-prover / runtime-monitor-generator (2.4)
Input: proofs + maps + code
Output: artifacts/engineering/code/backend/runtime/
```

**Claude executes:**
- Reads Curry-Howard proofs
- Reads verified maps
- Reads generated code
- Generates runtime type validators
- Creates composition guards
- Generates state machine guards
- Injects observability hooks

**Output:**
```
artifacts/engineering/code/backend/runtime/
├── monitors.py
├── type_validators.py
└── observability.py
```

---

### Phase 3: Apply Standardization

```
Skill: standardization-applier
Input: standardization.yaml + backend code + shared/
Output: modified code + proofs
```

**Claude executes:**
- Reads standardization.yaml configuration
- Reads generated backend code
- Reads shared/ contracts
- Identifies injection points in code
- Generates middleware implementations
- Injects middleware idempotently
- Verifies naturality laws
- Generates property-based tests

**Output:**
```
artifacts/engineering/code/backend/
  (modified with middleware injected)

artifacts/engineering/proofs/backend/standardization/
├── naturality-certificate.proof
├── composition-preservation.proof
└── type-preservation.proof
```

**Verification checklist:**
- [ ] Middleware injection markers present in code
- [ ] naturality-certificate.proof exists
- [ ] certificate.composition_preserved == true
- [ ] Property tests passed (10K examples)

---

### Phase 4: Generate Frontend

```
Skill: frontend-prover
Input: specifications/v1/api.openapi.json
Output: artifacts/engineering/code/frontend/ + proofs
```

**Claude executes:**
- Reads OpenAPI schema
- Parses schema into types
- Generates TypeScript types
- Generates framework-specific bindings (Shopify Remix, React, Vue, vanilla)
- Generates API client
- Proves type correspondence (bijection between backend and frontend types)

**Output:**
```
artifacts/engineering/code/frontend/
├── types/api.ts
├── client/api-client.ts
└── framework/shopify-remix/

artifacts/engineering/proofs/frontend/
└── type-correspondence/
    └── openapi-to-typescript.proof
```

**Verification checklist:**
- [ ] TypeScript types generated
- [ ] Framework bindings exist
- [ ] type-correspondence.proof exists
- [ ] Proof shows bijection between backend and frontend types

---

### Phase 5: Generate Infrastructure

```
Skill: infrastructure-prover
Input: specifications/v1/services.spec.yaml
Output: artifacts/engineering/configs/ + proofs
```

**Claude executes:**
- Reads service specifications
- Analyzes service topology
- Generates Docker configs
- Generates Kubernetes manifests
- Generates CI/CD pipelines
- Proves topology isomorphism (deployed topology matches architecture spec)

**Output:**
```
artifacts/engineering/configs/
├── docker/
│   ├── docker-compose.yml
│   └── Dockerfile.*
├── k8s/
│   ├── *-deployment.yaml
│   └── *-service.yaml
└── ci-cd/
    └── .github/workflows/

artifacts/engineering/proofs/infrastructure/
└── topology/
    └── deployment-isomorphism.proof
```

**Verification checklist:**
- [ ] All deployment manifests exist
- [ ] topology proof exists
- [ ] Proof shows deployed topology == architecture spec

---

### Phase 6: Compose Proofs (DEPLOYMENT GATE)

```
Skill: proof-composer
Input: all proofs from subdirectories
Output: artifacts/engineering/proofs/composed/
```

**Claude executes:**
- Collects all proofs from subdirectories
- Verifies version consistency (manifest hashes)
- Validates proof chain: Architecture → Backend Maps → Backend Code → Standardization → Frontend → Infrastructure
- Checks for gaps (missing proofs)
- Validates composition laws end-to-end
- Generates deployment certificate

**Output:**
```
artifacts/engineering/proofs/composed/
├── system-proof.certificate
├── composition-graph.dot
└── verification-report.md
```

**Verification checklist:**
- [ ] system-proof.certificate exists
- [ ] certificate.status == "valid"
- [ ] certificate.deploy_authorized == true
- [ ] certificate.all_proofs_verified == true
- [ ] certificate.gaps_detected == []

**⚠️ CRITICAL GATE: Do NOT deploy if certificate.deploy_authorized != true**

---

## Complete Flow Summary

```
Phase 0: system-architect
         → specifications/ (ADT, types, architecture, API, state machines)

Phase 1: standardization-definer
         → shared/ contracts + standardization.yaml

Phase 2: backend-prover (maps)
         Step 1: code-map-generator → maps/
         Step 2: composition-map-validator → proofs/ [GATE]

Phase 3: backend-prover (code)
         Step 3: code-implementation-generator → code/backend/
         Step 4: runtime-monitor-generator → code/backend/runtime/

Phase 4: standardization-applier
         Step 5: Apply middleware → modified code/ + proofs/

Phase 5: frontend-prover
         Step 6: Generate frontend → code/frontend/ + proofs/

Phase 6: infrastructure-prover
         Step 7: Generate configs → configs/ + proofs/

Phase 7: proof-composer [DEPLOYMENT GATE]
         Step 8: Compose proofs → certificate

Deploy: If authorized by certificate
```

**Total: 8 steps across 7 phases**

**Two critical gates:**
1. Step 2: Maps must be valid before code generation
2. Step 8: Certificate must authorize deployment

---

## Invocation Examples

### Full Flow Invocation

```
Human: "Execute full LeanOS flow for threads/engineering/multi-currency-backend/"

Claude: [Executes all skills in sequence]
        1. system-architect
        2. standardization-definer
        3. backend-prover (Phase 1 + 2)
        4. standardization-applier
        5. frontend-prover
        6. infrastructure-prover
        7. proof-composer

        Outputs: Complete verified system + certificate
```

### Step-by-Step Invocation

```
Human: "Generate specifications from threads/engineering/multi-currency-backend/"
Claude: [Executes system-architect only]
Human: "Generate backend maps"
Claude: [Executes backend-prover Phase 1 only]
```

And so on for each phase...

---

## Error Handling

**If any step fails:**
1. Human reviews error messages from Claude
2. Human fixes specifications or provides clarification
3. Re-run failed step
4. Continue from where left off

**Common failures:**
- Step 2: Composition laws don't hold → Fix ADT or architecture
- Step 5: Naturality fails → Adjust middleware configuration
- Step 8: Gaps detected → Missing proofs, re-run missing steps

---

## Deployment

Once proof-composer generates a valid certificate with `deploy_authorized: true`, the system is mathematically verified and ready for deployment.

**Human reviews certificate and deploys:**
```bash
# Review certificate
cat artifacts/engineering/proofs/composed/system-proof.certificate

# Deploy to staging
kubectl apply -f artifacts/engineering/configs/k8s/ --namespace=staging

# Deploy to production (after staging validation)
kubectl apply -f artifacts/engineering/configs/k8s/ --namespace=production
```

---

## Engineering Skills Reference

**7 skills with 27 sub-skills** for mathematically verified system generation.

| Skill | Sub-skills | Purpose | Input | Output |
|-------|------------|---------|-------|--------|
| system-architecture | 9 | Transform requirements to specs | 1-input.md | specifications/ |
| standardization-definer | 4 | Extract cross-cutting concerns | specifications/ | maps/shared/ |
| backend-prover | 4 | Two-phase maps → code | specs + shared/ | maps/, code/ |
| standardization-applier | 5 | Apply standards, verify naturality | code/ + shared/ | modified code/ |
| frontend-prover | 4 | Type-safe frontend | api.openapi.json | frontend/ |
| infrastructure-prover | 5 | Deployment with topology proofs | services.spec.yaml | configs/ |
| proof-composer | - | Validate proof chain | all proofs/ | certificate |

### Sub-skill Details

**system-architecture (9):** adt-analyzer, algebraic-structure-validator, functor-generator, natural-transformation-engine, curry-howard-prover, system-optimizer, architecture-validator, state-machine-validator, version-compatibility-prover

**standardization-definer (4):** specification-analyzer, concern-identifier, contract-generator, configuration-generator

**backend-prover (4):** code-map-generator, composition-map-validator, code-implementation-generator, runtime-monitor-generator

**standardization-applier (5):** configuration-parser, injection-point-identifier, middleware-generator, naturality-verifier, property-test-generator

**frontend-prover (4):** openapi-parser, typescript-generator, framework-adapter, type-correspondence-prover

**infrastructure-prover (5):** service-topology-analyzer, docker-generator, kubernetes-generator, ci-cd-generator, topology-prover

---

## Next Steps

- Learn causal flow: [Causal Flow](causal-flow.md)
- See daily routine: [Daily Routine](daily-routine.md)
- Understand sales workflow: [Sales Workflow](sales-workflow.md)
- Understand marketing workflow: [Marketing Workflow](marketing-workflow.md)
