# LeanOS Skills Reference

Complete reference of AI skills for business operations.

## Foundation Skills

### foundation-builder
**Purpose:** Orchestrate Canvas population through 5 phases
**Phases:** Discovery → Definition → Validation → Execution → Launch
**Agents:** 10 (7 core, 3 specialist)
**Output:** Complete 15-section Canvas
**Docs:** See [Canvas Setup](../foundation/canvas-setup.md)

---

## Market Research Skills (Mode-Aware)

### market-research-venture
**Purpose:** Venture-focused market analysis
**Mode:** VENTURE only
**Focus:** TAM sizing, growth rates, competitive landscape, scalability
**Output:** research/market/venture-analysis-{date}.md
**Key analyses:**
- Total Addressable Market (TAM/SAM/SOM)
- Market growth rate (CAGR projections)
- Competitive positioning
- Defensibility & moat assessment
- 10x opportunity validation

### market-research-bootstrap
**Purpose:** Bootstrap-focused market analysis
**Mode:** BOOTSTRAP only
**Focus:** Current spend, arbitrage, immediate revenue
**Output:** research/market/bootstrap-analysis-{date}.md
**Key analyses:**
- Who pays what today (spend mapping)
- Budget holder identification
- Pricing intelligence & arbitrage opportunities
- Procurement process analysis
- Q1 revenue potential

**Selection:** Check `strategy/canvas/00-business-model-mode.md` to determine which skill to use.

---

## Sales Skills

### Strategy Skills

**icp-generator**
- Defines target customers per segment
- Input: Canvas 04-segments.md
- Output: research/customer/icp/{segment}-icp.yaml

**sales-narrative**
- Creates messaging per segment
- Input: Canvas + ICP
- Output: threads/sales/narrative/{segment}/

### Execution Skills

**sales-execution** (orchestrator)
- Coordinates sales workflow
- Subskills: 5

**materials-generation**
- Generates segment-specific materials
- Output: Pitch decks, scripts, templates

**prospect-research**
- Finds companies matching ICP
- Uses web_search
- Output: Prospect lists (CSV)

**contact-finding**
- Identifies decision-makers
- Uses LinkedIn, websites
- Output: Contact lists (CSV)

**outreach-sequencing**
- Creates email/phone cadences
- Output: Sequence templates

**qualification-support**
- Prepares for discovery calls
- Output: Call prep docs

---

## Marketing Skills

### Strategy Skills

**marketing-narrative**
- Defines content strategy
- Input: Canvas + Sales narratives
- Output: artifacts/marketing/narrative/

### Execution Skills

**marketing-execution** (orchestrator)
- Coordinates content workflow
- Subskills: 5

**content-strategy**
- Scans threads for opportunities
- Daily automated scan
- Output: Prioritized opportunities

**content-generation**
- Creates educational drafts
- Uses content patterns
- Output: Blog, case studies, guides

**seo-optimization**
- Optimizes for search
- Automated
- Output: SEO-optimized content

**content-distribution**
- Publishes multi-channel
- Adds UTM tracking
- Output: Published content

**performance-tracking**
- Measures impact
- Schedule: Day 7, 30, 90
- Output: Performance reports

---

## Orchestration Skills

### causal-flow
**Purpose:** 6-stage decision framework  
**Stages:** Input → Hypothesis → Implication → Decision → Actions → Learning  
**Thread types:** Business, sales, marketing  
**Key feature:** Stage 6 auto-updates Canvas  
**Docs:** See [Causal Flow](../operations/causal-flow.md)

### ops-dashboard
**Purpose:** Auto-generate daily interface
**Outputs:** today.md, velocity.md, patterns.md, changes.md
**Schedule:** Daily automated
**Status:** Planned (Phase 4)

### business-metrics-tracker
**Purpose:** Generate mode-aware business performance dashboards
**Mode-aware:** VENTURE vs BOOTSTRAP metrics
**Metrics tracked:** Revenue (MRR/ARR), profitability, CAC, LTV, growth, cash flow
**Output:** artifacts/business/metrics.md
**Schedule:** Weekly/monthly/quarterly
**Data sources:** Canvas 13-metrics.md, sales/marketing threads (Stage 6)
**Key distinction:** Business outcomes (not operational efficiency)

---

## Engineering Skills (System Building - Optional)

**Activates when:** Building technical products, microservices, backend systems

**Integration:** Engineering threads use same 6-stage causal flow as business/sales/marketing

**Output location:** `engineering/services/`, `engineering/standards/`, `engineering/domain/`

---

### System Design Skills

**category-theoretic-system-design** (orchestrator)
- **Purpose:** Transform natural language requirements into mathematically correct, production-ready systems
- **Approach:** Category theory for compositional correctness
- **Sub-skills:** 8-skill pipeline
- **Output:** FastAPI/Python microservices with type safety

**Pipeline:**

**adt-analyzer**
- **Purpose:** Parse natural language → algebraic data types (ADTs)
- **Input:** Requirements, domain descriptions
- **Output:** Type definitions, data structures
- **Validation:** Type correctness, completeness

**domain-modeler**
- **Purpose:** Extract domain entities, relationships, bounded contexts
- **Input:** ADTs, business rules
- **Output:** Domain models, entity relationships
- **Artifacts:** `engineering/domain/{domain}-model.md`

**type-validator**
- **Purpose:** Ensure type safety and composition correctness
- **Input:** Domain models, type definitions
- **Output:** Validation reports, type proofs
- **Checks:** Type safety, composition laws, invariants

**functor-mapper**
- **Purpose:** Define data transformations as morphisms (A → B)
- **Input:** Domain models, transformation requirements
- **Output:** Transformation specifications, mappings
- **Validation:** Morphism laws (identity, composition)

**service-compositor**
- **Purpose:** Compose services using category theory principles
- **Input:** Services, transformation specs
- **Output:** Service composition diagrams
- **Validation:** Compositional correctness

**code-generator**
- **Purpose:** Generate production-ready FastAPI/Python code
- **Input:** Service compositions, domain models
- **Output:** Runnable microservice code
- **Artifacts:** `engineering/services/{service}/`
- **Tech stack:** FastAPI, Pydantic, Python type hints

**blueprint-creator**
- **Purpose:** Create service blueprints and architecture docs
- **Input:** Generated code, service specs
- **Output:** OpenAPI specs, architecture diagrams
- **Artifacts:** `engineering/services/{service}/blueprint.yaml`

**correctness-validator**
- **Purpose:** Verify mathematical correctness of entire system
- **Input:** Complete system design
- **Output:** Validation reports, correctness proofs
- **Checks:** Type safety, composition laws, business invariants

---

### Standardization Skills

**standardization-layer** (orchestrator)
- **Purpose:** Apply cross-cutting concerns uniformly to all services
- **Approach:** Natural transformations (category theory)
- **Sub-skills:** 5 concern-specific standardizers
- **Output:** Consistent middleware across microservices

**Standardizers:**

**auth-standardizer**
- **Applies:** JWT authentication, role-based access control (RBAC)
- **Output:** Auth middleware, token validation
- **Artifacts:** `engineering/standards/auth-patterns.md`

**validation-standardizer**
- **Applies:** Input validation, schema enforcement, error responses
- **Output:** Validation middleware, Pydantic schemas
- **Artifacts:** `engineering/standards/validation-patterns.md`

**response-standardizer**
- **Applies:** Uniform response formats, status codes, error handling
- **Output:** Response middleware, standard response models
- **Artifacts:** `engineering/standards/response-formats.md`

**logging-standardizer**
- **Applies:** Structured logging, distributed tracing, observability
- **Output:** Logging middleware, trace correlation
- **Artifacts:** `engineering/standards/logging-patterns.md`

**rate-limit-standardizer**
- **Applies:** Rate limiting, quotas, throttling patterns
- **Output:** Rate limit middleware, quota enforcement
- **Artifacts:** `engineering/standards/rate-limiting.md`

---

### Engineering Workflow

**Complete pipeline:**
1. Requirements (natural language) → **adt-analyzer** → ADTs
2. ADTs → **domain-modeler** → Domain models
3. Domain models → **type-validator** → Validated types
4. Types + transformations → **functor-mapper** → Morphisms
5. Services + morphisms → **service-compositor** → Composition
6. Composition → **code-generator** → FastAPI code
7. Code → **blueprint-creator** → OpenAPI specs
8. System → **correctness-validator** → Validation report
9. Services → **standardization-layer** → Cross-cutting concerns applied

**Typical thread:** `threads/engineering/services/{service-name}/`
- Stage 1: Input (requirements, feature requests)
- Stage 2: Hypothesis (design approach, architectural assumptions)
- Stage 3: Implication (implementation effort, system impact)
- Stage 4: Decision (technical approach, alternatives considered)
- Stage 5: Actions (code generation, testing, deployment)
- Stage 6: Learning (validation results, performance metrics)

**Integration points:**
- **Sales → Engineering:** Pilot requires custom features → Engineering thread
- **Engineering → Marketing:** Product capabilities documented → Technical content
- **Canvas → Engineering:** Solution definition (09-solution.md) drives system design

**Status:** Active - Both skills operational

---

**Note:** Engineering layer is optional. Activate only when building technical products. Business operations (sales, marketing) work independently.

---

For workflow details, see:
- [Sales Workflow](../operations/sales-workflow.md)
- [Marketing Workflow](../operations/marketing-workflow.md)
- [How It Works](../overview/how-it-works.md)