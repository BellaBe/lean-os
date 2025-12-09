---
name: infrastructure-prover
description: Generate deployment configurations with topology isomorphism verification. Transforms service specifications into Docker, Kubernetes, and CI/CD configs. Proves deployed topology matches architecture spec. Use when engineering thread requests infrastructure/deployment configuration.
version: 1.0.0
allowed-tools: bash_tool, create_file, view, str_replace
model: claude-sonnet-4-20250514
license: Proprietary - LeanOS Engineering Layer
---

# infrastructure-prover: Deployment Configuration with Topology Proofs

## Purpose

Generate deployment configurations with **topology isomorphism verification** (not composition verification).

**Key insight:** Infrastructure verification is about **topology matching**, not composition laws.

**Process:**
1. Analyze service topology (dependencies, networking)
2. Generate Docker configs (Dockerfiles, docker-compose)
3. Generate Kubernetes manifests (deployments, services, ingress)
4. Generate CI/CD pipelines (GitHub Actions)
5. Prove topology isomorphism (deployed = spec)

---

## Position in Engineering Layer

You are skill #5 of 6:

1. **system-architect** - Requirements → Specifications + Curry-Howard proofs
2. **backend-prover** - Specifications → Maps → Code + Runtime monitors
3. **standardization-layer** - Code → Middleware injection (naturality proofs)
4. **frontend-prover** - OpenAPI → TypeScript + Framework bindings + Type correspondence
5. **infrastructure-prover** (YOU) - Services spec → Deployment configs + Topology isomorphism proof
6. **proof-composer** - Validates entire proof chain

---

## Input Requirements

**From system-architect:**
```
artifacts/engineering/specifications/v{X}/
├── manifest.json                    # Version hash (locked)
└── services.spec.yaml              # Service topology specification
```

**From thread:**
```
threads/engineering/{requirement}/5-actions/action-4-infrastructure.md

Execute infrastructure-prover:
  platform: docker-compose | kubernetes | both
  environment: dev | staging | prod
  resources:
    cpu: 2
    memory: 4Gi
```

---

## Output Guarantees

```
artifacts/engineering/configs/
├── docker/
│   ├── Dockerfile.catalog
│   ├── Dockerfile.billing
│   ├── Dockerfile.auth
│   └── docker-compose.yml
│
├── k8s/
│   ├── catalog-deployment.yaml
│   ├── billing-deployment.yaml
│   ├── auth-deployment.yaml
│   ├── services.yaml
│   └── ingress.yaml
│
└── ci-cd/
    └── .github/workflows/
        ├── build.yml
        ├── test.yml
        └── deploy.yml

artifacts/engineering/proofs/infrastructure/
├── topology/
│   └── deployment-isomorphism.proof
├── resource-allocation/
├── networking/
└── ci-cd-correctness/
```

---

## Why Topology Isomorphism (Not Composition)?

**Backend verification problem:** Composition laws (morphisms compose correctly)
**Frontend verification problem:** Type correspondence (types match API)
**Infrastructure verification problem:** Topology isomorphism (deployed matches spec)

**Reasoning:**
- Service specs already define complete deployment requirements
- Deployment configs directly map to service specs
- No composition to verify (deployment is declarative)
- Goal: Prove deployed topology ≅ architecture topology (isomorphism)

**What we verify:**
- Every service in spec has deployment config
- All dependencies configured
- Network connectivity valid
- Resource constraints sufficient
- No extra services deployed

---

## Orchestration Flow

### Pre-check: Validate Services Spec Exists

```bash
spec_version=$(jq -r '.version' artifacts/engineering/specifications/manifest.json)
spec_hash=$(jq -r '.hash' artifacts/engineering/specifications/manifest.json)

if [ ! -f "artifacts/engineering/specifications/v${spec_version}/services.spec.yaml" ]; then
    echo "ERROR: services.spec.yaml not found. Run system-architect first."
    exit 1
fi

echo "✓ Using services spec from specification v$spec_version (hash: $spec_hash)"
```

---

### Step 1: Analyze Service Topology

**Invoke sub-skill:** `service-topology-analyzer`

**Purpose:** Extract service dependencies and build topology graph

**Input:**
- `artifacts/engineering/specifications/v{X}/services.spec.yaml`

**Output:**
- Internal topology graph (JSON)
- Dependency matrix
- Initialization order
- Network requirements

**What it does:**
- Parses service definitions
- Extracts dependencies (db, cache, message queue, other services)
- Builds dependency graph
- Detects circular dependencies
- Determines initialization order (topological sort)
- Identifies network requirements

---

### Step 2: Generate Docker Configs

**Invoke sub-skill:** `docker-generator`

**Purpose:** Generate Dockerfiles and docker-compose.yml

**Input:**
- Service topology graph (from step 1)
- Resource requirements (from thread)
- Platform config

**Output:**
- `artifacts/engineering/configs/docker/Dockerfile.{service}`
- `artifacts/engineering/configs/docker/docker-compose.yml`

**What it does:**
- Generates Dockerfile per service
- Multi-stage builds (dependencies → build → runtime)
- Configures networking (service mesh)
- Sets resource limits (CPU, memory)
- Defines health checks
- Configures environment variables

---

### Step 3: Generate Kubernetes Manifests

**Invoke sub-skill:** `kubernetes-generator`

**Purpose:** Generate Kubernetes deployment manifests

**Input:**
- Service topology graph (from step 1)
- Resource requirements (from thread)
- Environment (dev/staging/prod)

**Output:**
- `artifacts/engineering/configs/k8s/{service}-deployment.yaml`
- `artifacts/engineering/configs/k8s/services.yaml`
- `artifacts/engineering/configs/k8s/ingress.yaml`
- `artifacts/engineering/configs/k8s/configmaps.yaml`

**What it does:**
- Generates Deployment per service
- Generates Service definitions (ClusterIP, LoadBalancer)
- Generates Ingress rules (routing)
- Configures resource quotas
- Sets up ConfigMaps/Secrets templates
- Configures liveness/readiness probes

---

### Step 4: Generate CI/CD Pipelines

**Invoke sub-skill:** `ci-cd-generator`

**Purpose:** Generate build, test, and deployment pipelines

**Input:**
- Service topology graph (from step 1)
- Deployment platform (docker/k8s)
- Environment configs

**Output:**
- `artifacts/engineering/configs/ci-cd/.github/workflows/build.yml`
- `artifacts/engineering/configs/ci-cd/.github/workflows/test.yml`
- `artifacts/engineering/configs/ci-cd/.github/workflows/deploy.yml`

**What it does:**
- Generates GitHub Actions workflows
- Configures build pipeline (per service)
- Configures test pipeline (unit, integration, e2e)
- Configures deployment pipeline (environment-specific)
- Sets up caching strategies
- Configures secrets management

---

### Step 5: Prove Topology Isomorphism

**Invoke sub-skill:** `topology-prover`

**Purpose:** Verify deployed topology matches architecture spec

**Input:**
- Service topology graph (from step 1)
- Generated configs (from steps 2-4)
- Architecture spec (original)

**Output:**
- `artifacts/engineering/proofs/infrastructure/topology/deployment-isomorphism.proof`

**What it verifies:**
1. **Service existence:** Every service in spec has deployment config
2. **Dependencies configured:** All service dependencies present
3. **Network connectivity:** Services can reach dependencies
4. **Resource constraints:** CPU/memory sufficient
5. **No extra services:** Deployed topology = spec (no additions)
6. **Isomorphism:** Bijection between spec and deployment

**Proof structure:**
```json
{
  "status": "verified",
  "isomorphism": true,
  "services_verified": 15,
  "dependencies_valid": true,
  "network_valid": true,
  "resources_sufficient": true
}
```

---

## Orchestration Summary

**Execution sequence:**

```
1. Validate services.spec.yaml exists (system-architect output)
   ↓
2. Analyze Service Topology
   └─ 5.1: service-topology-analyzer (spec → topology graph)
   ↓
3. Generate Docker Configs
   └─ 5.2: docker-generator (topology → Dockerfiles + compose)
   ↓
4. Generate Kubernetes Manifests (if requested)
   └─ 5.3: kubernetes-generator (topology → K8s manifests)
   ↓
5. Generate CI/CD Pipelines
   └─ 5.4: ci-cd-generator (topology + platform → workflows)
   ↓
6. Prove Topology Isomorphism
   └─ 5.5: topology-prover (spec + configs → proof)
   ↓
7. Output: Complete deployment configs + isomorphism proof
```

---

## Usage Examples

### Example 1: Docker Compose (Dev Environment)

```bash
# Thread action invokes infrastructure-prover
# Input: threads/engineering/catalog-sync/5-actions/action-4-infrastructure.md
#   platform: docker-compose
#   environment: dev
#   resources: {cpu: 2, memory: 4Gi}

# Execution
✓ Services spec loaded (v1.2.0, 15 services)
✓ Topology analyzed (dependency graph valid, no cycles)
✓ Docker configs generated (15 Dockerfiles + compose)
✓ CI/CD pipelines generated (build, test, deploy)
✓ Topology isomorphism verified

# Output
artifacts/engineering/configs/docker/
├── Dockerfile.catalog
├── Dockerfile.billing
├── Dockerfile.auth
└── docker-compose.yml              (15 services configured)

artifacts/engineering/configs/ci-cd/.github/workflows/
├── build.yml
├── test.yml
└── deploy.yml

artifacts/engineering/proofs/infrastructure/topology/
└── deployment-isomorphism.proof    (verified)
```

---

### Example 2: Kubernetes (Production)

```bash
# Thread action
#   platform: kubernetes
#   environment: prod
#   resources: {cpu: 4, memory: 8Gi}

# Execution
✓ Services spec loaded (v1.2.0, 15 services)
✓ Topology analyzed
✓ Kubernetes manifests generated (deployments, services, ingress)
✓ CI/CD pipelines generated (K8s-specific)
✓ Topology isomorphism verified

# Output
artifacts/engineering/configs/k8s/
├── catalog-deployment.yaml
├── billing-deployment.yaml
├── auth-deployment.yaml
├── services.yaml
├── ingress.yaml
└── configmaps.yaml

artifacts/engineering/configs/ci-cd/.github/workflows/
├── build.yml
├── test.yml
└── deploy-prod.yml
```

---

### Example 3: Both Platforms

```bash
# Thread action
#   platform: both
#   environment: [dev, prod]

# Execution
✓ Services spec loaded
✓ Topology analyzed
✓ Docker configs generated (for dev)
✓ Kubernetes manifests generated (for prod)
✓ CI/CD pipelines generated (multi-environment)
✓ Topology isomorphism verified (both platforms)

# Output
artifacts/engineering/configs/
├── docker/                         (dev environment)
├── k8s/                           (prod environment)
└── ci-cd/                         (multi-environment pipelines)
```

---

## Sub-skill Responsibilities

### 5.1: service-topology-analyzer
- Parse services.spec.yaml
- Extract service dependencies
- Build dependency graph
- Validate no circular dependencies
- Determine initialization order (topological sort)
- Identify network requirements
- Output: Topology graph (JSON)

### 5.2: docker-generator
- Generate Dockerfile per service
- Multi-stage builds (deps → build → runtime)
- Generate docker-compose.yml
- Configure networking (service mesh)
- Set resource limits
- Define health checks
- Output: Docker configs

### 5.3: kubernetes-generator
- Generate Deployment manifests
- Generate Service definitions
- Generate Ingress rules
- Configure resource quotas
- Generate ConfigMaps/Secrets templates
- Set up probes (liveness, readiness)
- Output: Kubernetes manifests

### 5.4: ci-cd-generator
- Generate GitHub Actions workflows
- Configure build pipeline
- Configure test pipeline
- Configure deployment pipeline
- Set up environment-specific configs
- Configure secrets management
- Output: CI/CD workflows

### 5.5: topology-prover
- Verify service existence (spec → config)
- Verify dependencies configured
- Verify network connectivity
- Verify resource constraints sufficient
- Verify no extra services
- Prove isomorphism (bijection)
- Output: Topology isomorphism proof

---

## Success Criteria

**Complete when:**
- Services topology analyzed ✓
- Docker configs generated ✓
- Kubernetes manifests generated (if requested) ✓
- CI/CD pipelines generated ✓
- Topology isomorphism verified ✓
- Proof generated ✓

**Topology isomorphism verified means:**
- Every service in spec has deployment config ✓
- All dependencies configured ✓
- Network connectivity valid ✓
- Resource constraints sufficient ✓
- No extra services deployed ✓
- Bijection proven ✓

---

## Error Handling

### Topology Analysis Errors

**Circular dependency:**
```
ERROR: Circular dependency detected
Cycle: CatalogService → BillingService → CatalogService
Action: Remove circular dependency from services.spec.yaml
```

**Missing dependency:**
```
ERROR: Unresolved dependency
Service: CatalogService
Dependency: DatabaseConnection
Action: Add DatabaseConnection to services.spec.yaml or mark as external
```

### Config Generation Errors

**Invalid resource spec:**
```
ERROR: Invalid resource specification
Service: CatalogService
Issue: CPU value must be numeric
Action: Fix resource requirements in thread action
```

**Platform not supported:**
```
ERROR: Unsupported platform 'heroku'
Supported: docker-compose, kubernetes
Action: Choose supported platform
```

### Topology Verification Errors

**Isomorphism failed:**
```
ERROR: Topology isomorphism verification failed
Missing deployment config for service: BillingService
Action: Re-run docker-generator or kubernetes-generator
```

---

## Integration with Build Pipeline

**Build pipeline invokes infrastructure-prover:**

```bash
# build-pipeline/9-generate-infrastructure.sh

# Step 1: Analyze topology
infrastructure-prover analyze-topology

# Step 2: Generate Docker configs
infrastructure-prover generate-docker

# Step 3: Generate Kubernetes manifests (if prod)
if [ "$ENV" == "prod" ]; then
    infrastructure-prover generate-kubernetes
fi

# Step 4: Generate CI/CD pipelines
infrastructure-prover generate-ci-cd

# Step 5: Verify topology isomorphism
infrastructure-prover verify-topology

# Check verification passed
if [ "$(jq -r '.isomorphism' proofs/infrastructure/topology/deployment-isomorphism.proof)" != "true" ]; then
    echo "VERIFICATION FAILED: Topology isomorphism not proven"
    exit 1
fi

echo "✓ Infrastructure generation complete (topology verified)"
```

---

## Critical Reminders

1. **Topology isomorphism ≠ composition verification** - Different verification problem
2. **Services spec is source of truth** - Deployment configs match spec exactly
3. **Resource constraints matter** - CPU/memory must be sufficient
4. **Network connectivity critical** - Services must reach dependencies
5. **No extra services allowed** - Deployed = spec (bijection)

---

## Comparison: Backend vs Frontend vs Infrastructure Verification

| Aspect | Backend | Frontend | Infrastructure |
|--------|---------|----------|----------------|
| **Problem** | Composition verification | Type correspondence | Topology isomorphism |
| **Input** | ADT, composition rules | OpenAPI schema | Services spec |
| **Output** | Services + composition | Types + bindings | Deployment configs |
| **Verification** | Composition laws | Bijection (types) | Bijection (topology) |
| **Method** | Structural analysis | Type mapping | Graph matching |
| **Proof** | Composition correctness | Type isomorphism | Topology isomorphism |
| **Why different?** | Services compose | Data flows through API | Services deploy to infra |

---

## When You (infrastructure-prover) Finish

1. **Log results** in thread:
   ```
   threads/engineering/{requirement}/5-actions/action-4-infrastructure.md
   
   Status: Complete
   Platform: docker-compose, kubernetes
   Environment: dev, prod
   Docker: artifacts/engineering/configs/docker/
   Kubernetes: artifacts/engineering/configs/k8s/
   CI/CD: artifacts/engineering/configs/ci-cd/
   Proof: artifacts/engineering/proofs/infrastructure/topology/
   Verification: PASSED (isomorphism: true)
   Services: 15
   ```

2. **Notify proof-composer** (skill #6):
   - Infrastructure configs ready for final verification
   - All proofs ready for composition

3. **Update engineering thread Stage 5**:
   - Action 4 complete ✓
   - Ready for proof composition (proof-composer)

---

**You are an orchestrator. Coordinate sub-skills, ensure topology matches spec, prove isomorphism.**