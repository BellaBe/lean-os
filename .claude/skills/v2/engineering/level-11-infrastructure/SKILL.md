---
name: level-11-infrastructure
description: |
  Level 11: Infrastructure. Deployment configuration, containers, orchestration,
  monitoring, and operational concerns.
  
  Input: level-10.manifest.yaml (runnable application)
  Output: level-11.manifest.yaml + infrastructure code
  
  UNIVERSAL: Works for any domain. Multi-platform support.
---

# Level 11: Infrastructure

Deployment and operational infrastructure.

## CRITICAL: Generate Actual Files

**Level 11 produces ACTUAL INFRASTRUCTURE FILES, not manifest descriptions.**

```yaml
output_distinction:
  manifest_file:
    path: "level-11.manifest.yaml"
    contains: "References to generated files, NOT file contents"
    
  actual_files_required:
    - "infrastructure/Dockerfile"
    - "infrastructure/docker-compose.yaml"
    - "infrastructure/.env.example"
    - "infrastructure/scripts/start.sh"
    - "infrastructure/scripts/healthcheck.sh"
    
  action: |
    USE FILE CREATION TOOL to create actual files:
      create_file("infrastructure/Dockerfile", dockerfile_content)
      create_file("infrastructure/docker-compose.yaml", compose_content)
      
    DO NOT just describe what files would contain in YAML manifest
    
  validation: |
    After L11 execution:
      ls infrastructure/Dockerfile           # Must exist
      ls infrastructure/docker-compose.yaml  # Must exist
      docker-compose -f infrastructure/docker-compose.yaml config  # Must validate
      docker build -f infrastructure/Dockerfile .  # Must build
```

## Principle

Infrastructure is a functor from Application → Deployed System.

```
Infrastructure: App → Cloud

Maps:
  Application → Container(s)
  Configuration → Secrets + ConfigMaps
  Database → Managed/Containerized DB
  Lifecycle → Health checks + Probes
  Middleware → Load balancer + Ingress
```

## Components

```yaml
infrastructure_components:
  containers:
    description: "Docker/OCI container images"
    includes:
      - application: "Main service container"
      - database: "Database container (dev)"
      - cache: "Cache container (if needed)"
      - migrations: "Database migration job"
      
  orchestration:
    description: "Container orchestration"
    options:
      - docker_compose: "Development/simple deployment"
      - kubernetes: "Production orchestration"
      
  networking:
    description: "Network configuration"
    includes:
      - load_balancer: "Traffic distribution"
      - ingress: "External access"
      - service_mesh: "Internal communication"
      
  messaging:
    description: "Event/message infrastructure"
    options:
      - nats: "Lightweight messaging"
      - kafka: "Enterprise streaming"
      - rabbitmq: "Traditional messaging"
      
  observability:
    description: "Monitoring and debugging"
    includes:
      - metrics: "Prometheus + Grafana"
      - tracing: "Jaeger / Tempo"
      - logging: "Loki / ELK"
      
  secrets:
    description: "Secret management"
    options:
      - env_files: "Simple .env"
      - vault: "HashiCorp Vault"
      - cloud_secrets: "Cloud-native secrets"
```

## Process

```yaml
process:
  step_1_load_inputs:
    inputs:
      - "level-10.manifest.yaml"
      - "specifications/infrastructure.yaml"  # Infra requirements
    action: "Load application and infrastructure specs"
    
  step_2_determine_topology:
    action: "Determine deployment topology"
    considerations:
      - single_container: "Monolithic deployment"
      - multi_container: "Service + DB + Cache"
      - microservices: "Multiple services"
      
  step_3_generate_containers:
    action: "Generate Dockerfile(s)"
    for_each: "container in topology"
    includes:
      - base_image
      - dependencies
      - application_code
      - entrypoint
      - health_check
      
  step_4_generate_compose:
    action: "Generate docker-compose.yaml"
    includes:
      - services
      - networks
      - volumes
      - environment
      
  step_5_generate_orchestration:
    action: "Generate Kubernetes manifests (if needed)"
    includes:
      - deployments
      - services
      - configmaps
      - secrets
      - ingress
      
  step_6_generate_observability:
    action: "Generate monitoring configuration"
    includes:
      - prometheus_config
      - grafana_dashboards
      - alerting_rules
      
  step_7_generate_scripts:
    action: "Generate operational scripts"
    includes:
      - deploy.sh
      - rollback.sh
      - scale.sh
      - backup.sh
      
  step_8_validate:
    action: "Validate infrastructure"
    checks:
      - containers_build
      - compose_valid
      - k8s_valid (if applicable)
      - networking_correct
      
  step_9_produce_manifest:
    action: "Write level-11.manifest.yaml"
```

## Output Structure

```
infrastructure/
├── docker/
│   ├── Dockerfile              # Application image
│   ├── Dockerfile.dev          # Development image
│   └── .dockerignore
├── compose/
│   ├── docker-compose.yaml     # Base compose
│   ├── docker-compose.dev.yaml # Development overrides
│   └── docker-compose.prod.yaml# Production overrides
├── kubernetes/                  # (if needed)
│   ├── base/
│   │   ├── deployment.yaml
│   │   ├── service.yaml
│   │   └── configmap.yaml
│   └── overlays/
│       ├── dev/
│       └── prod/
├── monitoring/
│   ├── prometheus/
│   │   └── prometheus.yml
│   ├── grafana/
│   │   └── dashboards/
│   └── alertmanager/
│       └── alertmanager.yml
├── scripts/
│   ├── deploy.sh
│   ├── rollback.sh
│   └── health-check.sh
└── terraform/                   # (if cloud-native)
    ├── main.tf
    ├── variables.tf
    └── outputs.tf
```

## Dockerfile Template

```dockerfile
# Generated from level-11 infrastructure
# Traces: level-10.manifest.yaml

# Build stage
FROM python:3.11-slim as builder
WORKDIR /app
COPY pyproject.toml poetry.lock ./
RUN pip install poetry && poetry export -f requirements.txt > requirements.txt

# Runtime stage
FROM python:3.11-slim
WORKDIR /app

# Install dependencies
COPY --from=builder /app/requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# Copy application
COPY src/ ./src/

# Health check
HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
    CMD curl -f http://localhost:8000/health || exit 1

# Entry point
ENTRYPOINT ["python", "-m", "{project}"]
CMD ["serve"]
```

## Docker Compose Template

```yaml
# docker-compose.yaml
# Generated from level-11 infrastructure

version: "3.8"

services:
  app:
    build:
      context: .
      dockerfile: infrastructure/docker/Dockerfile
    ports:
      - "${PORT:-8000}:8000"
    environment:
      - DATABASE_URL=postgresql://postgres:postgres@db:5432/${DB_NAME}
    depends_on:
      db:
        condition: service_healthy
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:8000/health"]
      interval: 30s
      timeout: 10s
      retries: 3
      
  db:
    image: postgres:15-alpine
    environment:
      - POSTGRES_USER=postgres
      - POSTGRES_PASSWORD=postgres
      - POSTGRES_DB=${DB_NAME}
    volumes:
      - postgres_data:/var/lib/postgresql/data
    healthcheck:
      test: ["CMD-SHELL", "pg_isready -U postgres"]
      interval: 5s
      timeout: 5s
      retries: 5

volumes:
  postgres_data:
```

## Manifest Item Schema

```yaml
infrastructure_item:
  id: "infrastructure.{component}"
  name: "{ComponentName}"
  kind: "infrastructure"
  traces:
    - ref: "level-10.bootstrap.{item}"
      role: "deploys"
  definition:
    type: "{container|compose|k8s|monitoring|script}"
    platform: "{docker|kubernetes|cloud}"
  artifacts:
    - path: "infrastructure/..."
  status: "generated|validated"
```

## Validation Rules

```yaml
validation:
  containers_build:
    rule: "docker build succeeds"
    critical: true
    
  compose_valid:
    rule: "docker-compose config validates"
    critical: true
    
  health_checks:
    rule: "All services have health checks"
    critical: true
    
  networking:
    rule: "Services can communicate"
    critical: true
    
  secrets_secure:
    rule: "No secrets in plain text"
    critical: true
```

## Output

```
level-11.manifest.yaml
infrastructure/
├── docker/
├── compose/
├── kubernetes/        (if needed)
├── monitoring/
├── scripts/
└── terraform/         (if cloud-native)
```

## Invariant

```
∀ service ∈ Level10.application:
  ∃ container ∈ Level11: container.runs(service)

containers.build_success = true
compose.valid = true
health_checks.defined = true

This is the FINAL level. System is deployable.
```

## Example (Illustrative Only)

```yaml
# level-11.manifest.yaml
items:
  - id: "infrastructure.dockerfile.app"
    kind: "infrastructure"
    traces:
      - ref: "level-10.bootstrap.entry"
        role: "containerizes"
    definition:
      type: "container"
      base_image: "python:3.11-slim"
      health_check: "/health"
    artifacts:
      - path: "infrastructure/docker/Dockerfile"
    status: "validated"
    
  - id: "infrastructure.compose.main"
    kind: "infrastructure"
    traces:
      - ref: "infrastructure.dockerfile.app"
        role: "orchestrates"
    definition:
      type: "compose"
      services: ["app", "db"]
    artifacts:
      - path: "infrastructure/compose/docker-compose.yaml"
    status: "validated"
    
  - id: "infrastructure.monitoring.prometheus"
    kind: "infrastructure"
    traces:
      - ref: "level-7.transformation.Metrics"
        role: "scrapes"
    definition:
      type: "monitoring"
      metrics_endpoint: "/metrics"
    artifacts:
      - path: "infrastructure/monitoring/prometheus/prometheus.yml"
    status: "validated"

counts:
  total: 8
  by_type:
    container: 2
    compose: 1
    monitoring: 3
    scripts: 2
    
validation:
  containers_build: true
  compose_valid: true
  health_checks_defined: true
  complete: true
```

## System Complete

At Level 11 completion:

```
Specifications (NL) 
    → Level 0 (Primitives)
    → Level 1 (Entities) 
    → Level 2 (Morphisms)
    → Level 3 (Modules)
    → Level 4 (Categories)
    → Level 5 (Functors)
    → Level 6 (Adjunctions)
    → Level 7 (Transformations)
    → Level 8 (Proofs)
    → Level 9 (Code)
    → Level 10 (Bootstrap)
    → Level 11 (Infrastructure)
    → DEPLOYED SYSTEM

Complete traceability from requirements to running containers.
Mathematical proofs at every categorical construction.
No gaps. No missing items. 100% coverage guaranteed.
```
