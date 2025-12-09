---
name: docker-generator
description: Generate Dockerfiles and docker-compose.yml from service topology. Multi-stage builds, networking, resource limits, health checks. Sub-skill of infrastructure-prover.
version: 1.0.0
allowed-tools: bash_tool, create_file
model: claude-sonnet-4-20250514
license: Proprietary - LeanOS Engineering Layer
---

# docker-generator: Topology → Docker Configs

## Purpose

Generate Dockerfiles and docker-compose.yml for local/dev deployment.

**Input:** Service topology graph  
**Output:** Docker configuration files

---

## Input

```
artifacts/engineering/code/frontend/.internal/topology-graph.json
```

---

## Generation Process

### Step 1: Generate Dockerfile per Service

**Multi-stage build pattern:**

```dockerfile
# artifacts/engineering/configs/docker/Dockerfile.catalog

# ============================================================================
# Stage 1: Dependencies
# ============================================================================
FROM python:3.11-slim as dependencies

WORKDIR /app

# Install system dependencies
RUN apt-get update && apt-get install -y \
    build-essential \
    curl \
    && rm -rf /var/lib/apt/lists/*

# Copy dependency files
COPY pyproject.toml poetry.lock ./

# Install Python dependencies
RUN pip install poetry && \
    poetry config virtualenvs.create false && \
    poetry install --no-dev --no-interaction --no-ansi

# ============================================================================
# Stage 2: Build
# ============================================================================
FROM dependencies as build

WORKDIR /app

# Copy source code
COPY src/ ./src/
COPY alembic/ ./alembic/
COPY alembic.ini ./

# Run any build steps (if needed)
# RUN python -m compileall src/

# ============================================================================
# Stage 3: Runtime
# ============================================================================
FROM python:3.11-slim as runtime

WORKDIR /app

# Install runtime dependencies only
RUN apt-get update && apt-get install -y \
    curl \
    && rm -rf /var/lib/apt/lists/*

# Copy Python packages from dependencies stage
COPY --from=dependencies /usr/local/lib/python3.11/site-packages /usr/local/lib/python3.11/site-packages
COPY --from=dependencies /usr/local/bin /usr/local/bin

# Copy application code from build stage
COPY --from=build /app /app

# Create non-root user
RUN useradd -m -u 1000 appuser && \
    chown -R appuser:appuser /app

USER appuser

# Health check
HEALTHCHECK --interval=30s --timeout=3s --start-period=40s --retries=3 \
    CMD curl -f http://localhost:8001/health || exit 1

# Expose port
EXPOSE 8001

# Run application
CMD ["uvicorn", "src.main:app", "--host", "0.0.0.0", "--port", "8001"]
```

**Generation rules:**
- Stage 1: Install dependencies (cached layer)
- Stage 2: Build application (if needed)
- Stage 3: Runtime (minimal, non-root user)
- Health check from service spec
- Port from service spec
- CMD from framework (uvicorn for FastAPI)

---

### Step 2: Generate docker-compose.yml

```yaml
# artifacts/engineering/configs/docker/docker-compose.yml

version: '3.8'

services:
  # ==========================================================================
  # External Dependencies
  # ==========================================================================
  
  postgres:
    image: postgres:15-alpine
    environment:
      POSTGRES_USER: ${POSTGRES_USER:-postgres}
      POSTGRES_PASSWORD: ${POSTGRES_PASSWORD:-postgres}
      POSTGRES_DB: ${POSTGRES_DB:-catalog}
    ports:
      - "5432:5432"
    volumes:
      - postgres_data:/var/lib/postgresql/data
    healthcheck:
      test: ["CMD-SHELL", "pg_isready -U postgres"]
      interval: 10s
      timeout: 5s
      retries: 5
  
  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"
    volumes:
      - redis_data:/data
    healthcheck:
      test: ["CMD", "redis-cli", "ping"]
      interval: 10s
      timeout: 5s
      retries: 5
  
  nats:
    image: nats:2.10-alpine
    command: ["-js", "-sd", "/data"]
    ports:
      - "4222:4222"
      - "8222:8222"
    volumes:
      - nats_data:/data
    healthcheck:
      test: ["CMD", "wget", "--no-verbose", "--tries=1", "--spider", "http://localhost:8222/healthz"]
      interval: 10s
      timeout: 5s
      retries: 5
  
  # ==========================================================================
  # Application Services (Initialization Order)
  # ==========================================================================
  
  catalog:
    build:
      context: ../../code/backend
      dockerfile: ../../configs/docker/Dockerfile.catalog
    ports:
      - "8001:8001"
    environment:
      DATABASE_URL: postgresql://postgres:postgres@postgres:5432/catalog
      REDIS_URL: redis://redis:6379
      NATS_URL: nats://nats:4222
      JWT_SECRET: ${JWT_SECRET}
    depends_on:
      postgres:
        condition: service_healthy
      redis:
        condition: service_healthy
      nats:
        condition: service_healthy
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:8001/health"]
      interval: 30s
      timeout: 3s
      retries: 3
      start_period: 40s
    networks:
      - app_network
    deploy:
      resources:
        limits:
          cpus: '2'
          memory: 4G
        reservations:
          cpus: '1'
          memory: 2G
  
  billing:
    build:
      context: ../../code/backend
      dockerfile: ../../configs/docker/Dockerfile.billing
    ports:
      - "8002:8002"
    environment:
      DATABASE_URL: postgresql://postgres:postgres@postgres:5432/billing
      CATALOG_SERVICE_URL: http://catalog:8001
      NATS_URL: nats://nats:4222
      JWT_SECRET: ${JWT_SECRET}
    depends_on:
      postgres:
        condition: service_healthy
      nats:
        condition: service_healthy
      catalog:
        condition: service_healthy
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:8002/health"]
      interval: 30s
      timeout: 3s
      retries: 3
      start_period: 40s
    networks:
      - app_network
    deploy:
      resources:
        limits:
          cpus: '1'
          memory: 2G
  
  auth:
    build:
      context: ../../code/backend
      dockerfile: ../../configs/docker/Dockerfile.auth
    ports:
      - "8003:8003"
    environment:
      DATABASE_URL: postgresql://postgres:postgres@postgres:5432/auth
      CATALOG_SERVICE_URL: http://catalog:8001
      JWT_SECRET: ${JWT_SECRET}
    depends_on:
      postgres:
        condition: service_healthy
      catalog:
        condition: service_healthy
    networks:
      - app_network

networks:
  app_network:
    driver: bridge

volumes:
  postgres_data:
  redis_data:
  nats_data:
```

**Key features:**
- External dependencies first (postgres, redis, nats)
- Services in initialization order (from topology)
- Health checks with `depends_on: service_healthy`
- Resource limits from service spec
- Environment variables for configuration
- Shared network for service-to-service communication

---

### Step 3: Generate .dockerignore

```
# artifacts/engineering/configs/docker/.dockerignore

**/__pycache__
**/*.pyc
**/*.pyo
**/*.pyd
.Python
*.so
*.egg
*.egg-info
dist
build

.env
.venv
venv/
ENV/

.git
.gitignore
.dockerignore

node_modules/
npm-debug.log

tests/
*.test.py
pytest.ini
.pytest_cache/

docs/
*.md
README*

.vscode/
.idea/
*.swp
*.swo
*~
```

---

### Step 4: Generate Docker Helper Scripts

**Start script:**
```bash
# artifacts/engineering/configs/docker/start.sh

#!/bin/bash
set -e

echo "Starting services..."

# Build images
docker-compose build

# Start services
docker-compose up -d

# Wait for services to be healthy
echo "Waiting for services to be healthy..."
docker-compose ps

# Show logs
echo ""
echo "Services started. View logs with: docker-compose logs -f"
echo "Stop services with: docker-compose down"
```

**Stop script:**
```bash
# artifacts/engineering/configs/docker/stop.sh

#!/bin/bash
set -e

echo "Stopping services..."
docker-compose down

echo "Services stopped."
```

**Logs script:**
```bash
# artifacts/engineering/configs/docker/logs.sh

#!/bin/bash

# Follow logs for specific service or all
if [ -z "$1" ]; then
    docker-compose logs -f
else
    docker-compose logs -f "$1"
fi
```

---

## Output Structure

```
artifacts/engineering/configs/docker/
├── Dockerfile.catalog
├── Dockerfile.billing
├── Dockerfile.auth
├── docker-compose.yml
├── .dockerignore
├── start.sh
├── stop.sh
└── logs.sh
```

---

## Success Criteria

✓ Dockerfile per service (multi-stage)
✓ docker-compose.yml with all services
✓ External dependencies configured
✓ Services in initialization order
✓ Health checks configured
✓ Resource limits set
✓ Networks configured
✓ Helper scripts generated

---

## Key Features

**Multi-stage builds:**
- Smaller final images (runtime only)
- Cached dependency layers
- Non-root user for security

**Health checks:**
- Service readiness validation
- Automatic restart on failure
- Dependency ordering

**Resource limits:**
- CPU and memory constraints
- Prevents resource exhaustion
- Matches service spec

**Networking:**
- Shared network for services
- Service discovery by name
- Port mapping for external access

---

## Error Handling

**Missing service spec:**
```
ERROR: Service 'CatalogService' not in topology graph
Action: Re-run service-topology-analyzer
```

**Invalid resource spec:**
```
ERROR: Invalid CPU value for CatalogService
Value: "not-a-number"
Expected: numeric (e.g., 2, 0.5)
Action: Fix resources in services.spec.yaml
```

---

## Key Insights

1. **Multi-stage builds optimize image size** - Runtime images ~50% smaller
2. **Health checks enable dependency ordering** - Services wait for dependencies
3. **Resource limits prevent issues** - Memory leaks don't crash host
4. **Initialization order matters** - From topology graph
5. **Docker Compose is dev/local** - Not production (use Kubernetes)

**Next:** kubernetes-generator creates production deployment manifests