---
name: ci-cd-generator
description: Generate GitHub Actions workflows for build, test, and deployment pipelines. Environment-specific configs, caching, secrets management. Sub-skill of infrastructure-prover.
version: 1.0.0
allowed-tools: bash_tool, create_file
model: claude-sonnet-4-20250514
license: Proprietary - LeanOS Engineering Layer
---

# ci-cd-generator: Topology → CI/CD Pipelines

## Purpose

Generate GitHub Actions workflows for automated build, test, and deployment.

**Input:** Service topology graph + platform choice  
**Output:** GitHub Actions YAML files

---

## Generated Workflows

### 1. Build Pipeline

```yaml
# .github/workflows/build.yml
name: Build

on:
  push:
    branches: [main, develop]
  pull_request:
    branches: [main]

jobs:
  build-catalog:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Set up Python
        uses: actions/setup-python@v4
        with:
          python-version: '3.11'
          cache: 'pip'
      
      - name: Install dependencies
        run: |
          cd services/catalog
          pip install poetry
          poetry install
      
      - name: Build Docker image
        run: |
          docker build -f configs/docker/Dockerfile.catalog -t catalog:${{ github.sha }} .
      
      - name: Push to registry
        run: |
          echo ${{ secrets.DOCKER_PASSWORD }} | docker login -u ${{ secrets.DOCKER_USERNAME }} --password-stdin
          docker push catalog:${{ github.sha }}
  
  build-billing:
    runs-on: ubuntu-latest
    steps:
      # Similar to catalog...
```

---

### 2. Test Pipeline

```yaml
# .github/workflows/test.yml
name: Test

on:
  push:
    branches: [main, develop]
  pull_request:
    branches: [main]

jobs:
  unit-tests:
    runs-on: ubuntu-latest
    strategy:
      matrix:
        service: [catalog, billing, auth]
    steps:
      - uses: actions/checkout@v3
      
      - name: Set up Python
        uses: actions/setup-python@v4
        with:
          python-version: '3.11'
      
      - name: Run unit tests
        run: |
          cd services/${{ matrix.service }}
          pip install poetry
          poetry install
          poetry run pytest tests/unit
  
  integration-tests:
    runs-on: ubuntu-latest
    needs: unit-tests
    steps:
      - uses: actions/checkout@v3
      
      - name: Start services
        run: docker-compose -f configs/docker/docker-compose.yml up -d
      
      - name: Run integration tests
        run: pytest tests/integration
      
      - name: Stop services
        run: docker-compose down
```

---

### 3. Deploy Pipeline

```yaml
# .github/workflows/deploy.yml
name: Deploy

on:
  push:
    branches: [main]

jobs:
  deploy-dev:
    runs-on: ubuntu-latest
    environment: dev
    steps:
      - uses: actions/checkout@v3
      
      - name: Deploy to dev (Docker Compose)
        run: |
          ssh ${{ secrets.DEV_HOST }} << 'EOF'
            cd /app
            docker-compose pull
            docker-compose up -d
          EOF
  
  deploy-prod:
    runs-on: ubuntu-latest
    environment: prod
    needs: deploy-dev
    if: github.ref == 'refs/heads/main'
    steps:
      - uses: actions/checkout@v3
      
      - name: Configure kubectl
        run: |
          echo "${{ secrets.KUBECONFIG }}" | base64 -d > kubeconfig
          export KUBECONFIG=kubeconfig
      
      - name: Deploy to Kubernetes
        run: |
          kubectl apply -f configs/k8s/
          kubectl rollout status deployment/catalog-service
          kubectl rollout status deployment/billing-service
```

---

## Output Structure

```
artifacts/engineering/configs/ci-cd/.github/workflows/
├── build.yml
├── test.yml
└── deploy.yml
```

---

## Key Features

- **Build:** Docker images per service, pushed to registry
- **Test:** Unit tests (parallel), integration tests (sequential)
- **Deploy:** Environment-specific (dev → prod)
- **Caching:** Dependencies cached for speed
- **Secrets:** Managed via GitHub secrets
- **Matrix builds:** Parallel service builds

---

## Success Criteria

✓ Build workflow (all services)
✓ Test workflow (unit + integration)
✓ Deploy workflow (multi-environment)
✓ Caching configured
✓ Secrets management
✓ Environment protection

**Next:** topology-prover verifies configs match spec