---
name: gen-wiring
description: |
  Generate application wiring: entry points, dependency injection, infrastructure
  configuration. Creates main.py, container, Dockerfile, docker-compose.yaml.
  Topology-aware (monolith/microservices/library). Use when: finalizing generation,
  creating deployable system.
---

# Gen Wiring

Generate application wiring and infrastructure.

## CRITICAL RULE

This skill generates **ACTUAL FILES**, not YAML with code inside.

```
WRONG: Writing Dockerfile content inside wiring-manifest.yaml
RIGHT: create_file("Dockerfile", dockerfile_content)
```

## Input

- `artifacts/v{N}/build/functors.yaml`
- `artifacts/v{N}/build/transformations.yaml`
- `artifacts/v{N}/build/effects.yaml`
- `artifacts/v{N}/targets.yaml`
- `artifacts/v{N}/gen/types-manifest.yaml`
- `artifacts/v{N}/gen/morphisms-manifest.yaml`

## Output

- `artifacts/v{N}/gen/{language}/src/main.py` (or equivalent)
- `artifacts/v{N}/gen/{language}/src/container.py`
- `artifacts/v{N}/gen/{language}/Dockerfile`
- `artifacts/v{N}/gen/{language}/docker-compose.yaml`
- `artifacts/v{N}/gen/{language}/pyproject.toml` (or package.json)
- `artifacts/v{N}/gen/wiring-manifest.yaml`

## Process

1. **Read targets.yaml** — Topology, language, standardization
2. **Generate DI container** — Wire dependencies
3. **Generate entry points** — Based on topology
4. **Apply transformations** — Middleware composition
5. **Generate infrastructure** — Docker, compose, config
6. **Write manifest** — Track what was generated

## Topology Handling

### Monolith

Single entry point, all services in one process.

```
gen/python/
├── src/
│   ├── main.py           # Single entry point
│   ├── container.py      # DI container
│   └── config.py         # Configuration
├── Dockerfile
├── docker-compose.yaml
└── pyproject.toml
```

### Microservices

Multiple services, each with own entry point.

```
gen/python/
├── services/
│   ├── users/
│   │   ├── main.py
│   │   ├── Dockerfile
│   │   └── ...
│   ├── orders/
│   │   ├── main.py
│   │   ├── Dockerfile
│   │   └── ...
├── shared/
│   └── ...
├── docker-compose.yaml   # Orchestrates all services
└── pyproject.toml
```

### Library

No entry point, just importable code.

```
gen/python/
├── src/
│   └── ...               # Domain code only
├── pyproject.toml        # Library metadata
└── README.md
```

### Serverless

Function handlers, no long-running process.

```
gen/python/
├── functions/
│   ├── create_user/
│   │   └── handler.py
│   ├── get_user/
│   │   └── handler.py
├── serverless.yaml
└── pyproject.toml
```

## Generated Code Examples

### main.py (Monolith)

```python
# src/main.py
"""Application entry point."""
import asyncio
import logging
from contextlib import asynccontextmanager

from fastapi import FastAPI
from fastapi.middleware.cors import CORSMiddleware

from .container import Container
from .config import Settings
from .api.routes import users, orders
from .middleware import setup_middleware


@asynccontextmanager
async def lifespan(app: FastAPI):
    """Application lifespan manager."""
    # Startup
    container = app.state.container
    await container.init_resources()
    logging.info("Application started")
    
    yield
    
    # Shutdown
    await container.shutdown_resources()
    logging.info("Application stopped")


def create_app() -> FastAPI:
    """Application factory."""
    settings = Settings()
    
    app = FastAPI(
        title="Generated API",
        version="1.0.0",
        lifespan=lifespan,
    )
    
    # Initialize DI container
    container = Container()
    container.config.from_pydantic(settings)
    app.state.container = container
    
    # Setup middleware (in order from transformations.yaml)
    setup_middleware(app, container)
    
    # Register routes
    app.include_router(users.router, prefix="/api/v1/users", tags=["users"])
    app.include_router(orders.router, prefix="/api/v1/orders", tags=["orders"])
    
    return app


app = create_app()


if __name__ == "__main__":
    import uvicorn
    uvicorn.run(
        "src.main:app",
        host="0.0.0.0",
        port=8000,
        reload=True,
    )
```

### container.py (Dependency Injection)

```python
# src/container.py
"""Dependency injection container."""
from dependency_injector import containers, providers

from .config import Settings
from .storage.database import Database
from .storage.repositories.user_repository import SqlUserRepository


class Container(containers.DeclarativeContainer):
    """Application DI container."""
    
    wiring_config = containers.WiringConfiguration(
        modules=[
            ".api.handlers.user_handlers",
            ".api.handlers.auth_handlers",
        ]
    )
    
    # Configuration
    config = providers.Configuration()
    
    # Infrastructure
    database = providers.Singleton(
        Database,
        url=config.database_url,
    )
    
    async def init_resources(self) -> None:
        """Initialize async resources."""
        await self.database().connect()
        
    async def shutdown_resources(self) -> None:
        """Cleanup async resources."""
        await self.database().disconnect()
```

### dependencies.py (Env Provider) - CRITICAL

```python
# src/api/dependencies.py
"""
FastAPI dependencies for injecting Env.

THIS IS THE CRITICAL BRIDGE between categorical abstractions and runtime.
The Reader monad (Env -> A) becomes Depends(get_env) in FastAPI.
"""
from fastapi import Depends
from sqlalchemy.ext.asyncio import AsyncSession

from ..domain.effects.app import Env
from ..domain.interfaces.repositories import Repositories
from ..storage.database import get_session
from ..storage.repositories.user_repository import SqlUserRepository
from ..storage.repositories.org_repository import SqlOrgRepository
from ..config import Settings, get_settings


async def get_env(
    session: AsyncSession = Depends(get_session),
    settings: Settings = Depends(get_settings),
) -> Env:
    """
    Build Env from FastAPI dependencies.
    
    This is where the categorical Reader monad becomes concrete:
    - Reader[Env, A] in types
    - App[A] = Env -> IO[Result[E, A]] in domain
    - Depends(get_env) in FastAPI handlers
    
    ALL domain operations get their dependencies through Env,
    NOT through function parameters.
    """
    # Build repository implementations
    repositories = Repositories(
        users=SqlUserRepository(session),
        orgs=SqlOrgRepository(session),
        # ... add all repositories from interfaces
    )
    
    return Env(
        repositories=repositories,
        config=settings,
    )


# Shorthand for use in handlers
EnvDep = Depends(get_env)
```

### database.py (Session Provider)

```python
# src/storage/database.py
"""Database session management."""
from typing import AsyncGenerator
from sqlalchemy.ext.asyncio import (
    AsyncSession,
    async_sessionmaker,
    create_async_engine,
)

from ..config import get_settings


# Create engine (singleton)
settings = get_settings()
engine = create_async_engine(
    settings.database_url,
    echo=settings.debug,
    pool_size=5,
    max_overflow=10,
)

# Session factory
async_session_factory = async_sessionmaker(
    engine,
    class_=AsyncSession,
    expire_on_commit=False,
)


async def get_session() -> AsyncGenerator[AsyncSession, None]:
    """
    Provide database session.
    
    Used via Depends(get_session) in FastAPI.
    Sessions are request-scoped (one per request).
    """
    async with async_session_factory() as session:
        try:
            yield session
            await session.commit()
        except Exception:
            await session.rollback()
            raise
```

### middleware.py (Transformation Application)

```python
# src/middleware/__init__.py
"""Middleware setup from transformations."""
from fastapi import FastAPI
from starlette.middleware.base import BaseHTTPMiddleware

from .auth import AuthMiddleware
from .logging import LoggingMiddleware
from .validation import ValidationMiddleware
from .timeout import TimeoutMiddleware


def setup_middleware(app: FastAPI, container) -> None:
    """
    Apply transformations in composition order.
    
    Order (outer to inner):
    1. logging  - outermost, logs everything
    2. auth     - authentication check
    3. validation - input validation
    4. timeout  - innermost, timeout on actual work
    
    Applied in reverse order (first added is outermost):
    """
    # Timeout (innermost)
    app.add_middleware(
        TimeoutMiddleware,
        default_timeout_ms=5000,
    )
    
    # Validation
    app.add_middleware(ValidationMiddleware)
    
    # Auth
    app.add_middleware(
        AuthMiddleware,
        container=container,
        exclude_paths=["/health", "/api/v1/auth/login", "/api/v1/users"],
    )
    
    # Logging (outermost)
    app.add_middleware(
        LoggingMiddleware,
        format="json",
        level="info",
    )
```

### config.py

```python
# src/config.py
"""Application configuration."""
from pydantic_settings import BaseSettings


class Settings(BaseSettings):
    """Application settings from environment."""
    
    # Database
    database_url: str = "postgresql://localhost/app"
    
    # Auth
    jwt_secret: str = "change-me-in-production"
    jwt_algorithm: str = "HS256"
    jwt_expire_minutes: int = 60
    
    # Resilience
    timeout_ms: int = 5000
    retry_max_attempts: int = 3
    retry_backoff: str = "exponential"
    
    # Logging
    log_level: str = "info"
    log_format: str = "json"
    
    class Config:
        env_file = ".env"
        env_file_encoding = "utf-8"
```

## CRITICAL: Environment Variable Parity

Every variable in `config.py` MUST be present in:
1. `docker-compose.yaml` (environment section)
2. `.env.example` (documented with description)

### Extraction Process

```python
def extract_config_vars(config_py: str) -> dict[str, dict]:
    """
    Extract all settings from config.py.
    
    Returns: {
        "DATABASE_URL": {"type": "str", "default": "postgresql://localhost/app", "required": True},
        "JWT_SECRET": {"type": "str", "default": "change-me-in-production", "required": True},
        ...
    }
    """
    import ast
    
    tree = ast.parse(config_py)
    vars = {}
    
    for node in ast.walk(tree):
        if isinstance(node, ast.ClassDef) and node.name == "Settings":
            for item in node.body:
                if isinstance(item, ast.AnnAssign) and item.target:
                    var_name = item.target.id
                    env_name = var_name.upper()  # Pydantic convention
                    
                    # Get type
                    type_str = ast.unparse(item.annotation) if item.annotation else "str"
                    
                    # Get default
                    default = ast.unparse(item.value) if item.value else None
                    
                    # Required if no default
                    required = default is None
                    
                    vars[env_name] = {
                        "field_name": var_name,
                        "type": type_str,
                        "default": default,
                        "required": required,
                    }
    
    return vars
```

### Generated .env.example

```bash
# .env.example
# Environment configuration for the application.
# Copy this file to .env and update values for your environment.
#
# GENERATED FILE - matches config.py Settings class
# All variables here MUST be in config.py
# All variables in config.py MUST be here

# ============================================================
# DATABASE
# ============================================================

# PostgreSQL connection string
# Format: postgresql://user:password@host:port/database
DATABASE_URL=postgresql://postgres:postgres@db:5432/app

# ============================================================
# AUTHENTICATION
# ============================================================

# JWT signing secret - CHANGE IN PRODUCTION
# Generate with: openssl rand -hex 32
JWT_SECRET=change-me-in-production-use-openssl-rand-hex-32

# JWT algorithm (HS256, HS384, HS512, RS256, etc.)
JWT_ALGORITHM=HS256

# JWT token expiration in minutes
JWT_EXPIRE_MINUTES=60

# ============================================================
# RESILIENCE
# ============================================================

# Request timeout in milliseconds
TIMEOUT_MS=5000

# Maximum retry attempts for failed operations
RETRY_MAX_ATTEMPTS=3

# Retry backoff strategy: exponential, linear, constant
RETRY_BACKOFF=exponential

# ============================================================
# LOGGING
# ============================================================

# Log level: debug, info, warning, error, critical
LOG_LEVEL=info

# Log format: json, text
LOG_FORMAT=json
```

### Generated docker-compose.yaml (environment section)

```yaml
# docker-compose.yaml
version: "3.8"

services:
  app:
    build: .
    ports:
      - "8000:8000"
    environment:
      # === ALL VARIABLES FROM config.py ===
      # Database
      - DATABASE_URL=postgresql://postgres:postgres@db:5432/app
      
      # Auth
      - JWT_SECRET=${JWT_SECRET:-change-me-in-production}
      - JWT_ALGORITHM=${JWT_ALGORITHM:-HS256}
      - JWT_EXPIRE_MINUTES=${JWT_EXPIRE_MINUTES:-60}
      
      # Resilience
      - TIMEOUT_MS=${TIMEOUT_MS:-5000}
      - RETRY_MAX_ATTEMPTS=${RETRY_MAX_ATTEMPTS:-3}
      - RETRY_BACKOFF=${RETRY_BACKOFF:-exponential}
      
      # Logging
      - LOG_LEVEL=${LOG_LEVEL:-info}
      - LOG_FORMAT=${LOG_FORMAT:-json}
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
      - POSTGRES_DB=app
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

### Parity Verification

```python
def verify_env_parity(gen_dir: str) -> list[str]:
    """
    Verify environment variable parity across:
    - config.py (source of truth)
    - docker-compose.yaml
    - .env.example
    
    Returns list of errors.
    """
    errors = []
    
    # 1. Extract from config.py
    config_py = read_file(f"{gen_dir}/src/config.py")
    config_vars = extract_config_vars(config_py)
    
    # 2. Extract from docker-compose.yaml
    compose = load_yaml(f"{gen_dir}/docker-compose.yaml")
    compose_vars = set()
    for service in compose.get("services", {}).values():
        for env in service.get("environment", []):
            if isinstance(env, str):
                var_name = env.split("=")[0].replace("${", "").split(":-")[0].rstrip("}")
                compose_vars.add(var_name)
    
    # 3. Extract from .env.example
    env_example = read_file(f"{gen_dir}/.env.example")
    env_vars = set()
    for line in env_example.splitlines():
        line = line.strip()
        if line and not line.startswith("#") and "=" in line:
            var_name = line.split("=")[0]
            env_vars.add(var_name)
    
    # 4. Check parity
    config_var_names = set(config_vars.keys())
    
    # Missing from docker-compose
    missing_compose = config_var_names - compose_vars
    for var in missing_compose:
        errors.append(
            f"ENV PARITY: {var} in config.py but missing from docker-compose.yaml"
        )
    
    # Missing from .env.example
    missing_env = config_var_names - env_vars
    for var in missing_env:
        errors.append(
            f"ENV PARITY: {var} in config.py but missing from .env.example"
        )
    
    # Extra in docker-compose (warning)
    extra_compose = compose_vars - config_var_names - {"POSTGRES_USER", "POSTGRES_PASSWORD", "POSTGRES_DB"}
    for var in extra_compose:
        errors.append(
            f"ENV PARITY WARNING: {var} in docker-compose.yaml but not in config.py"
        )
    
    # Extra in .env.example (warning)
    extra_env = env_vars - config_var_names
    for var in extra_env:
        errors.append(
            f"ENV PARITY WARNING: {var} in .env.example but not in config.py"
        )
    
    return errors
```

### Gate G7 Integration

Add to Gate G7 validation:

```python
def validate_gate_g7(gen_dir: str, targets: dict) -> GateResult:
    errors = []
    
    # ... existing checks ...
    
    # === ENVIRONMENT VARIABLE PARITY ===
    env_errors = verify_env_parity(gen_dir)
    for err in env_errors:
        if "WARNING" in err:
            warnings.append(err)
        else:
            errors.append(err)
    
    return GateResult(passed=len(errors) == 0, errors=errors, warnings=warnings)
```

### Validation Commands

```bash
# Extract config vars
python -c "
from src.config import Settings
import json
fields = Settings.model_fields
print(json.dumps({k.upper(): str(v.annotation) for k, v in fields.items()}))
"

# Check docker-compose has all vars
grep -E '^\s+- [A-Z_]+=' docker-compose.yaml | sed 's/.*- //' | cut -d= -f1 | sort > /tmp/compose_vars.txt
python -c "from src.config import Settings; print('\n'.join(k.upper() for k in Settings.model_fields))" | sort > /tmp/config_vars.txt
diff /tmp/config_vars.txt /tmp/compose_vars.txt

# Check .env.example has all vars
grep -E '^[A-Z_]+=' .env.example | cut -d= -f1 | sort > /tmp/env_vars.txt
diff /tmp/config_vars.txt /tmp/env_vars.txt
```

### Dockerfile

```dockerfile
# Dockerfile
FROM python:3.11-slim as builder

WORKDIR /app

# Install build dependencies
RUN pip install --no-cache-dir poetry

# Copy dependency files
COPY pyproject.toml poetry.lock ./

# Install dependencies
RUN poetry config virtualenvs.create false \
    && poetry install --no-dev --no-interaction --no-ansi

# Production stage
FROM python:3.11-slim

WORKDIR /app

# Copy installed packages from builder
COPY --from=builder /usr/local/lib/python3.11/site-packages /usr/local/lib/python3.11/site-packages
COPY --from=builder /usr/local/bin /usr/local/bin

# Copy application code
COPY src/ ./src/

# Create non-root user
RUN useradd --create-home appuser
USER appuser

# Environment
ENV PYTHONUNBUFFERED=1
ENV PYTHONDONTWRITEBYTECODE=1

# Health check
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
    CMD curl -f http://localhost:8000/health || exit 1

# Run
EXPOSE 8000
CMD ["uvicorn", "src.main:app", "--host", "0.0.0.0", "--port", "8000"]
```

### docker-compose.yaml

```yaml
# docker-compose.yaml
version: "3.8"

services:
  app:
    build: .
    ports:
      - "8000:8000"
    environment:
      - DATABASE_URL=postgresql://postgres:postgres@db:5432/app
      - JWT_SECRET=${JWT_SECRET:-dev-secret}
      - LOG_LEVEL=info
    depends_on:
      db:
        condition: service_healthy
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:8000/health"]
      interval: 30s
      timeout: 3s
      retries: 3
      start_period: 10s

  db:
    image: postgres:15-alpine
    environment:
      - POSTGRES_USER=postgres
      - POSTGRES_PASSWORD=postgres
      - POSTGRES_DB=app
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

### pyproject.toml

```toml
# pyproject.toml
[tool.poetry]
name = "generated-app"
version = "1.0.0"
description = "Generated by LeanOS"
authors = ["LeanOS Generator"]

[tool.poetry.dependencies]
python = "^3.11"
fastapi = "^0.104.0"
uvicorn = {extras = ["standard"], version = "^0.24.0"}
pydantic = "^2.5.0"
pydantic-settings = "^2.1.0"
sqlalchemy = {extras = ["asyncio"], version = "^2.0.0"}
asyncpg = "^0.29.0"
dependency-injector = "^4.41.0"
python-jose = {extras = ["cryptography"], version = "^3.3.0"}
structlog = "^23.2.0"

[tool.poetry.group.dev.dependencies]
pytest = "^7.4.0"
pytest-asyncio = "^0.21.0"
httpx = "^0.25.0"
ruff = "^0.1.0"
mypy = "^1.7.0"

[build-system]
requires = ["poetry-core"]
build-backend = "poetry.core.masonry.api"

[tool.ruff]
line-length = 100
target-version = "py311"

[tool.mypy]
python_version = "3.11"
strict = true
```

## Manifest Output

```yaml
version: "1.0"

topology: monolith
language: python

entry_points:
  - path: "src/main.py"
    type: application
    command: "uvicorn src.main:app"

files:
  # Application
  - path: "src/main.py"
    type: "entry_point"
    description: "FastAPI application factory"
    
  - path: "src/container.py"
    type: "di_container"
    description: "Dependency injection configuration"
    
  - path: "src/config.py"
    type: "configuration"
    description: "Application settings"
  
  # CRITICAL: Env provider
  - path: "src/api/dependencies.py"
    type: "env_provider"
    description: "Provides Env for Reader monad - bridges categorical abstractions to runtime"
    critical: true
    
  - path: "src/storage/database.py"
    type: "session_provider"
    description: "Database session management"
    
  # Middleware
  - path: "src/middleware/__init__.py"
    type: "middleware_setup"
    transformations_applied: ["logging", "auth", "validation", "timeout"]
    
  - path: "src/middleware/auth.py"
    type: "middleware"
    transformation: "auth"
    
  - path: "src/middleware/logging.py"
    type: "middleware"
    transformation: "logging"
    
  - path: "src/middleware/error_handler.py"
    type: "middleware"
    transformation: "error_to_http"
    description: "Natural transformation: AppError -> HTTPResponse"
    
  - path: "src/middleware/timeout.py"
    type: "middleware"
    transformation: "timeout"
    
  # Infrastructure
  - path: "Dockerfile"
    type: "docker"
    
  - path: "docker-compose.yaml"
    type: "compose"
    services: ["app", "db"]
    
  - path: "pyproject.toml"
    type: "package_config"
    
  - path: ".env.example"
    type: "env_template"

transformations_applied:
  order: ["logging", "auth", "error_handler", "timeout"]
  composition: "logging(auth(error_handler(timeout(endpoint))))"

infrastructure:
  database:
    enabled: true
    type: postgresql
    container: db
    
  cache:
    enabled: false
    
  message_broker:
    enabled: false

summary:
  total_files: 12
  entry_points: 1
  middlewares: 4
  infrastructure: 3
```

## External Validation

```bash
# Verify files exist
ls -la gen/python/src/main.py
ls -la gen/python/Dockerfile
ls -la gen/python/docker-compose.yaml

# Verify Python imports
cd gen/python
python -c "from src.main import create_app; app = create_app()"

# Verify Docker builds
docker build -t test-app .

# Verify compose is valid
docker-compose config

# Verify can start (smoke test)
docker-compose up -d
curl http://localhost:8000/health
docker-compose down
```

## Validation Checklist

### Categorical Correctness (CRITICAL)
- [ ] `api/dependencies.py` exists and provides `get_env`
- [ ] Env contains Repositories with all repository interfaces
- [ ] Handlers use `env: Env = Depends(get_env)`
- [ ] Error handler middleware transforms AppError → HTTP

### Infrastructure
- [ ] Entry point created (main.py or equivalent)
- [ ] DI container wires all dependencies
- [ ] Middleware applies transformations in correct order
- [ ] Configuration reads from environment
- [ ] Dockerfile builds successfully
- [ ] docker-compose.yaml is valid
- [ ] pyproject.toml has all dependencies
- [ ] Can import and create app
- [ ] Health check endpoint works

### Validation Commands

```bash
# Categorical checks
grep -q "def get_env" gen/python/src/api/dependencies.py
grep -q "Repositories" gen/python/src/api/dependencies.py
grep -q "env: Env = Depends" gen/python/src/api/handlers/*.py

# Import checks
python -c "from src.api.dependencies import get_env, Env"
python -c "from src.domain.interfaces.repositories import Repositories"
```

## Do NOT

- **Put code in YAML** — Write actual files
- **Skip dependencies.py** — This is the categorical bridge to runtime
- **Pass repos to operations** — Operations get deps from Env
- **Skip error handler** — AppError must map to HTTP responses
- **Skip middleware order** — Order matters for semantics
- **Hardcode secrets** — Use environment variables
- **Skip health checks** — Required for production
- **Forget dependencies** — pyproject.toml must be complete
- **Skip validation** — docker-compose config must pass
