---
name: lean-os-gen
description: |
  Gen phase agent. Generates actual source code files from verified artifacts.
  Runs: gen-types, gen-maps, verify-maps, gen-code, apply-standards, gen-wiring.
  Validates: Gate G7.5 (maps verified), Gate G7 (code valid).
skills: gen-types, gen-maps, verify-maps, gen-code, apply-standards, gen-wiring
model: opus
---

# Gen Phase Agent

Generate actual source code from verified artifacts.

## Purpose

Transform verified mathematical structures into production code:
- Domain types (classes, enums, dataclasses)
- Code maps (verifiable intermediate representation)
- Operations (functions, methods)
- Standardization (middleware, error handling)
- Entry points, DI, infrastructure

## CRITICAL RULES

### Rule 1: Generate ACTUAL FILES

```python
# WRONG
write_yaml("gen/types-manifest.yaml", {"code": "class User: ..."})

# RIGHT
create_file("gen/python/src/domain/types/user.py", "class User: ...")
write_yaml("gen/types-manifest.yaml", {"files": ["src/domain/types/user.py"]})
```

### Rule 2: Use Code Maps for Verification

Generate lightweight maps BEFORE full code. Verify maps BEFORE generating code.
This catches type mismatches, wrong arguments, and missing imports early.

```
300 lines of maps → verify → 5000 lines of code
(fast check)        (fast)   (guaranteed correct)
```

### Rule 3: Effects Module FIRST

The effects module (Result, App, Errors) must be generated before anything else.

## Prerequisites

- Gates G5-G6 passed (verify phase complete)
- `artifacts/v{N}/build/` contains verified artifacts
- `artifacts/v{N}/targets.yaml` exists

## Skills

| Skill | Output | Purpose |
|-------|--------|---------|
| gen-types | effects/, types/, interfaces/ | Foundation types |
| gen-maps | maps/*.map.yaml | Verifiable code specifications |
| verify-maps | maps-verification.yaml | Catch errors before codegen |
| gen-code | operations/, handlers/ | Generate from verified maps |
| apply-standards | middleware/ | Inject cross-cutting concerns |
| gen-wiring | main.py, Dockerfile | Entry points, infrastructure |

## Execution Order

```
build/*.yaml + targets.yaml
     │
     ├─→ [gen-types]
     │       │
     │       ↓
     │   src/domain/effects/      ← FIRST (Result, App, Errors)
     │   src/domain/types/        ← SECOND
     │   src/domain/interfaces/   ← Repository protocols
     │   src/api/schemas/         ← If API enabled
     │   src/storage/models/      ← If persistence enabled
     │       │
     │       ↓
     ├─→ [gen-maps]
     │       │
     │       ↓
     │   maps/operations/*.map.yaml
     │   maps/handlers/*.map.yaml
     │       │
     │       ↓
     ├─→ [verify-maps] ─→ Gate G7.5
     │       │
     │       ↓ (ONLY if G7.5 passes)
     │   maps-verification.yaml (status: PASS)
     │       │
     │       ↓
     ├─→ [gen-code]
     │       │
     │       ↓
     │   src/domain/operations/*.py  ← From verified maps
     │   src/api/handlers/*.py       ← From verified maps
     │       │
     │       ↓
     ├─→ [apply-standards]
     │       │
     │       ↓
     │   src/middleware/*.py
     │   Handlers with StandardResponse
     │       │
     │       ↓
     └─→ [gen-wiring]
             │
             ↓
         main.py, container.py
         Dockerfile, docker-compose.yaml
         pyproject.toml
             │
             ↓
        Gate G7 (final validation)
```

## Process

```python
def run_gen_phase() -> GateResult:
    # Load inputs
    category = load_yaml("build/category.yaml")
    effects = load_yaml("build/effects.yaml")
    functors = load_yaml("build/functors.yaml")
    transformations = load_yaml("build/transformations.yaml")
    targets = load_yaml("targets.yaml")
    
    language = targets["targets"]["language"]["primary"]
    gen_dir = f"gen/{language}"
    
    # === PHASE 1: Generate Types (Foundation) ===
    run_skill("gen-types", category, effects, functors, targets)
    
    # Verify effects module exists (CRITICAL)
    if not verify_effects_exist(gen_dir):
        return GateResult(passed=False, errors=["Effects module not generated"])
    
    # === PHASE 2: Generate Code Maps ===
    run_skill("gen-maps", category, effects, functors, targets)
    
    if not file_exists(f"{gen_dir}/maps/operations"):
        return GateResult(passed=False, errors=["Code maps not generated"])
    
    # === GATE G7.5: Verify Maps ===
    run_skill("verify-maps", gen_dir)
    
    verification = load_yaml(f"{gen_dir}/maps-verification.yaml")
    if verification["status"] != "PASS":
        return GateResult(
            passed=False,
            errors=verification["errors"],
            message="Code maps failed verification. Fix before generating code."
        )
    
    # === PHASE 3: Generate Code (from verified maps) ===
    run_skill("gen-code", gen_dir)
    
    if not verify_operations_exist(gen_dir):
        return GateResult(passed=False, errors=["Code generation failed"])
    
    # === PHASE 4: Apply Standards ===
    run_skill("apply-standards", transformations, gen_dir)
    
    if not file_exists(f"{gen_dir}/src/middleware/setup.py"):
        return GateResult(passed=False, errors=["Standards not applied"])
    
    # === PHASE 5: Generate Wiring ===
    run_skill("gen-wiring", functors, transformations, targets)
    
    # === GATE G7: Final Validation ===
    return validate_gate_g7(gen_dir, targets)
```

## Gate G7.5: Maps Verified

Maps must pass static analysis AND be complete BEFORE code generation.

```python
def validate_gate_g7_5(gen_dir: str, category: dict) -> GateResult:
    errors = []
    
    # === COMPLETENESS CHECK ===
    # Count expected maps from category.yaml
    expected_operations = len(category.get("morphisms", {}).get("operations", []))
    expected_handlers = len(category.get("morphisms", {}).get("handlers", []))
    
    # Count actual maps
    ops_dir = f"{gen_dir}/maps/operations"
    handlers_dir = f"{gen_dir}/maps/handlers"
    
    actual_op_maps = len(glob(f"{ops_dir}/*.map.yaml")) if dir_exists(ops_dir) else 0
    actual_handler_maps = len(glob(f"{handlers_dir}/*.map.yaml")) if dir_exists(handlers_dir) else 0
    
    if actual_op_maps == 0:
        errors.append(f"No operation maps generated. Expected: {expected_operations}")
    elif actual_op_maps < expected_operations:
        errors.append(f"Incomplete operation maps: {actual_op_maps}/{expected_operations}")
    
    if actual_handler_maps == 0 and expected_handlers > 0:
        errors.append(f"No handler maps generated. Expected: {expected_handlers}")
    elif actual_handler_maps < expected_handlers:
        errors.append(f"Incomplete handler maps: {actual_handler_maps}/{expected_handlers}")
    
    # === VERIFICATION STATUS ===
    verification_file = f"{gen_dir}/maps-verification.yaml"
    if not file_exists(verification_file):
        errors.append("maps-verification.yaml not found. Run verify-maps first.")
        return GateResult(passed=False, errors=errors)
    
    verification = load_yaml(verification_file)
    
    if verification["status"] != "PASS":
        errors.extend(verification.get("errors", []))
        return GateResult(
            passed=False,
            errors=errors,
            message="Fix map errors before generating code"
        )
    
    # Check specific validations
    type_errors = [
        e for e in verification.get("errors", [])
        if "type" in e.lower()
    ]
    if type_errors:
        errors.extend(type_errors)
        return GateResult(
            passed=False,
            errors=errors,
            message="Type mismatches detected in code maps"
        )
    
    if errors:
        return GateResult(passed=False, errors=errors)
    
    return GateResult(passed=True)
```

### Gate G7.5 Bash Validation

```bash
cd artifacts/v{N}/gen

# Maps directories exist
test -d maps/operations || { echo "FAIL: maps/operations/ missing"; exit 1; }

# At least one operation map exists
ls maps/operations/*.map.yaml >/dev/null 2>&1 || { echo "FAIL: No operation maps"; exit 1; }

# Count maps vs expected (from category.yaml)
EXPECTED_OPS=$(grep -c "^  - name:" ../build/category.yaml || echo 0)
ACTUAL_OPS=$(ls maps/operations/*.map.yaml 2>/dev/null | wc -l)
if [ "$ACTUAL_OPS" -lt "$EXPECTED_OPS" ]; then
    echo "FAIL: Incomplete maps - $ACTUAL_OPS/$EXPECTED_OPS operations"
    exit 1
fi

# Verification passed
grep -q 'status: PASS' maps-verification.yaml || { echo "FAIL: Maps verification failed"; exit 1; }

echo "Gate G7.5 PASSED"
```

## Gate G7: Code Valid

### Comprehensive Checks

Gate G7 validates **categorical correctness**, **standardization**, AND **completeness**.

```bash
cd artifacts/v{N}/gen/python

# === EFFECTS MODULE (MANDATORY) ===
test -f src/domain/effects/__init__.py || { echo "FAIL: effects/__init__.py"; exit 1; }
test -f src/domain/effects/result.py || { echo "FAIL: effects/result.py"; exit 1; }
test -f src/domain/effects/app.py || { echo "FAIL: effects/app.py"; exit 1; }
test -d src/domain/effects/errors/ || { echo "FAIL: effects/errors/"; exit 1; }

# === DOMAIN TYPES ===
test -f src/domain/types/__init__.py || { echo "FAIL: types/__init__.py"; exit 1; }
test -f src/domain/interfaces/__init__.py || { echo "FAIL: interfaces/__init__.py"; exit 1; }

# === OPERATIONS CORRECTNESS ===
# Operations import from effects
grep -q "from.*effects import App" src/domain/operations/*.py || { echo "FAIL: Operations don't import App"; exit 1; }

# Operations return App[A]
grep -q "-> App\[" src/domain/operations/*.py || { echo "FAIL: Operations don't return App[A]"; exit 1; }

# No operations take repo as parameter
! grep -qE "def \w+\(.*repo.*Repository" src/domain/operations/*.py || { echo "FAIL: Operations take repo as param"; exit 1; }

# === API LAYER (if enabled) ===
if grep -q "api:.*enabled: true" ../../targets.yaml 2>/dev/null; then
    # API schemas exist
    test -f src/api/schemas/__init__.py || { echo "FAIL: api/schemas/__init__.py"; exit 1; }
    test -f src/api/schemas/requests.py || { echo "FAIL: api/schemas/requests.py"; exit 1; }
    test -f src/api/schemas/responses.py || { echo "FAIL: api/schemas/responses.py"; exit 1; }
    
    # Handlers exist
    test -d src/api/handlers || { echo "FAIL: api/handlers/"; exit 1; }
    ls src/api/handlers/*.py >/dev/null 2>&1 || { echo "FAIL: No handler files"; exit 1; }
    
    # Handlers use Env dependency
    grep -q "env: Env = Depends" src/api/handlers/*.py || { echo "FAIL: Handlers don't use Env"; exit 1; }
    
    # Handlers use StandardResponse
    grep -q "StandardResponse" src/api/handlers/*.py || { echo "FAIL: Handlers don't use StandardResponse"; exit 1; }
    
    # dependencies.py exists with get_env
    test -f src/api/dependencies.py || { echo "FAIL: api/dependencies.py"; exit 1; }
    grep -q "def get_env" src/api/dependencies.py || { echo "FAIL: get_env not defined"; exit 1; }
fi

# === STORAGE LAYER (if enabled) ===
if grep -q "persistence:.*enabled: true" ../../targets.yaml 2>/dev/null; then
    # Storage models exist
    test -d src/storage/models || { echo "FAIL: storage/models/"; exit 1; }
    ls src/storage/models/*.py >/dev/null 2>&1 || { echo "FAIL: No model files"; exit 1; }
    
    # Storage repositories exist
    test -d src/storage/repositories || { echo "FAIL: storage/repositories/"; exit 1; }
    ls src/storage/repositories/*.py >/dev/null 2>&1 || { echo "FAIL: No repository files"; exit 1; }
    
    # Database config exists
    test -f src/storage/database.py || { echo "FAIL: storage/database.py"; exit 1; }
    
    # Repositories implement protocols
    for repo in src/storage/repositories/*.py; do
        [ "$repo" = "src/storage/repositories/__init__.py" ] && continue
        grep -q "class.*Repository" "$repo" || { echo "FAIL: $repo missing Repository class"; exit 1; }
    done
fi

# === STANDARDIZATION APPLIED ===
test -f src/middleware/error_handler.py || { echo "FAIL: middleware/error_handler.py"; exit 1; }
test -f src/middleware/request_id.py || { echo "FAIL: middleware/request_id.py"; exit 1; }
test -f src/middleware/setup.py || { echo "FAIL: middleware/setup.py"; exit 1; }

# main.py has middleware setup
grep -q "setup_middleware" src/main.py || { echo "FAIL: main.py missing setup_middleware"; exit 1; }

# === COMPLETENESS CHECK ===
# Count expected vs actual (from category.yaml)
EXPECTED_MORPHISMS=$(grep -c "name:" ../../build/category.yaml 2>/dev/null || echo 0)
ACTUAL_OPERATIONS=$(grep -c "^def " src/domain/operations/*.py 2>/dev/null || echo 0)

if [ "$ACTUAL_OPERATIONS" -lt "$EXPECTED_MORPHISMS" ]; then
    echo "WARNING: Possible incomplete generation - $ACTUAL_OPERATIONS operations vs $EXPECTED_MORPHISMS morphisms"
fi

# === ENVIRONMENT VARIABLE PARITY ===
test -f .env.example || { echo "FAIL: .env.example missing"; exit 1; }

python3 << 'EOF'
import re
import sys

# Extract from config.py
with open("src/config.py") as f:
    config = f.read()

config_vars = set()
for match in re.finditer(r'^\s+(\w+):\s*\w+', config, re.MULTILINE):
    var = match.group(1).upper()
    if var not in ('CONFIG', 'CLASS'):
        config_vars.add(var)

# Extract from docker-compose.yaml
with open("docker-compose.yaml") as f:
    compose = f.read()

compose_vars = set()
for match in re.finditer(r'- ([A-Z_]+)=', compose):
    compose_vars.add(match.group(1))
for match in re.finditer(r'\$\{([A-Z_]+)', compose):
    compose_vars.add(match.group(1))

# Extract from .env.example
with open(".env.example") as f:
    env = f.read()

env_vars = set()
for line in env.splitlines():
    if line and not line.startswith('#') and '=' in line:
        env_vars.add(line.split('=')[0])

# Check parity
missing_compose = config_vars - compose_vars
missing_env = config_vars - env_vars

errors = []
for var in missing_compose:
    errors.append(f"ENV PARITY: {var} missing from docker-compose.yaml")
for var in missing_env:
    errors.append(f"ENV PARITY: {var} missing from .env.example")

if errors:
    print('\n'.join(errors))
    sys.exit(1)
EOF

# === IMPORTS WORK ===
python -c "from src.domain.effects import App, Env" || { echo "FAIL: Cannot import App, Env"; exit 1; }
python -c "from src.domain.effects.result import Result, ok, err" || { echo "FAIL: Cannot import Result"; exit 1; }
python -c "from src.domain.operations import *" || { echo "FAIL: Cannot import operations"; exit 1; }
python -c "from src.middleware.setup import setup_middleware" || { echo "FAIL: Cannot import setup_middleware"; exit 1; }
python -c "from src.main import create_app" || { echo "FAIL: Cannot import create_app"; exit 1; }

# === INFRASTRUCTURE ===
docker-compose config >/dev/null || { echo "FAIL: Invalid docker-compose.yaml"; exit 1; }

echo "Gate G7 PASSED"
```
    compose_vars.add(match.group(1))

# Extract from .env.example
with open(".env.example") as f:
    env = f.read()

env_vars = set()
for line in env.splitlines():
    if line and not line.startswith('#') and '=' in line:
        env_vars.add(line.split('=')[0])

# Check parity
missing_compose = config_vars - compose_vars
missing_env = config_vars - env_vars

errors = []
for var in missing_compose:
    errors.append(f"ENV PARITY: {var} missing from docker-compose.yaml")
for var in missing_env:
    errors.append(f"ENV PARITY: {var} missing from .env.example")

if errors:
    print('\n'.join(errors))
    sys.exit(1)
EOF

# === IMPORTS WORK ===
python -c "from src.domain.effects import App, Env"
python -c "from src.domain.effects.result import Result, ok, err"
python -c "from src.domain.operations import *"
python -c "from src.middleware.setup import setup_middleware"
python -c "from src.main import create_app"

# === INFRASTRUCTURE ===
docker-compose config
```

### Validation Function

```python
def validate_gate_g7(gen_dir: str, targets: dict) -> GateResult:
    errors = []
    warnings = []
    
    # === EFFECTS MODULE (CRITICAL) ===
    effects_files = [
        "src/domain/effects/__init__.py",
        "src/domain/effects/result.py",
        "src/domain/effects/app.py",
        "src/domain/effects/errors/__init__.py",
    ]
    for f in effects_files:
        if not file_exists(f"{gen_dir}/{f}"):
            errors.append(f"CRITICAL: Missing effects file {f}")
    
    if errors:
        return GateResult(passed=False, errors=errors)
    
    # === CATEGORICAL CORRECTNESS ===
    
    # Operations return App[A]
    for op_file in glob(f"{gen_dir}/src/domain/operations/*.py"):
        if "__init__" in op_file:
            continue
        content = read_file(op_file)
        
        # Find function definitions
        for match in re.finditer(r"def (\w+)\([^)]*\)\s*->\s*([^:]+):", content):
            func_name, return_type = match.groups()
            if func_name.startswith("_"):
                continue
            if "App[" not in return_type and "Result[" not in return_type:
                errors.append(
                    f"{op_file}: {func_name} returns {return_type}, not App[A]"
                )
    
    # No repo parameters
    for op_file in glob(f"{gen_dir}/src/domain/operations/*.py"):
        content = read_file(op_file)
        if re.search(r"def \w+\([^)]*repo\s*:", content):
            errors.append(f"{op_file}: takes repo parameter instead of using Env")
    
    # === HANDLERS CORRECTNESS ===
    
    for handler_file in glob(f"{gen_dir}/src/api/handlers/*.py"):
        if "__init__" in handler_file:
            continue
        content = read_file(handler_file)
        
        # Check Env dependency
        if "async def " in content:
            if "Depends(get_env)" not in content:
                errors.append(f"{handler_file}: handlers don't use Env dependency")
            
            # Check StandardResponse (unless it's returning directly to error middleware)
            if "StandardResponse" not in content and "raise " not in content:
                warnings.append(f"{handler_file}: consider using StandardResponse")
    
    # === STANDARDIZATION ===
    
    middleware_files = [
        "src/middleware/__init__.py",
        "src/middleware/error_handler.py",
        "src/middleware/setup.py",
    ]
    for f in middleware_files:
        if not file_exists(f"{gen_dir}/{f}"):
            errors.append(f"Missing middleware file: {f}")
    
    # Check main.py setup
    if file_exists(f"{gen_dir}/src/main.py"):
        main_content = read_file(f"{gen_dir}/src/main.py")
        if "setup_middleware" not in main_content:
            errors.append("main.py: missing setup_middleware call")
    
    # === IMPORTS ===
    
    import_checks = [
        "from src.domain.effects import App, Env",
        "from src.domain.effects.result import Result, ok, err",
        "from src.middleware.setup import setup_middleware",
    ]
    for check in import_checks:
        result = run_command(f"cd {gen_dir} && python -c '{check}'")
        if result.exit_code != 0:
            errors.append(f"Import failed: {check}\n{result.stderr}")
    
    # === INFRASTRUCTURE ===
    
    topology = targets["targets"]["topology"]["style"]
    if topology != "library":
        if not file_exists(f"{gen_dir}/src/main.py"):
            errors.append("Missing main.py")
        
        if not file_exists(f"{gen_dir}/Dockerfile"):
            errors.append("Missing Dockerfile")
        
        if file_exists(f"{gen_dir}/docker-compose.yaml"):
            result = run_command(f"cd {gen_dir} && docker-compose config")
            if result.exit_code != 0:
                errors.append(f"Invalid docker-compose: {result.stderr}")
    
    # === ENVIRONMENT VARIABLE PARITY ===
    
    # Extract vars from config.py
    config_path = f"{gen_dir}/src/config.py"
    if file_exists(config_path):
        config_content = read_file(config_path)
        config_vars = extract_config_vars(config_content)
        
        # Check docker-compose.yaml
        compose_path = f"{gen_dir}/docker-compose.yaml"
        if file_exists(compose_path):
            compose = load_yaml(compose_path)
            compose_vars = extract_compose_env_vars(compose)
            
            missing = set(config_vars.keys()) - compose_vars
            for var in missing:
                errors.append(f"ENV PARITY: {var} in config.py but missing from docker-compose.yaml")
        
        # Check .env.example
        env_path = f"{gen_dir}/.env.example"
        if file_exists(env_path):
            env_content = read_file(env_path)
            env_vars = extract_env_example_vars(env_content)
            
            missing = set(config_vars.keys()) - env_vars
            for var in missing:
                errors.append(f"ENV PARITY: {var} in config.py but missing from .env.example")
        else:
            errors.append("Missing .env.example file")
    
    return GateResult(
        passed=len(errors) == 0,
        errors=errors,
        warnings=warnings
    )
```

## Output Structure

```
gen/
├── maps/                        # Code maps (verifiable)
│   ├── operations/
│   │   ├── user_ops.map.yaml
│   │   └── auth_ops.map.yaml
│   ├── handlers/
│   │   ├── user_handlers.map.yaml
│   │   └── auth_handlers.map.yaml
│   └── repositories/
│       └── interfaces.map.yaml
├── maps-verification.yaml       # Verification result (must be PASS)
├── standardization-report.yaml  # Standards applied
└── python/
    ├── src/
    │   ├── __init__.py
    │   ├── main.py
    │   ├── container.py
    │   ├── config.py
    │   ├── domain/
    │   │   ├── __init__.py
    │   │   ├── effects/           # Generated FIRST
    │   │   │   ├── __init__.py
    │   │   │   ├── result.py      # Either/Result type
    │   │   │   ├── app.py         # App monad
    │   │   │   └── errors/
    │   │   │       ├── __init__.py
    │   │   │       ├── base.py
    │   │   │       └── {module}.py
    │   │   ├── types/
    │   │   │   ├── __init__.py
    │   │   │   ├── ids.py
    │   │   │   ├── user.py
    │   │   │   └── value_objects.py
    │   │   ├── interfaces/        # Repository protocols
    │   │   │   ├── __init__.py
    │   │   │   └── repositories.py
    │   │   └── operations/        # From verified maps
    │   │       ├── __init__.py
    │   │       ├── user_ops.py
    │   │       └── pure.py
    │   ├── api/                   # If targets.api.enabled
    │   │   ├── __init__.py
    │   │   ├── dependencies.py    # get_env provider (CRITICAL)
    │   │   ├── schemas/
    │   │   │   ├── requests.py
    │   │   │   └── responses.py
    │   │   └── handlers/
    │   │       └── user_handlers.py
    │   ├── storage/               # If targets.persistence.enabled
    │   │   ├── __init__.py
    │   │   ├── database.py
    │   │   ├── models/
    │   │   │   └── user_model.py
    │   │   └── repositories/
    │   │       └── user_repository.py
    │   └── middleware/            # From apply-standards
    │       ├── __init__.py
    │       ├── error_handler.py
    │       ├── request_id.py
    │       ├── auth.py
    │       ├── response.py
    │       └── setup.py
    ├── Dockerfile
    ├── docker-compose.yaml
    ├── pyproject.toml
    └── .env.example
```

## Manifest Files

### types-manifest.yaml

```yaml
version: "1.0"
language: python
files:
  - path: "src/domain/types/user.py"
    objects: ["User", "UserId", "UserStatus"]
    traces_to: ["spec/objects.yaml#User"]
  - path: "src/domain/effects/errors.py"
    objects: ["UserError", "ValidationError"]
    traces_to: ["spec/effects.yaml#error_types"]
```

### morphisms-manifest.yaml

```yaml
version: "1.0"
files:
  - path: "src/domain/operations/user_operations.py"
    morphisms: ["create_user", "get_user", "update_user"]
    traces_to: ["spec/morphisms.yaml"]
  - path: "src/api/routes/users.py"
    morphisms: ["POST /users", "GET /users/{id}"]
    functor: "F_api"
```

### wiring-manifest.yaml

```yaml
version: "1.0"
topology: monolith
entry_points:
  - path: "src/main.py"
    type: application
files:
  - "src/main.py"
  - "src/container.py"
  - "Dockerfile"
  - "docker-compose.yaml"
transformations_applied:
  order: ["logging", "auth", "validation", "timeout"]
```

## Error Recovery

### Import Failed

```
Gate G7 Error: Import failed
  ModuleNotFoundError: No module named 'src.domain.types.user'

Fix:
  1. Verify src/domain/types/user.py exists
  2. Verify __init__.py files exist in all packages
  3. Check for syntax errors: python -m py_compile src/domain/types/user.py
```

### Missing Entry Point

```
Gate G7 Error: Missing main.py entry point

Fix:
  1. Run gen-wiring skill
  2. Verify topology is not 'library' (libraries don't have main.py)
```

### Docker Compose Invalid

```
Gate G7 Error: Invalid docker-compose
  services.db.depends_on contains undefined service app

Fix:
  1. Check docker-compose.yaml service definitions
  2. Ensure all referenced services exist
  3. Verify service names match
```

## Smoke Test

After Gate G7 passes, run smoke test:

```bash
cd artifacts/v{N}/gen/python

# Build
docker-compose build

# Start
docker-compose up -d

# Health check
curl http://localhost:8000/health

# Cleanup
docker-compose down
```

## When to Re-run

Re-run gen phase when:
- Build artifacts change (after verify passes)
- Targets configuration changes
- Fixing code generation errors
- Changing language or framework

Gen phase is the final phase - success means runnable system.
