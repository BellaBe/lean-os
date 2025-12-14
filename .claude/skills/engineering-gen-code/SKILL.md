---
name: gen-code
description: |
  Generate actual source code from verified code maps. This skill only runs
  AFTER verify-maps passes. Code is generated mechanically from maps, ensuring
  correctness. Use when: code maps are verified, generating final source files.
---

# Gen Code

Generate source code from verified code maps.

## Prerequisites

**MUST have passed:**
- gen-types (effects module exists)
- gen-maps (maps generated)
- verify-maps (maps verified, status: PASS)

**DO NOT run if verify-maps failed.**

## Input

- `artifacts/v{N}/gen/maps/*.map.yaml` — Verified code maps
- `artifacts/v{N}/gen/maps-verification.yaml` — Must show `status: PASS`

## Output

- `artifacts/v{N}/gen/python/src/domain/operations/*.py`
- `artifacts/v{N}/gen/python/src/domain/workflows/*.py`
- `artifacts/v{N}/gen/python/src/api/handlers/*.py`

## Process

Code generation is MECHANICAL — maps dictate exactly what to generate.

### Step 1: Check Verification Status

```python
verification = load_yaml("gen/maps-verification.yaml")
if verification["status"] != "PASS":
    raise Error("Cannot generate code: maps verification failed")
```

### Step 2: Generate Operations

For each `maps/operations/*.map.yaml`:

```python
def generate_operation_file(map_data: dict) -> str:
    """
    Generate Python source from operation map.
    """
    lines = []
    
    # Generate imports (from map)
    lines.append('"""')
    lines.append(f'{map_data["module"].split(".")[-1]} operations.')
    lines.append('')
    lines.append('Generated from verified code map. Do not edit directly.')
    lines.append('"""')
    
    for imp in map_data["imports"]:
        if imp.get("from"):
            names = ", ".join(imp["names"])
            lines.append(f'from {imp["from"]} import {names}')
        else:
            lines.append(f'import {imp["names"][0]}')
    
    lines.append('')
    lines.append('')
    
    # Generate each function
    for func in map_data["functions"]:
        lines.extend(generate_function(func))
        lines.append('')
        lines.append('')
    
    return '\n'.join(lines)


def generate_function(func: dict) -> List[str]:
    """
    Generate function from map specification.
    """
    lines = []
    
    # Signature
    params = ', '.join(
        f'{p["name"]}: {p["type"]}'
        for p in func["signature"]["params"]
    )
    returns = func["signature"]["returns"]
    
    lines.append(f'def {func["name"]}({params}) -> {returns}:')
    
    # Docstring
    lines.append('    """')
    if "traces_to" in func:
        lines.append(f'    Spec: {func["traces_to"]}')
    lines.append('    """')
    
    # Inner async function for App monad
    lines.append('    async def _run(env: Env) -> Result[AppError, ...]')
    
    # Env access
    for access in func.get("env_access", []):
        alias = access.get("alias", access["path"].split(".")[-1])
        lines.append(f'        {alias} = {access["path"]}')
    
    lines.append('')
    
    # Body steps
    for step in func["body"]["steps"]:
        lines.extend(generate_step(step, indent=8))
    
    lines.append('')
    lines.append('    return App(_run)')
    
    return lines


def generate_step(step: dict, indent: int) -> List[str]:
    """
    Generate code for a single step.
    """
    pad = ' ' * indent
    lines = []
    
    if step["action"] == "call":
        # Method call
        args = ', '.join(
            arg["value"] for arg in step.get("args", [])
        )
        call = f'{step["target"]}({args})'
        
        if step.get("returns", {}).get("bind"):
            bind = step["returns"]["bind"]
            lines.append(f'{pad}{bind} = await {call}')
        else:
            lines.append(f'{pad}await {call}')
    
    elif step["action"] == "condition":
        lines.append(f'{pad}if {step["test"]}:')
        if step["if_true"]["action"] == "return":
            lines.append(f'{pad}    return {step["if_true"]["value"]}')
    
    elif step["action"] == "construct":
        args_lines = []
        for k, v in step["args"].items():
            args_lines.append(f'{k}={v}')
        args_str = ', '.join(args_lines)
        
        if step.get("bind"):
            lines.append(f'{pad}{step["bind"]} = {step["type"]}({args_str})')
        else:
            lines.append(f'{pad}{step["type"]}({args_str})')
    
    elif step["action"] == "return":
        lines.append(f'{pad}return {step["value"]}')
    
    elif step["action"] == "match":
        lines.append(f'{pad}match {step["on"]}:')
        for case in step["cases"]:
            lines.append(f'{pad}    case {case["pattern"]}:')
            for sub_step in [case["body"]]:
                lines.extend(generate_step(sub_step, indent + 8))
    
    return lines
```

### Step 3: Generate Handlers

For each `maps/handlers/*.map.yaml`:

```python
def generate_handler_file(map_data: dict) -> str:
    """
    Generate API handler file from map.
    """
    lines = []
    
    # Imports
    for imp in map_data["imports"]:
        names = ", ".join(imp["names"])
        lines.append(f'from {imp["from"]} import {names}')
    
    lines.append('')
    lines.append('')
    
    # Router
    router = map_data["router"]
    lines.append(f'router = APIRouter(prefix="{router["prefix"]}", tags={router["tags"]})')
    lines.append('')
    lines.append('')
    
    # Endpoints
    for endpoint in map_data["endpoints"]:
        lines.extend(generate_endpoint(endpoint))
        lines.append('')
        lines.append('')
    
    return '\n'.join(lines)


def generate_endpoint(endpoint: dict) -> List[str]:
    """
    Generate endpoint handler from map.
    """
    lines = []
    
    # Decorator
    lines.append(f'@{endpoint["decorator"]}')
    
    # Signature
    params = []
    for p in endpoint["signature"]["params"]:
        if p.get("default"):
            params.append(f'{p["name"]}: {p["type"]} = {p["default"]}')
        else:
            params.append(f'{p["name"]}: {p["type"]}')
    
    params_str = ', '.join(params)
    returns = endpoint["signature"]["returns"]
    
    lines.append(f'async def {endpoint["name"]}({params_str}) -> {returns}:')
    
    # Docstring
    lines.append('    """')
    if "traces_to" in endpoint:
        lines.append(f'    Functor: {endpoint["traces_to"]}')
    lines.append('    """')
    
    # Body
    for step in endpoint["body"]["steps"]:
        lines.extend(generate_step(step, indent=4))
    
    return lines
```

### Step 4: Generate Repository Implementations

For each repository protocol, generate SQLAlchemy implementation:

```python
def generate_repository_impl(protocol_map: dict, model_info: dict) -> str:
    """
    Generate concrete repository from protocol map.
    """
    lines = []
    
    protocol_name = protocol_map["name"]  # e.g., "UserRepository"
    impl_name = f"Sql{protocol_name}"     # e.g., "SqlUserRepository"
    
    lines.append(f'class {impl_name}({protocol_name}):')
    lines.append(f'    """SQLAlchemy implementation of {protocol_name}."""')
    lines.append('')
    lines.append('    def __init__(self, session: AsyncSession) -> None:')
    lines.append('        self._session = session')
    lines.append('')
    
    for method in protocol_map["methods"]:
        lines.extend(generate_repo_method(method, model_info))
        lines.append('')
    
    return '\n'.join(lines)
```

## Generated Code Quality

Since maps are verified, generated code is guaranteed:

1. **Correct imports** — Every used name is imported
2. **Correct calls** — Every call matches its target signature
3. **Correct types** — Every variable has verified type
4. **No unused code** — Every import/binding is used

## Output Validation

After generation, verify code compiles:

```bash
cd gen/python

# Syntax check all files
find src -name "*.py" -exec python -m py_compile {} \;

# Import check
python -c "from src.domain.operations import *"
python -c "from src.api.handlers import *"
```

## File Structure Generated

```
gen/python/src/
├── domain/
│   ├── operations/
│   │   ├── __init__.py
│   │   ├── user_ops.py      ← from maps/operations/user_ops.map.yaml
│   │   ├── auth_ops.py      ← from maps/operations/auth_ops.map.yaml
│   │   └── pure.py          ← from maps/operations/pure.map.yaml
│   └── workflows/
│       ├── __init__.py
│       └── registration.py  ← from maps/workflows/registration.map.yaml
└── api/
    └── handlers/
        ├── __init__.py
        ├── user_handlers.py ← from maps/handlers/user_handlers.map.yaml
        └── auth_handlers.py ← from maps/handlers/auth_handlers.map.yaml
```

## Traceability

Every generated file includes:
1. Source map reference in docstring
2. Spec reference for each function
3. "Generated from verified code map" notice

```python
"""
user_ops operations.

Generated from verified code map. Do not edit directly.
Source: maps/operations/user_ops.map.yaml
"""

def create_user(input: CreateUserInput) -> App[User]:
    """
    Spec: build/category.yaml#morphisms.create_user
    """
    ...
```

## Do NOT

- **Run without verification** — Check maps-verification.yaml status first
- **Modify generated code** — Modify maps and regenerate instead
- **Add manual code** — Everything comes from maps
- **Skip import generation** — Maps specify exact imports needed
