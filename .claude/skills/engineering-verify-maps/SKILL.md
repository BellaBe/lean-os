---
name: verify-maps
description: |
  Verify code maps against type definitions. Catches type mismatches, wrong
  arguments, and missing imports BEFORE generating actual code. This is the
  fast-feedback loop that prevents broken code generation.
---

# Verify Maps

Static analysis of code maps to catch errors before code generation.

## Purpose

**The 300-line check:** Verify 300 lines of maps instead of debugging 5000 lines of broken code.

This skill:
1. Parses type definitions from gen-types output
2. Builds a symbol table
3. Verifies every call, construct, and import in code maps
4. Reports errors that would cause runtime failures

## Input

- `artifacts/v{N}/gen/python/src/domain/types/` — Type definitions
- `artifacts/v{N}/gen/python/src/domain/effects/` — Effect types
- `artifacts/v{N}/gen/python/src/domain/interfaces/` — Repository protocols
- `artifacts/v{N}/gen/maps/*.map.yaml` — Code maps to verify

## Output

- `artifacts/v{N}/gen/maps-verification.yaml` — Verification report
- Exit code 0 if all checks pass, 1 if any fail

## Verification Process

### Step 1: Build Symbol Table

Parse all generated type files to build a complete symbol table:

```python
# symbol_table.py
from dataclasses import dataclass
from typing import Dict, List, Optional
import ast

@dataclass
class TypeInfo:
    name: str
    kind: str  # dataclass, pydantic, enum, protocol, newtype
    fields: Dict[str, str]  # field_name -> type_string
    methods: Dict[str, "MethodInfo"]  # method_name -> info

@dataclass
class MethodInfo:
    name: str
    params: List[tuple[str, str]]  # [(name, type), ...]
    returns: str
    is_async: bool

def build_symbol_table(src_dir: str) -> Dict[str, TypeInfo]:
    """
    Parse all Python files and extract type information.
    """
    table = {}
    
    # Parse domain types
    for py_file in glob(f"{src_dir}/domain/types/*.py"):
        module_ast = ast.parse(read_file(py_file))
        for node in ast.walk(module_ast):
            if isinstance(node, ast.ClassDef):
                table[node.name] = extract_class_info(node)
            elif isinstance(node, ast.Assign):
                # Handle NewType
                if is_newtype(node):
                    table[get_newtype_name(node)] = TypeInfo(
                        name=get_newtype_name(node),
                        kind="newtype",
                        fields={},
                        methods={}
                    )
    
    # Parse effects
    for py_file in glob(f"{src_dir}/domain/effects/**/*.py"):
        module_ast = ast.parse(read_file(py_file))
        for node in ast.walk(module_ast):
            if isinstance(node, ast.ClassDef):
                table[node.name] = extract_class_info(node)
    
    # Parse interfaces
    for py_file in glob(f"{src_dir}/domain/interfaces/*.py"):
        module_ast = ast.parse(read_file(py_file))
        for node in ast.walk(module_ast):
            if isinstance(node, ast.ClassDef):
                table[node.name] = extract_protocol_info(node)
    
    return table
```

### Step 2: Verify Call Sites

For each call in a code map:

```python
def verify_call(call: dict, context: dict, symbol_table: dict) -> List[str]:
    """
    Verify a function/method call is valid.
    
    Returns list of errors (empty if valid).
    """
    errors = []
    
    target = call["target"]  # e.g., "repo.get_by_email"
    args = call["args"]      # e.g., [{"name": "email", "value": "input.email", "type": "str"}]
    
    # Resolve target
    if "." in target:
        obj_name, method_name = target.rsplit(".", 1)
        obj_type = context.get(obj_name)  # e.g., "UserRepository"
        
        if obj_type is None:
            errors.append(f"Unknown object: {obj_name}")
            return errors
        
        type_info = symbol_table.get(obj_type)
        if type_info is None:
            errors.append(f"Unknown type: {obj_type}")
            return errors
        
        method_info = type_info.methods.get(method_name)
        if method_info is None:
            errors.append(f"Type {obj_type} has no method {method_name}")
            return errors
    else:
        # Direct function call
        method_info = symbol_table.get(target)
        if method_info is None:
            errors.append(f"Unknown function: {target}")
            return errors
    
    # Verify argument count
    expected_params = method_info.params
    if len(args) != len(expected_params):
        errors.append(
            f"{target}: expected {len(expected_params)} args, got {len(args)}"
        )
        return errors
    
    # Verify argument types
    for arg, (param_name, param_type) in zip(args, expected_params):
        arg_type = arg["type"]
        if not types_compatible(arg_type, param_type):
            errors.append(
                f"{target}: arg {param_name} expected {param_type}, got {arg_type}"
            )
    
    return errors
```

### Step 3: Verify Field Access

```python
def verify_field_access(access: dict, symbol_table: dict) -> List[str]:
    """
    Verify that accessing a field on a type is valid.
    
    Prevents AttributeError at runtime by checking:
    1. Type exists in symbol table
    2. Type has the declared field
    3. Field has the expected type
    """
    errors = []
    
    var_type = access["type"]
    field_name = access["field"]
    expected_field_type = access["field_type"]
    
    # Get type info
    type_info = symbol_table.get(var_type)
    if type_info is None:
        errors.append(f"Unknown type: {var_type}")
        return errors
    
    # Check field exists
    if field_name not in type_info.fields:
        errors.append(
            f"Type {var_type} has no field '{field_name}'. "
            f"Available fields: {list(type_info.fields.keys())}"
        )
        return errors
    
    # Check field type matches
    actual_field_type = type_info.fields[field_name]
    if not types_compatible(actual_field_type, expected_field_type):
        errors.append(
            f"Field {var_type}.{field_name} has type {actual_field_type}, "
            f"expected {expected_field_type}"
        )
    
    return errors


def verify_all_field_accesses(func: dict, symbol_table: dict) -> List[str]:
    """
    Verify all declared field accesses in a function.
    """
    errors = []
    
    for access in func.get("field_accesses", []):
        access_errors = verify_field_access(access, symbol_table)
        for err in access_errors:
            errors.append(f"Function {func['name']}: {err}")
    
    # Also verify constructor field accesses
    for step in func.get("body", {}).get("steps", []):
        if step.get("action") == "construct":
            for field_access in step.get("constructor_field_accesses", []):
                type_name = step["type"]
                field_name = field_access["field"]
                expected_type = field_access["value_type"]
                
                type_info = symbol_table.get(type_name)
                if type_info is None:
                    errors.append(f"Unknown constructor type: {type_name}")
                    continue
                
                if field_name not in type_info.fields:
                    errors.append(
                        f"Constructor {type_name} has no field '{field_name}'"
                    )
                    continue
                
                actual_type = type_info.fields[field_name]
                if not types_compatible(expected_type, actual_type):
                    errors.append(
                        f"Constructor {type_name}.{field_name}: "
                        f"expected {actual_type}, got {expected_type}"
                    )
    
    return errors


def verify_undeclared_field_accesses(func: dict) -> List[str]:
    """
    Find field accesses in body that weren't declared in field_accesses.
    
    Catches: developer forgot to declare input.email but used it in body.
    """
    errors = []
    
    # Collect declared accesses
    declared = set()
    for access in func.get("field_accesses", []):
        declared.add(f"{access['variable']}.{access['field']}")
    
    # Find accesses used in body
    used = set()
    for step in func.get("body", {}).get("steps", []):
        # Check args
        for arg in step.get("args", []):
            value = arg.get("value", "")
            if "." in str(value) and not value.startswith("datetime."):
                # Looks like field access
                used.add(value)
        
        # Check construct args
        if step.get("action") == "construct":
            for field, value in step.get("args", {}).items():
                if "." in str(value) and not str(value).startswith("datetime."):
                    used.add(str(value))
    
    # Find undeclared
    undeclared = used - declared
    for access in undeclared:
        # Skip known safe patterns
        if any(access.startswith(p) for p in ["datetime.", "uuid.", "UserStatus."]):
            continue
        errors.append(
            f"Function {func['name']}: field access '{access}' used but not declared. "
            f"Add to field_accesses for verification."
        )
    
    return errors
```

### Step 4: Verify Imports Complete

```python
def verify_imports(map_data: dict) -> List[str]:
    """
    Verify all used names are imported.
    """
    errors = []
    
    # Collect all names used in the map
    used_names = set()
    for func in map_data.get("functions", []):
        # Signature types
        for param in func["signature"]["params"]:
            used_names.update(extract_type_names(param["type"]))
        used_names.update(extract_type_names(func["signature"]["returns"]))
        
        # Body
        for step in func["body"]["steps"]:
            if step["action"] == "call":
                for arg in step.get("args", []):
                    used_names.update(extract_type_names(arg["type"]))
            elif step["action"] == "construct":
                used_names.add(step["type"])
    
    # Collect imported names
    imported_names = set()
    for imp in map_data.get("imports", []):
        imported_names.update(imp["names"])
    
    # Check coverage
    missing = used_names - imported_names - BUILTINS
    for name in missing:
        errors.append(f"Used but not imported: {name}")
    
    # Check unused (warning, not error)
    unused = imported_names - used_names
    for name in unused:
        errors.append(f"WARNING: Imported but not used: {name}")
    
    return errors
```

### Step 5: Verify Env Access

```python
def verify_env_access(env_access: list, symbol_table: dict) -> List[str]:
    """
    Verify env access paths are valid.
    """
    errors = []
    
    # Get Env type
    env_type = symbol_table.get("Env")
    if env_type is None:
        errors.append("Env type not found in symbol table")
        return errors
    
    for access in env_access:
        path = access["path"]  # e.g., "env.repositories.users"
        expected_type = access["type"]  # e.g., "UserRepository"
        
        # Walk the path
        parts = path.split(".")
        current_type = "Env"
        
        for part in parts[1:]:  # Skip "env"
            type_info = symbol_table.get(current_type)
            if type_info is None:
                errors.append(f"Unknown type in path: {current_type}")
                break
            
            if part not in type_info.fields:
                errors.append(f"Type {current_type} has no field {part}")
                break
            
            current_type = type_info.fields[part]
        
        # Verify final type matches expected
        if current_type != expected_type:
            errors.append(
                f"Path {path} has type {current_type}, expected {expected_type}"
            )
    
    return errors
```

## Full Verification Algorithm

```python
def verify_all_maps(maps_dir: str, src_dir: str) -> VerificationResult:
    """
    Verify all code maps against symbol table.
    """
    # Build symbol table
    symbol_table = build_symbol_table(src_dir)
    
    all_errors = []
    all_warnings = []
    
    # Verify each map
    for map_file in glob(f"{maps_dir}/**/*.map.yaml"):
        map_data = load_yaml(map_file)
        
        for func in map_data.get("functions", []):
            # Build context for this function
            context = {}
            
            # Add env access to context
            for access in func.get("env_access", []):
                alias = access.get("alias", access["path"].split(".")[-1])
                context[alias] = access["type"]
            
            # Add params to context
            for param in func["signature"]["params"]:
                context[param["name"]] = param["type"]
            
            # Verify each step
            for step in func["body"]["steps"]:
                if step["action"] == "call":
                    errors = verify_call(step, context, symbol_table)
                    all_errors.extend(errors)
                    
                    # Add binding to context
                    if "bind" in step.get("returns", {}):
                        context[step["returns"]["bind"]] = step["returns"]["type"]
                
                elif step["action"] == "construct":
                    errors = verify_construct(step, symbol_table)
                    all_errors.extend(errors)
                    
                    if "bind" in step:
                        context[step["bind"]] = step["type"]
        
        # Verify imports
        import_errors = verify_imports(map_data)
        for err in import_errors:
            if err.startswith("WARNING:"):
                all_warnings.append(err)
            else:
                all_errors.append(err)
    
    return VerificationResult(
        passed=len(all_errors) == 0,
        errors=all_errors,
        warnings=all_warnings
    )
```

## Output Format

```yaml
# gen/maps-verification.yaml
version: "1.0"
status: PASS  # or FAIL

summary:
  maps_verified: 15
  total_functions: 42
  total_calls: 128
  errors: 0
  warnings: 2

errors: []

warnings:
  - file: maps/operations/user_ops.map.yaml
    function: create_user
    message: "Imported but not used: uuid4"

type_checks:
  - file: maps/operations/user_ops.map.yaml
    function: create_user
    checks:
      - call: "repo.get_by_email"
        status: PASS
        expected_args: [("email", "str")]
        actual_args: [("input.email", "str")]
      - call: "repo.save"
        status: PASS
        expected_args: [("user", "User")]
        actual_args: [("user", "User")]

env_checks:
  - file: maps/operations/user_ops.map.yaml
    function: create_user
    access: "env.repositories.users"
    expected_type: UserRepository
    actual_type: UserRepository
    status: PASS

import_checks:
  - file: maps/operations/user_ops.map.yaml
    status: PASS
    imported: 12
    used: 11
    missing: []
    unused: ["uuid4"]
```

## Gate Integration

This skill is Gate G7.5 — runs between gen-maps and gen-code:

```python
def gate_g7_5(gen_dir: str) -> GateResult:
    """
    Verify code maps before generating code.
    """
    result = verify_all_maps(
        maps_dir=f"{gen_dir}/maps",
        src_dir=f"{gen_dir}/python/src"
    )
    
    if not result.passed:
        return GateResult(
            passed=False,
            errors=result.errors,
            message="Code maps failed verification. Fix before generating code."
        )
    
    return GateResult(passed=True)
```

## Validation Commands

```bash
# Run verification
python -m lean_os.verify_maps artifacts/v1/gen/

# Check result
grep "status: PASS" artifacts/v1/gen/maps-verification.yaml || exit 1

# No errors
test $(grep -c "^  - " artifacts/v1/gen/maps-verification.yaml | grep "errors:") -eq 0
```

## Do NOT

- **Skip verification** — Maps MUST be verified before gen-code
- **Ignore errors** — Any error means gen-code will produce broken code
- **Trust map authors** — Always verify, even for hand-written maps
- **Generate code on FAIL** — Block gen-code until maps pass

## Library Integration

This skill has prescriptive tooling in `.claude/lib/leanos/`.

### Claude Usage (Direct Python API)

Claude calls library functions directly:

```python
from leanos.validators import (
    validate,
    build_symbol_table,
    ValidationResult,
)
from pathlib import Path

# Build symbol table from generated types
symbol_table = build_symbol_table(Path("gen/python/src/domain"))

# Validate all generated code
result = validate("gen/")

if not result.passed:
    for error in result.errors:
        print(f"ERROR: {error.file}: {error.message}")
    raise GateFailure("Maps verification failed", result.errors)

for warning in result.warnings:
    print(f"WARNING: {warning.file}: {warning.message}")
```

### Human/CI Usage (CLI)

```bash
# Verify code maps against types
leanos maps verify gen/maps/ gen/python/src/domain/types/

# Full validation of generated code
leanos validate gen/

# Output as JSON for CI
leanos validate gen/ --json
```

### What the Library Validates

1. **Field accesses** — Every `input.email` verified against type definition
2. **Call signatures** — Every `repo.save(user)` verified against protocol
3. **Return types** — Every function returns declared type
4. **Imports** — Every used name is imported
5. **Categorical patterns** — Operations return App[A], handlers use Env
