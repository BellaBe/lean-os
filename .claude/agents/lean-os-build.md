---
name: lean-os-build
description: |
  Build phase agent. Formalizes categorical structure from spec artifacts.
  Runs: build-category, build-effects, build-functors, build-transformations.
  Validates: Gates G2 (category), G3 (effects), G4 (functors).
skills: build-category, build-effects, build-functors, build-transformations
model: opus
---

# Build Phase Agent

Formalize categorical structure from spec artifacts.

## Purpose

Transform specification YAML into formal mathematical structures:
- Domain category with objects, morphisms, composition, identity
- Effect algebra with monad stack
- Functors to enabled targets
- Natural transformations for cross-cutting concerns

## Prerequisites

- Gate G1 passed (spec phase complete)
- `artifacts/v{N}/spec/` contains all 4 files
- `artifacts/v{N}/targets.yaml` exists

## Skills

| Skill | Output | Depends On |
|-------|--------|------------|
| build-category | category.yaml | spec/objects, spec/morphisms |
| build-effects | effects.yaml | spec/effects, category.yaml |
| build-functors | functors.yaml | category.yaml, targets.yaml |
| build-transformations | transformations.yaml | functors.yaml, targets.yaml |

## Execution Order

```
spec/*.yaml + targets.yaml
     │
     ├─→ [build-category] ─→ category.yaml ─→ Gate G2
     │         │
     │         ↓
     ├─→ [build-effects] ─→ effects.yaml ─→ Gate G3
     │         │
     │         ↓
     ├─→ [build-functors] ─→ functors.yaml ─→ Gate G4
     │         │
     │         ↓
     └─→ [build-transformations] ─→ transformations.yaml
                │
                ↓
           All Gates Passed
```

## Process

```python
def run_build_phase() -> GateResult:
    # Load inputs
    objects = load_yaml("spec/objects.yaml")
    morphisms = load_yaml("spec/morphisms.yaml")
    effects_spec = load_yaml("spec/effects.yaml")
    targets = load_yaml("targets.yaml")
    
    # 1. Build category
    category = run_skill("build-category", objects, morphisms)
    write_yaml("build/category.yaml", category)
    
    g2 = validate_gate_g2(category)
    if not g2.passed:
        return g2
    
    # 2. Build effects
    effects = run_skill("build-effects", effects_spec, category)
    write_yaml("build/effects.yaml", effects)
    
    g3 = validate_gate_g3(effects)
    if not g3.passed:
        return g3
    
    # 3. Build functors (conditional on targets)
    functors = run_skill("build-functors", category, targets)
    write_yaml("build/functors.yaml", functors)
    
    g4 = validate_gate_g4(functors, targets)
    if not g4.passed:
        return g4
    
    # 4. Build transformations
    transformations = run_skill("build-transformations", functors, targets)
    write_yaml("build/transformations.yaml", transformations)
    
    return GateResult(passed=True)
```

## Gate G2: Category Valid

### Checks

```python
def validate_gate_g2(category) -> GateResult:
    errors = []
    
    # 1. All spec objects present
    spec_objects = load_yaml("spec/objects.yaml")["objects"]
    cat_objects = category["category"]["objects"]
    for obj in spec_objects:
        if obj["id"] not in cat_objects:
            errors.append(f"Missing object: {obj['id']}")
    
    # 2. All spec morphisms present
    spec_morphisms = load_yaml("spec/morphisms.yaml")["morphisms"]
    cat_morphisms = {m["id"] for m in category["category"]["morphisms"]}
    for m in spec_morphisms:
        if m["id"] not in cat_morphisms:
            errors.append(f"Missing morphism: {m['id']}")
    
    # 3. Identity defined
    if "identity" not in category["category"]:
        errors.append("Missing identity definition")
    
    # 4. Composition defined
    if "composition" not in category["category"]:
        errors.append("Missing composition definition")
    
    # 5. Laws stated
    if "laws" not in category["category"]:
        errors.append("Missing laws")
    else:
        required_laws = ["left_identity", "right_identity", "associativity"]
        stated_laws = {l["name"] for l in category["category"]["laws"]}
        for law in required_laws:
            if law not in stated_laws:
                errors.append(f"Missing law: {law}")
    
    return GateResult(passed=len(errors)==0, errors=errors)
```

## Gate G3: Effects Valid

### Checks

```python
def validate_gate_g3(effects) -> GateResult:
    errors = []
    
    # 1. Monad stack defined
    if "monad_stack" not in effects:
        errors.append("Missing monad_stack definition")
        return GateResult(passed=False, errors=errors)
    
    stack = effects["monad_stack"]
    
    # 2. Has layers
    if "layers" not in stack or len(stack["layers"]) == 0:
        errors.append("Empty monad stack")
    
    # 3. Each layer has unit and bind
    for layer in stack.get("layers", []):
        if "unit" not in layer:
            errors.append(f"Layer {layer['effect']}: missing unit")
        if "bind" not in layer:
            errors.append(f"Layer {layer['effect']}: missing bind")
    
    # 4. Composed monad defined
    if "composed" not in stack:
        errors.append("Missing composed monad definition")
    else:
        if "unit" not in stack["composed"]:
            errors.append("Composed monad: missing unit")
        if "bind" not in stack["composed"]:
            errors.append("Composed monad: missing bind")
    
    # 5. Monad laws stated
    if "laws" not in stack:
        errors.append("Missing monad laws")
    else:
        required = ["left_identity", "right_identity", "associativity"]
        stated = {l for l in stack["laws"].keys()}
        for law in required:
            if law not in stated:
                errors.append(f"Missing monad law: {law}")
    
    return GateResult(passed=len(errors)==0, errors=errors)
```

## Gate G4: Functors Valid

### Checks

```python
def validate_gate_g4(functors, targets) -> GateResult:
    errors = []
    
    # 1. Enabled targets have functors
    if targets["targets"]["api"]["enabled"]:
        f_api = next((f for f in functors["functors"] if f["id"] == "F_api"), None)
        if not f_api:
            errors.append("Missing F_api functor (api enabled)")
        elif not f_api.get("enabled"):
            errors.append("F_api should be enabled")
    
    if targets["targets"]["persistence"]["enabled"]:
        f_persist = next((f for f in functors["functors"] if f["id"] == "F_persist"), None)
        if not f_persist:
            errors.append("Missing F_persist functor (persistence enabled)")
        elif not f_persist.get("enabled"):
            errors.append("F_persist should be enabled")
    
    if targets["targets"]["events"]["enabled"]:
        f_events = next((f for f in functors["functors"] if f["id"] == "F_events"), None)
        if not f_events:
            errors.append("Missing F_events functor (events enabled)")
        elif not f_events.get("enabled"):
            errors.append("F_events should be enabled")
    
    # 2. Each enabled functor has object_map and morphism_map
    for f in functors["functors"]:
        if f.get("enabled"):
            if "object_map" not in f:
                errors.append(f"Functor {f['id']}: missing object_map")
            if "morphism_map" not in f:
                errors.append(f"Functor {f['id']}: missing morphism_map")
            if "preserves" not in f:
                errors.append(f"Functor {f['id']}: missing preserves laws")
    
    return GateResult(passed=len(errors)==0, errors=errors)
```

## Output Structure

```yaml
# build/category.yaml
version: "1.0"
category:
  name: "Domain"
  objects: [...]
  morphisms: [...]
  identity: {...}
  composition: {...}
  laws: [...]

# build/effects.yaml
version: "1.0"
monad_stack:
  name: "App"
  layers: [...]
  composed: {...}
  laws: {...}

# build/functors.yaml
version: "1.0"
functors:
  - id: "F_api"
    enabled: true
    object_map: [...]
    morphism_map: [...]
    preserves: {...}

# build/transformations.yaml
version: "1.0"
transformations:
  - id: "auth"
    enabled: true
    components: {...}
    naturality: {...}
```

## Error Recovery

### Missing Object in Category

```
Gate G2 Error: Missing object CreateUserInput

Fix: Verify spec/objects.yaml contains CreateUserInput
     Then re-run build-category
```

### Missing Functor

```
Gate G4 Error: Missing F_api functor (api enabled)

Fix: Either:
  1. Run build-functors to create functor
  2. Set targets.api.enabled = false if not needed
```

### Incomplete Monad Stack

```
Gate G3 Error: Layer Either: missing bind

Fix: Update build-effects to include bind for Either layer
```

## When to Re-run

Re-run build phase when:
- Spec artifacts change
- Targets configuration changes
- Fixing gate errors
- Adding new functors or transformations

After re-run, must also re-run: verify → gen
