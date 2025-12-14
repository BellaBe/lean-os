---
name: lean-os-spec
description: |
  Spec phase agent. Extracts categorical structure from requirements.
  Runs: spec-objects, spec-morphisms, spec-effects, spec-constraints.
  Validates: Gate G1 (all 4 outputs exist and cross-reference correctly).
skills: spec-objects, spec-morphisms, spec-effects, spec-constraints
model: opus
---

# Spec Phase Agent

Extract categorical structure from requirements.

## Purpose

Transform natural language requirements into formal categorical specification.

## Skills

| Skill | Output | Depends On |
|-------|--------|------------|
| spec-objects | objects.yaml | requirements |
| spec-morphisms | morphisms.yaml | objects.yaml |
| spec-effects | effects.yaml | morphisms.yaml |
| spec-constraints | constraints.yaml | objects, morphisms, effects |

## Execution Order

```
requirements
     │
     ├─→ [spec-objects] ─→ objects.yaml
     │         │
     │         ↓
     ├─→ [spec-morphisms] ─→ morphisms.yaml
     │         │
     │         ↓
     ├─→ [spec-effects] ─→ effects.yaml
     │         │
     │         ↓
     └─→ [spec-constraints] ─→ constraints.yaml
                │
                ↓
           Gate G1
```

## Process

```python
def run_spec_phase(requirements: str) -> GateResult:
    # 1. Extract objects (types)
    objects = run_skill("spec-objects", requirements)
    write_yaml("spec/objects.yaml", objects)
    
    # 2. Extract morphisms (operations)
    # Needs objects for domain/codomain references
    morphisms = run_skill("spec-morphisms", requirements, objects)
    write_yaml("spec/morphisms.yaml", morphisms)
    
    # 3. Extract effects (error types, monads)
    # Needs morphisms to know which effects are used
    effects = run_skill("spec-effects", requirements, morphisms)
    write_yaml("spec/effects.yaml", effects)
    
    # 4. Extract constraints (invariants, laws)
    # Needs all previous for scope references
    constraints = run_skill("spec-constraints", requirements, objects, morphisms, effects)
    write_yaml("spec/constraints.yaml", constraints)
    
    # 5. Validate Gate G1
    return validate_gate_g1()
```

## Gate G1: Spec Completeness

### Checks

```bash
# 1. All files exist
ls artifacts/v{N}/spec/objects.yaml
ls artifacts/v{N}/spec/morphisms.yaml
ls artifacts/v{N}/spec/effects.yaml
ls artifacts/v{N}/spec/constraints.yaml

# 2. YAML is valid
python -c "import yaml; yaml.safe_load(open('spec/objects.yaml'))"
python -c "import yaml; yaml.safe_load(open('spec/morphisms.yaml'))"
python -c "import yaml; yaml.safe_load(open('spec/effects.yaml'))"
python -c "import yaml; yaml.safe_load(open('spec/constraints.yaml'))"
```

### Cross-Reference Validation

```python
def validate_gate_g1() -> GateResult:
    errors = []
    
    objects = load_yaml("spec/objects.yaml")
    morphisms = load_yaml("spec/morphisms.yaml")
    effects = load_yaml("spec/effects.yaml")
    constraints = load_yaml("spec/constraints.yaml")
    
    object_ids = {o["id"] for o in objects["objects"]}
    morphism_ids = {m["id"] for m in morphisms["morphisms"]}
    effect_ids = {e["id"] for e in effects["effects"]}
    
    # Check morphism references
    for m in morphisms["morphisms"]:
        if m["domain"] not in object_ids:
            errors.append(f"Morphism {m['id']}: unknown domain {m['domain']}")
        if m["codomain"] not in object_ids:
            errors.append(f"Morphism {m['id']}: unknown codomain {m['codomain']}")
        if not m["generator"]:
            for ref in m["composed_of"]:
                if ref not in morphism_ids:
                    errors.append(f"Morphism {m['id']}: unknown composition ref {ref}")
    
    # Check constraint scopes
    for c in constraints["constraints"]:
        if c["scope"] not in object_ids and c["scope"] not in morphism_ids:
            errors.append(f"Constraint {c['id']}: unknown scope {c['scope']}")
    
    if errors:
        return GateResult(passed=False, errors=errors)
    return GateResult(passed=True)
```

## Output Structure

```yaml
# spec/objects.yaml
version: "1.0"
objects:
  - id: "UserId"
    kind: primitive
    definition:
      base: "UUID"
    # ...

# spec/morphisms.yaml
version: "1.0"
morphisms:
  - id: "create_user"
    domain: "CreateUserInput"
    codomain: "User"
    effects: ["IO", "Either[UserError, _]"]
    generator: true
    # ...

# spec/effects.yaml
version: "1.0"
effects:
  - id: "IO"
    kind: io
    # ...
error_types:
  - id: "UserError"
    variants:
      - name: "NotFound"
        # ...

# spec/constraints.yaml
version: "1.0"
constraints:
  - id: "positive_money"
    kind: invariant
    scope: "Money"
    expression: "value >= 0"
    proof_obligation: true
    # ...
```

## Error Recovery

### Missing Object Reference

```
Error: Morphism create_user: unknown domain CreateUserInput

Fix: Add CreateUserInput to spec/objects.yaml
```

### Missing Morphism in Composition

```
Error: Morphism register_user: unknown composition ref validate_input

Fix: Either:
  1. Add validate_input as generator morphism
  2. Remove from composed_of if not needed
```

### Invalid Constraint Scope

```
Error: Constraint user_active: unknown scope check_status

Fix: Verify constraint references existing object or morphism
```

## When to Re-run

Re-run spec phase when:
- Requirements change
- Adding new types or operations
- Fixing reference errors
- Refactoring domain model

After re-run, must also re-run: build → verify → gen
