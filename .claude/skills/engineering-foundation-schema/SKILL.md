---
name: foundation-schema
description: |
  Manifest schema definitions for all LeanOS artifacts. Reference skill for
  validating manifest structure, understanding artifact formats, checking
  cross-references. Use when: validating outputs, debugging schema issues,
  understanding data flow between skills.
---

# Foundation Schema

Defines YAML schemas for all pipeline artifacts. This is a reference skill.

## Directory Structure

```
artifacts/v{N}/
├── spec/
│   ├── objects.yaml
│   ├── morphisms.yaml
│   ├── effects.yaml
│   └── constraints.yaml
├── build/
│   ├── category.yaml
│   ├── effects.yaml
│   ├── functors.yaml
│   └── transformations.yaml
├── verify/
│   ├── proofs/*.lean
│   ├── laws-report.yaml
│   ├── constraints-report.yaml
│   └── coverage-report.yaml
├── gen/
│   ├── {language}/src/
│   ├── types-manifest.yaml
│   ├── morphisms-manifest.yaml
│   └── wiring-manifest.yaml
└── targets.yaml
```

---

## Spec Schemas

### objects.yaml

```yaml
version: string                    # Semantic version
objects:
  - id: string                     # Unique identifier (e.g., "User", "UserId")
    kind: primitive | product | coproduct | refined
    
    definition:
      # For kind: primitive
      base: string                 # Base type: Bool, String, Int, UUID, DateTime, etc.
      
      # For kind: product (×)
      fields:
        - name: string             # Field name
          type: string             # Reference to another object
          optional: boolean        # Default: false
          
      # For kind: coproduct (+)
      variants:
        - name: string             # Variant name
          payload: string | null   # Optional payload type reference
          
      # For kind: refined
      base: string                 # Underlying type
      predicate: string            # Constraint expression
      
    description: string            # Human-readable description
    traces_to: [string]            # Source requirement references
```

### morphisms.yaml

```yaml
version: string
morphisms:
  - id: string                     # Unique identifier (e.g., "create_user")
    domain: string                 # Input type (object reference)
    codomain: string               # Output type (object reference)
    effects: [string]              # Effect references (from effects.yaml)
    pure: boolean                  # true if effects is empty
    
    generator: boolean             # true = atomic, false = derived
    composed_of: [string]          # If generator: false, list of morphism ids
    composition_type: pure | kleisli  # ∘ or >=>
    
    description: string
    traces_to: [string]
```

### effects.yaml

```yaml
version: string
effects:
  - id: string                     # e.g., "IO", "Either[UserError, _]"
    kind: io | error | state | reader | writer | async
    
    parameters:
      - name: string               # Type parameter name
        variance: covariant | contravariant | invariant
        bound: string | null       # Optional type bound
        
    description: string

error_types:
  - id: string                     # e.g., "UserError"
    variants:
      - name: string               # e.g., "NotFound"
        payload: string | null     # e.g., "UserId"
```

### constraints.yaml

```yaml
version: string
constraints:
  - id: string                     # Unique identifier
    kind: invariant | precondition | postcondition | law
    
    scope: string                  # Object or morphism reference
    expression: string             # Formal proposition
    
    proof_obligation: boolean      # true = needs Lean proof
    description: string
    traces_to: [string]
```

---

## Build Schemas

### category.yaml

```yaml
version: string
category:
  name: string                     # e.g., "Domain"
  
  objects: [string]                # All object ids from spec
  
  morphisms:
    - id: string
      hom: string                  # "A → B" or "A → M[B]"
      effects: [string]
      generator: boolean
      composed_of: [string]        # If not generator
      
  identity:
    pattern: string                # "id_A: A → A"
    implementation: string         # "λx. x"
    
  composition:
    pure:
      operator: string             # "∘"
      signature: string            # "(B → C) × (A → B) → (A → C)"
    kleisli:
      operator: string             # ">=>"
      signature: string            # "(A → M[B]) × (B → M[C]) → (A → M[C])"
      
  laws:
    - name: string                 # e.g., "left_identity"
      statement: string            # e.g., "id ∘ f = f"
      status: stated | proven
```

### effects.yaml (build)

```yaml
version: string
monad_stack:
  name: string                     # e.g., "App"
  full_type: string                # e.g., "Reader[Env, IO[Either[AppError, A]]]"
  
  layers:
    - effect: string               # Effect id from spec
      position: integer            # Stack order (1 = outermost)
      
      unit:
        signature: string
        implementation: string
        
      bind:
        signature: string
        implementation: string
        
  composed:
    unit:
      signature: string
      implementation: string
    bind:
      signature: string
      implementation: string
      
  laws:
    left_identity:
      statement: string
      status: stated | proven
    right_identity:
      statement: string
      status: stated | proven
    associativity:
      statement: string
      status: stated | proven
```

### functors.yaml

```yaml
version: string
functors:
  - id: string                     # e.g., "F_api"
    enabled: boolean               # From targets config
    
    source: string                 # Source category name
    target: string                 # Target category name
    
    target_category:
      objects: [string]            # Target type names
      morphisms:
        - id: string
          hom: string
          
    object_map:
      - from: string               # Source object
        to: string                 # Target object
        transform: string          # Transformation description
        
    morphism_map:
      - from: string               # Source morphism
        to: string                 # Target morphism
        wrapping: string           # How it's wrapped
        
    preserves:
      identity:
        statement: string
        status: stated | proven
      composition:
        statement: string
        status: stated | proven
```

### transformations.yaml

```yaml
version: string
transformations:
  - id: string                     # e.g., "auth"
    enabled: boolean               # From targets config
    kind: middleware | decorator | adapter
    
    source_functor: string         # Functor being transformed
    target_functor: string         # Usually same functor
    
    config:                        # From targets.standardization
      # Varies by transformation type
      
    components:
      pattern: string              # How morphisms are wrapped
      
    naturality:
      statement: string
      status: stated | proven
```

---

## Verify Schemas

### laws-report.yaml

```yaml
version: string
proofs:
  - law: string                    # Law name
    category: category | monad | functor | transformation
    status: proven | failed | sorry
    file: string                   # Path to .lean file
    line: integer                  # Line number
    error: string | null           # Error message if failed
    
total:
  proven: integer
  failed: integer
  sorry: integer
```

### constraints-report.yaml

```yaml
version: string
constraints:
  - id: string                     # Constraint id from spec
    status: proven | satisfied | violated | runtime_check | unknown
    method: lean_proof | generated_validation | manual
    evidence: string               # Proof location or explanation
    file: string | null
    line: integer | null
```

### coverage-report.yaml

```yaml
version: string
coverage:
  objects:
    spec_count: integer
    build_count: integer
    gen_count: integer
    percentage: number
    gaps: [string]                 # Missing object ids
    
  morphisms:
    spec_count: integer
    build_count: integer
    gen_count: integer
    percentage: number
    gaps: [string]
    
  constraints:
    total: integer
    proven: integer
    runtime_check: integer
    unverified: integer
    percentage: number
    gaps:
      - id: string
        status: string
        
  functors:
    - id: string
      objects_mapped: string       # "15/15"
      morphisms_mapped: string     # "22/22"
      
overall:
  spec_to_build: string            # Percentage
  build_to_gen: string
  constraints_verified: string
  status: PASS | FAIL | WARN
```

---

## Gen Schemas

### types-manifest.yaml

```yaml
version: string
files:
  - path: string                   # Relative path to generated file
    objects: [string]              # Object ids in this file
    traces_to: [string]            # Spec object references
```

### morphisms-manifest.yaml

```yaml
version: string
files:
  - path: string
    morphisms: [string]            # Morphism ids in this file
    functor: string | null         # If functor application
    traces_to: [string]
```

### wiring-manifest.yaml

```yaml
version: string
entry_points:
  - path: string
    type: application | library | service
    
topology: monolith | microservices | serverless | library

files: [string]                    # All generated files
```

---

## Cross-Reference Rules

### Required References

1. `morphisms.yaml` domain/codomain → must exist in `objects.yaml`
2. `morphisms.yaml` effects → must exist in `effects.yaml`
3. `morphisms.yaml` composed_of → must exist in `morphisms.yaml`
4. `constraints.yaml` scope → must exist in `objects.yaml` or `morphisms.yaml`
5. `category.yaml` objects → must match `objects.yaml`
6. `category.yaml` morphisms → must match `morphisms.yaml`
7. `functors.yaml` object_map.from → must exist in source category
8. `gen/*.yaml` traces_to → must exist in spec or build

### Validation Commands

```bash
# Validate YAML syntax
python -c "import yaml; yaml.safe_load(open('file.yaml'))"

# Validate cross-references (custom script)
python validate_refs.py artifacts/v{N}/

# Validate generated code
python -c "import sys; sys.path.insert(0, 'gen/python/src'); import project"

# Validate Lean proofs
cd artifacts/v{N}/verify/proofs && lake build

# Validate Docker
docker-compose -f gen/python/docker-compose.yaml config
```

---

## Version Management

```yaml
# Version format: MAJOR.MINOR.PATCH
# 
# MAJOR: Breaking changes to spec (removed objects/morphisms)
# MINOR: Additive changes (new objects/morphisms)
# PATCH: Fixes (constraint changes, proof fixes)

version_history:
  - version: "1.0.0"
    timestamp: "2024-01-15T10:00:00Z"
    changes: "Initial specification"
  - version: "1.1.0"
    timestamp: "2024-01-16T14:30:00Z"
    changes: "Added Profile entity"
```
