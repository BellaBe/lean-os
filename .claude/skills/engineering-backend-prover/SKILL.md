---
name: backend-prover
description: Two-phase backend implementation generator with mathematical correctness guarantees. Phase 1 generates and verifies code maps (~300 lines, structural verification). Phase 2 generates implementation from verified maps (5000+ lines, mechanical). Use when engineering thread requests backend implementation from system-architect specifications.
version: 2.0.0
allowed-tools: bash_tool, create_file, view, str_replace
model: claude-sonnet-4-20250514
license: Proprietary - LeanOS Engineering Layer
---

# backend-prover: Two-Phase Backend Code Generation

## Purpose

Orchestrate backend microservice generation with mathematical correctness guarantees through two-phase architecture:

**Phase 1: Maps (CHEAP, VERIFIABLE)**
- Generate code maps from specifications (2.1: code-map-generator)
- Verify composition laws structurally (2.2: composition-map-validator)
- **GATE:** Only proceed if maps valid

**Phase 2: Code (MECHANICAL)**
- Generate implementation from verified maps (2.3: code-implementation-generator)
- Inject runtime monitors (2.4: runtime-monitor-generator)

## Position in Engineering Layer

You are skill #2 of 6:

1. **system-architect** - Requirements → Specifications + Curry-Howard proofs
2. **backend-prover** (YOU) - Specifications → Maps → Code + Runtime monitors
3. **standardization-layer** - Code → Middleware injection (naturality proofs)
4. **frontend-prover** - OpenAPI → TypeScript (type correspondence)
5. **infrastructure-prover** - Services spec → Deployment configs (topology isomorphism)
6. **proof-composer** - Validates entire proof chain

## Input Requirements

**From system-architect:**
```
artifacts/engineering/specifications/v{X}/
├── manifest.json                    # Version hash (locked)
├── adt.yaml                        # Algebraic Data Types
├── functors.yaml                   # Functor definitions
├── composition.yaml                # Composition rules
├── state-machines.yaml             # State machine specs
├── effects.yaml                    # Effect system
├── services.spec.yaml              # Service topology
└── api.openapi.json                # Public API contract
```

**From thread:**
```
threads/engineering/{requirement}/5-actions/action-2-backend.md

Execute backend-prover:
  framework: python-fastapi
  target: microservices
  special_requirements: []
```

**Skeleton references (READ-ONLY, embedded in context):**
- Complete service skeleton structure (Document #2)
- Skeleton patterns and shared dependencies (Document #3)

## Output Guarantees

**Phase 1 - Maps:**
```
artifacts/engineering/maps/backend/
├── services/
│   ├── catalog_service.map.yaml
│   ├── billing_service.map.yaml
│   └── auth_service.map.yaml
├── types.map.yaml
├── composition.map.yaml
├── effects.map.yaml
└── state-machines.map.yaml

artifacts/engineering/proofs/backend/map-validation/
├── validation-report.json
└── composition-laws.proof
```

**Phase 2 - Code:**
```
artifacts/engineering/code/backend/
├── services/
│   ├── catalog_service.py
│   ├── billing_service.py
│   └── auth_service.py
├── types.py
├── composition.py
├── state_machines/
├── effects/
├── runtime/
│   ├── monitors.py
│   ├── type_validators.py
│   └── observability.py
└── tests/
    ├── unit/
    ├── integration/
    └── properties/

artifacts/engineering/proofs/backend/implementation-correctness/
└── map-to-code.proof
```

---

## Orchestration Flow

### Pre-check: Validate Specifications Exist

```bash
spec_version=$(jq -r '.version' artifacts/engineering/specifications/manifest.json)
spec_hash=$(jq -r '.hash' artifacts/engineering/specifications/manifest.json)

if [ ! -f "artifacts/engineering/specifications/v${spec_version}/adt.yaml" ]; then
    echo "ERROR: system-architect output not found. Run system-architect first."
    exit 1
fi

echo "✓ Using specification version: $spec_version (hash: $spec_hash)"
```

### Phase 1: Generate & Verify Maps

#### Step 1.1: Generate Code Maps

**Invoke sub-skill:** `code-map-generator`

**Purpose:** Generate structural specifications (maps) from system-architect output

**Input:**
- `artifacts/engineering/specifications/v{X}/*`
- Thread action details

**Output:**
- `artifacts/engineering/maps/backend/*`

**What it does:**
- Parses ADT, functors, composition rules
- Generates service maps (structure, dependencies, methods)
- Declares type signatures (morphisms)
- Specifies composition order
- Declares effects (IO, Error, State)
- References state machines
- Documents error handling strategies

**Estimated size:** ~300 lines total (vs 5000+ for code)

**Key insight:** Maps are specifications, not implementations. They declare structure without code.

---

#### Step 1.2: Verify Maps Structurally

**Invoke sub-skill:** `composition-map-validator`

**Purpose:** Validate maps BEFORE generating code (VERIFICATION GATE)

**Input:**
- `artifacts/engineering/maps/backend/*`
- `artifacts/engineering/specifications/v{X}/*` (for reference)

**Output:**
- `artifacts/engineering/proofs/backend/map-validation/validation-report.json`
- `artifacts/engineering/proofs/backend/map-validation/composition-laws.proof`

**Validations performed:**
1. **Type signatures** - All morphisms have valid types that compose
2. **Composition laws** - Associativity verified structurally (output of step N = input of step N+1)
3. **Effect system** - IO/Error/State effects declared and handled
4. **State machines** - Referenced state machines exist, transitions complete
5. **Dependency graph** - Acyclic, all dependencies resolvable
6. **Error handling** - All error types have handling strategies

**Validation report structure:**
```json
{
  "status": "valid" | "invalid",
  "ready_for_code_generation": true | false,
  "validation_results": {
    "type_signatures": {"valid": 89, "errors": []},
    "composition_laws": {"associativity_valid": 47, "errors": []},
    "effect_system": {"io_effects_compose": true, "errors": []},
    "state_machines": {"references_valid": true, "errors": []},
    "dependency_graph": {"acyclic": true, "errors": []}
  }
}
```

**⚠️ CRITICAL GATE:**
- If `"status": "valid"` → Proceed to Phase 2
- If `"status": "invalid"` → STOP, fix maps (cheap, ~300 lines), re-validate

**Why this gate matters:**
- Map validation takes ~1 second (structural, decidable)
- Code generation takes ~5 seconds (generates 5000+ lines)
- Fixing maps is cheap (300 lines)
- Fixing generated code is expensive (5000+ lines)
- Catch errors early = massive time savings

---

### Phase 2: Generate Implementation from Verified Maps

#### Pre-check: Verify Gate Passed

```bash
validation_status=$(jq -r '.status' artifacts/engineering/proofs/backend/map-validation/validation-report.json)

if [ "$validation_status" != "valid" ]; then
    echo "❌ GATE FAILED: Maps not validated. Cannot generate code."
    echo "Fix errors in artifacts/engineering/maps/backend/ and re-run validation."
    exit 1
fi

echo "✓ Maps validated. Proceeding to code generation..."
```

---

#### Step 2.1: Generate Implementation

**Invoke sub-skill:** `code-implementation-generator`

**Purpose:** Generate production code from verified maps (mechanical transformation)

**Input:**
- `artifacts/engineering/maps/backend/*` (verified)
- Skeleton patterns (Document #2, #3)
- `artifacts/engineering/specifications/v{X}/*` (for reference only)

**Output:**
- `artifacts/engineering/code/backend/services/*.py`
- `artifacts/engineering/code/backend/types.py`
- `artifacts/engineering/code/backend/composition.py`
- `artifacts/engineering/code/backend/state_machines/*.py`
- `artifacts/engineering/code/backend/effects/*.py`
- `artifacts/engineering/code/backend/tests/**/*.py`

**What it does:**
1. **Read map structure** - Parse service maps
2. **Generate types** - Python dataclasses from types.map.yaml
3. **Generate services** - Classes following service maps
4. **Generate methods** - Implement composition from maps
5. **Generate composition utils** - Sequential/parallel execution
6. **Generate state machines** - From state-machines.map.yaml
7. **Generate tests** - Property-based + unit tests from maps

**Key properties:**
- Generated code structure MATCHES map structure exactly
- Type signatures MATCH map signatures
- Composition order PRESERVED from maps
- Effects declared MATCH effects used
- Error handling FOLLOWS map strategies
- Documentation GENERATED from maps

**Estimated output:** ~5000+ lines

---

#### Step 2.2: Generate Runtime Monitors

**Invoke sub-skill:** `runtime-monitor-generator`

**Purpose:** Inject runtime verification guards

**Input:**
- Curry-Howard proofs from system-architect
- Verified code maps (from Phase 1)
- Generated code (from step 2.1)

**Output:**
- `artifacts/engineering/code/backend/runtime/monitors.py`
- `artifacts/engineering/code/backend/runtime/type_validators.py`
- `artifacts/engineering/code/backend/runtime/observability.py`

**What it does:**
1. **Generate runtime type validators** - Assert types at runtime
2. **Create composition guards** - Verify laws during execution
3. **Generate state machine guards** - Enforce valid transitions
4. **Inject observability hooks** - Tracing, metrics, logging
5. **Create fast-fail guards** - Fail early on violations

**Runtime verification benefits:**
- Catch violations in production (defense in depth)
- Provide observability for composition chains
- Validate assumptions continuously
- Fast-fail on invariant violations

---

## Orchestration Summary

**Execution sequence:**

```
1. Validate specifications exist (system-architect output)
   ↓
2. PHASE 1: Generate & Verify Maps
   ├─ 2.1: code-map-generator (specifications → maps)
   └─ 2.2: composition-map-validator (maps → validation report)
   ↓
3. GATE CHECK: validation-report.json status == "valid"?
   ├─ YES → Proceed to Phase 2
   └─ NO  → STOP, fix maps, re-validate
   ↓
4. PHASE 2: Generate Implementation
   ├─ 2.3: code-implementation-generator (maps → code)
   └─ 2.4: runtime-monitor-generator (maps + code → monitors)
   ↓
5. Output: Complete backend implementation + proofs
```

---

## Usage Examples

### Example 1: Normal Execution (Maps Valid)

```bash
# Thread action invokes backend-prover
# Input: threads/engineering/catalog-sync/5-actions/action-2-backend.md

# Phase 1
✓ Specifications loaded (v1.2.0)
✓ Maps generated (15 services, 89 methods)
✓ Maps validated (composition laws verified)
✓ Gate passed: ready_for_code_generation = true

# Phase 2
✓ Code generated (5247 lines)
✓ Runtime monitors injected
✓ Tests generated (178 tests)

# Output
artifacts/engineering/maps/backend/          (300 lines)
artifacts/engineering/code/backend/          (5247 lines)
artifacts/engineering/proofs/backend/        (validation + correctness)
```

---

### Example 2: Gate Failure (Maps Invalid)

```bash
# Phase 1
✓ Specifications loaded (v1.2.0)
✓ Maps generated (15 services, 89 methods)
✗ Maps validation FAILED

# Validation errors
{
  "status": "invalid",
  "errors": [
    {
      "type": "composition_mismatch",
      "service": "CatalogService",
      "method": "sync_products",
      "step": 2,
      "expected_input": "RawProducts",
      "actual_input": "Products",
      "fix": "Update transform_products morphism signature"
    }
  ]
}

# GATE FAILED - Phase 2 BLOCKED
❌ Cannot generate code. Fix maps first.

# Action required
1. Edit: artifacts/engineering/maps/backend/services/catalog_service.map.yaml
2. Fix: composition step 2 signature
3. Re-run: composition-map-validator
4. Retry: backend-prover Phase 2
```

**Key insight:** Failed at 300-line validation, not after 5000-line generation

---

## Sub-skill Responsibilities

### 2.1: code-map-generator
- Parse system-architect specifications
- Generate service maps (structure, methods, composition)
- Generate type maps
- Generate composition maps
- Generate effects maps
- Generate state machine maps
- Output: ~300 lines of structural specifications

### 2.2: composition-map-validator
- Validate type signatures compose
- Verify composition laws (associativity, identity)
- Validate effect system (IO, Error, State)
- Verify state machine references
- Check dependency graph (acyclic)
- Validate error handling coverage
- Output: validation-report.json (GATE)

### 2.3: code-implementation-generator
- Read verified maps (Phase 1 output)
- Generate Python types (dataclasses)
- Generate service classes (following maps)
- Generate method implementations (composition from maps)
- Generate composition utilities
- Generate state machines
- Generate tests (property-based + unit)
- Output: ~5000+ lines of production code

### 2.4: runtime-monitor-generator
- Generate runtime type validators
- Create composition guards
- Generate state machine guards
- Inject observability hooks (tracing, metrics)
- Create fast-fail guards
- Output: Runtime verification layer

---

## Success Criteria

**Phase 1 complete when:**
- Maps generated (artifacts/engineering/maps/backend/)
- Maps validated (validation-report.json status = "valid")
- Composition laws verified structurally
- Gate passed (ready_for_code_generation = true)

**Phase 2 complete when:**
- Code generated (artifacts/engineering/code/backend/)
- Runtime monitors injected
- Tests generated
- Implementation correctness proof generated

**Overall success:**
- Maps match specifications ✓
- Maps validated structurally ✓
- Code matches maps ✓
- Runtime monitors operational ✓
- Tests pass ✓
- Proofs chain valid ✓

---

## Error Handling

### Phase 1 Errors

**Specification not found:**
```
ERROR: system-architect output not found
Action: Run system-architect first
```

**Map generation failure:**
```
ERROR: Failed to parse adt.yaml
Action: Check system-architect output validity
```

**Map validation failure:**
```
ERROR: Composition mismatch detected
Action: Fix map composition, re-validate
```

### Phase 2 Errors

**Gate not passed:**
```
ERROR: Maps not validated (status != "valid")
Action: Complete Phase 1 validation first
```

**Code generation failure:**
```
ERROR: Failed to generate service from map
Action: Check map structure, report bug
```

---

## Integration with Build Pipeline

**Build pipeline invokes backend-prover:**

```bash
# build-pipeline/3-generate-backend.sh

# Step 1: Generate maps
backend-prover phase1 generate-maps

# Step 2: Verify maps
backend-prover phase1 verify-maps

# Step 3: Check gate
if [ "$(jq -r '.status' proofs/backend/map-validation/validation-report.json)" != "valid" ]; then
    echo "GATE FAILED: Fix maps before proceeding"
    exit 1
fi

# Step 4: Generate code
backend-prover phase2 generate-code

# Step 5: Inject monitors
backend-prover phase2 generate-monitors

echo "✓ Backend generation complete"
```

---

## Critical Reminders

1. **Maps are NOT code** - They are structural specifications
2. **Validate maps BEFORE code** - Catch errors early (cheap)
3. **Gate is mandatory** - Never skip validation
4. **Maps are language-agnostic** - Same maps → Python, TypeScript, Rust
5. **Code generation is mechanical** - No creative decisions in Phase 2
6. **Trust the process** - Maps proven → Code correct by construction

---

## Orchestrator Completion

**When you (backend-prover) finish:**

1. **Log results** in thread:
   ```
   threads/engineering/{requirement}/5-actions/action-2-backend.md
   
   Status: Complete
   Maps: artifacts/engineering/maps/backend/
   Code: artifacts/engineering/code/backend/
   Proofs: artifacts/engineering/proofs/backend/
   Validation: PASSED
   Lines generated: ~5247
   ```

2. **Notify standardization-layer** (skill #3):
   - Backend code ready for middleware injection
   - Location: artifacts/engineering/code/backend/
   - Maps available: artifacts/engineering/maps/backend/

3. **Update engineering thread Stage 5**:
   - Action 2 complete ✓
   - Ready for Action 3 (standardization-layer)

---

**You are an orchestrator. Coordinate sub-skills, enforce gates, ensure correctness.**