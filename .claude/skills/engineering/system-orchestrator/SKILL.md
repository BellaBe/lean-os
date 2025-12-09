---
name: system-orchestrator
description: |
  Master orchestrator for building complete systems using categorical architecture.
  Coordinates 12 level skills from primitives to deployed infrastructure. Use when:
  (1) Building a new system from specifications or requirements
  (2) Regenerating a system after specification changes
  (3) Validating an existing system's categorical structure
  (4) Debugging pipeline failures at any level

  Input: specifications/ directory OR raw requirements (routes to specifications-architect first)
  Output: Complete deployed system with manifests, proofs, code, and infrastructure

  IMPORTANT: All engineering outputs are VERSIONED under artifacts/engineering/v{X}/
---

# System Orchestrator

Master controller for the LeanOS categorical system builder.

## Purpose

Execute the complete 12-level pipeline:

```
Specifications → L0..L11 → Deployed System
```

Each level is a functor preserving structure. The orchestrator ensures:
- Correct execution order
- Validation gates between levels
- Error recovery and retry
- Manifest chain integrity

## Critical: Manifests vs Actual Files

```
╔══════════════════════════════════════════════════════════════════════════════╗
║  ⚠️  CRITICAL: L9-L11 MUST CREATE ACTUAL FILES, NOT JUST MANIFESTS  ⚠️       ║
║                                                                              ║
║  If your output is "manifests that describe code" you have FAILED.           ║
║  The goal is a RUNNING SYSTEM, not documentation.                            ║
║                                                                              ║
║  ❌ WRONG: "Actual code generation would follow these specifications"        ║
║  ✅ RIGHT: Actually generate the code files NOW                              ║
╚══════════════════════════════════════════════════════════════════════════════╝
```

**THIS IS THE MOST IMPORTANT DISTINCTION:**

```yaml
manifest_vs_files:
  levels_0_to_8:
    output: "ONLY manifests (YAML)"
    reason: "These levels define structure, not executable code"
    manifest_contains: "Item definitions, traces, validation"
    actual_files: "None (manifest IS the artifact)"
    
  levels_9_to_11:
    output: "Manifests AND actual files"
    reason: "These levels produce executable artifacts"
    manifest_contains: "References to generated files"
    actual_files: "REAL CODE that runs"
    
    YOU_MUST:
      - "Use file creation tools to write actual .py files"
      - "Use file creation tools to write actual Dockerfile"
      - "Use file creation tools to write actual docker-compose.yaml"
      - "NOT just describe what files would contain"
      - "NOT say 'code generation would follow'"
      - "NOT put code inside YAML manifests"
    
  L9_code:
    manifest: "artifacts/engineering/v{X}/manifests/level-9.manifest.yaml"
    actual_files:
      - "artifacts/engineering/v{X}/generated/python/src/project/**/*.py"
      - "artifacts/engineering/v{X}/generated/python/tests/**/*.py"
      - "artifacts/engineering/v{X}/generated/python/pyproject.toml"
    action: "WRITE ACTUAL PYTHON FILES using create_file or equivalent"
    not_action: "Describe what files would contain in YAML"

  L10_bootstrap:
    manifest: "artifacts/engineering/v{X}/manifests/level-10.manifest.yaml"
    actual_files:
      - "artifacts/engineering/v{X}/generated/python/src/project/main.py"
      - "artifacts/engineering/v{X}/generated/python/src/project/container.py"
      - "artifacts/engineering/v{X}/generated/python/src/project/config.py"
    action: "WRITE ACTUAL PYTHON FILES"

  L11_infrastructure:
    manifest: "artifacts/engineering/v{X}/manifests/level-11.manifest.yaml"
    actual_files:
      - "artifacts/engineering/v{X}/infrastructure/Dockerfile"
      - "artifacts/engineering/v{X}/infrastructure/docker-compose.yaml"
      - "artifacts/engineering/v{X}/infrastructure/.env.example"
    action: "WRITE ACTUAL INFRASTRUCTURE FILES"
```

**FAILURE MODE TO AVOID:**

```yaml
# This output indicates FAILURE:
"The manifests define the complete structure. Actual code generation 
 would follow these specifications with full traceability..."

# This means you generated DESCRIPTIONS, not CODE.
# Go back and actually CREATE THE FILES.
```

**CORRECT EXECUTION:**

```yaml
L9_execution:
  step_1: "Read manifests L0-L8"
  step_2: "For each code item, CREATE ACTUAL FILE:"
  
  example:
    item: "code.customer_service"
    action: |
      # Actually create the file using file creation tool:
      create_file(
        path="generated/python/src/project/modules/customers/service.py",
        content='''
        from project.shared.interfaces import IRepository
        from project.domain.entities import Customer, CustomerId
        
        class CustomerService:
            def __init__(self, repo: IRepository[Customer, CustomerId]):
                self._repo = repo
                
            async def get_customer(self, id: CustomerId) -> Result[AppError, Customer]:
                return await self._repo.get(id)
        '''
      )
      
  step_3: "After ALL files created, write manifest with file references"
  step_4: "Validate files exist on disk"
```

## Pipeline Overview

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         SYSTEM ORCHESTRATOR                             │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  PHASE 1: SPECIFICATION (if needed)                                     │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │ specifications-architect                                         │    │
│  │   Requirements → specifications/v{X}/                            │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                              │                                          │
│                              ▼                                          │
│  PHASE 2: TYPE FOUNDATION (L0-L3)                                       │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │ L0: level-0-primitives     → level-0.manifest.yaml              │    │
│  │ L1: level-1-entities       → level-1.manifest.yaml              │    │
│  │ L2: level-2-morphisms      → level-2.manifest.yaml              │    │
│  │ L3: level-3-modules        → level-3.manifest.yaml              │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                              │                                          │
│                              ▼                                          │
│  PHASE 3: CATEGORICAL STRUCTURE (L4-L7)                                 │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │ L4: level-4-categories     → level-4.manifest.yaml (+ monads)   │    │
│  │ L5: level-5-functors       → level-5.manifest.yaml              │    │
│  │ L6: level-6-adjunctions    → level-6.manifest.yaml              │    │
│  │ L7: level-7-transformations → level-7.manifest.yaml             │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                              │                                          │
│                              ▼                                          │
│  PHASE 4: VERIFICATION (L8)                                             │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │ L8: level-8-proofs         → level-8.manifest.yaml + *.lean     │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                              │                                          │
│                              ▼                                          │
│  PHASE 5: CODE GENERATION (L9-L11)                                      │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │ L9: level-9-code           → level-9.manifest.yaml + code/      │    │
│  │ L10: level-10-bootstrap    → level-10.manifest.yaml + main.py   │    │
│  │ L11: level-11-infrastructure → level-11.manifest.yaml + infra/  │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                              │                                          │
│                              ▼                                          │
│                      DEPLOYED SYSTEM                                    │
└─────────────────────────────────────────────────────────────────────────┘
```

## Execution Protocol

### Step 0: Input Detection

```yaml
input_detection:
  if_specifications_exist:
    check: "specifications/v{X}/ exists with validation-report.yaml"
    action: "Proceed to Level 0"
    
  if_requirements_only:
    check: "Raw requirements provided, no specifications/"
    action: "Route to specifications-architect first"
    skill: "specifications-architect"
    output: "specifications/v{X}/"
    then: "Proceed to Level 0"
    
  if_partial_manifests:
    check: "Some level-N.manifest.yaml exist"
    action: "Resume from highest valid level + 1"
```

### Step 1: Execute Level Skills

**Before starting any level execution:**

```yaml
prerequisite_reading:
  always_first:
    - "manifest-schema/SKILL.md - understand manifest structure"
    - "shared-modules/SKILL.md - understand scope detection"
  then_per_level:
    - "level-{N}-{name}/SKILL.md - understand level process"
```

For each level N from 0 to 11:

```yaml
execute_level:
  1_read_skill:
    action: "Read level-{N}-{name}/SKILL.md"
    understand: "Process, inputs, outputs, validation"
    
  2_load_inputs:
    action: "Load required manifests from previous levels"
    validate: "All input manifests exist and are valid"
    on_missing: "HALT - missing prerequisite"
    
  3_execute_process:
    action: "Follow skill's process steps exactly"
    generate: "All items specified in skill"
    scope: "Apply shared-modules scope detection to each item"
    
  4_generate_artifacts:
    # THIS IS THE CRITICAL STEP THAT WAS MISSING
    if_level_0_to_8:
      action: "Manifest IS the artifact - no additional files"
      
    if_level_9:
      action: "WRITE ACTUAL CODE FILES"
      do_not: "Put code inside manifest YAML"
      must: |
        For each item in manifest:
          1. Generate actual .py/.ts file at artifact path
          2. Write real, executable code to that file
          3. Record path in manifest item.artifact field
      example: |
        # WRONG: code in manifest
        items:
          - id: "service.customer"
            definition:
              code: "class CustomerService: ..."
              
        # RIGHT: file reference in manifest, actual file written
        items:
          - id: "service.customer"
            artifact: "generated/python/src/project/modules/customers/service.py"
        
        # AND create the actual file:
        # generated/python/src/project/modules/customers/service.py
        
    if_level_10:
      action: "WRITE ACTUAL BOOTSTRAP FILES"
      must: "Create main.py, container.py, config.py as real files"
      
    if_level_11:
      action: "WRITE ACTUAL INFRASTRUCTURE FILES"
      must: "Create Dockerfile, docker-compose.yaml as real files"
    
  5_validate_output:
    action: "Run skill's validation rules + manifest-schema rules"
    checks:
      - "Schema valid (manifest-schema)"
      - "Counts match"
      - "Traces valid"
      - "Coverage complete"
      - "Scope valid (shared-modules)"
    if_level_9_to_11:
      additional_checks:
        - "All artifact files exist on disk"
        - "Code files are syntactically valid"
        - "No placeholder/TODO in generated code"
    on_fail: "HALT with diagnostic"
    
  6_write_manifest:
    action: "Write level-{N}.manifest.yaml per manifest-schema"
    include: "Validation timestamp, checksums"
    format: "Follow manifest-schema item structure exactly"
    if_level_9_to_11: "Manifest references files, does NOT contain file contents"
    
  7_proceed:
    action: "Move to level N+1"
```

### Step 2: Validation Gates

Each level must pass before proceeding:

```yaml
validation_gates:
  L0_gate:
    check: "All primitives defined, kinds valid"
    blocks: "L1"
    
  L1_gate:
    check: "All entities defined, traces to L0"
    blocks: "L2"
    
  L2_gate:
    check: "All morphisms typed, effects from L0"
    blocks: "L3"
    
  L3_gate:
    check: "All morphisms grouped, no orphans"
    blocks: "L4"
    
  L4_gate:
    check: "Categories defined, monads have laws"
    blocks: "L5, L8"
    
  L5_gate:
    check: "Functors preserve structure"
    blocks: "L6"
    
  L6_gate:
    check: "Adjunctions have unit/counit"
    blocks: "L7"
    
  L7_gate:
    check: "Transformations satisfy naturality"
    blocks: "L8"
    
  L8_gate:
    check: "All proofs compile, no sorry"
    blocks: "L9"
    critical: true  # No code without proofs
    
  L9_gate:
    check: "All code ACTUALLY GENERATED as files"
    validation:
      - "generated/python/src/ directory exists"
      - "*.py files exist (not just manifest)"
      - "ast.parse() succeeds on all .py files"
      - "imports resolve"
    failure_indicator: "Only manifest exists, no .py files"
    blocks: "L10"
    
  L10_gate:
    check: "Bootstrap files ACTUALLY CREATED"
    validation:
      - "main.py exists as actual file"
      - "container.py exists as actual file"
      - "Can import main module"
    failure_indicator: "Only manifest exists, no main.py"
    blocks: "L11"
    
  L11_gate:
    check: "Infrastructure files ACTUALLY CREATED"
    validation:
      - "Dockerfile exists as actual file"
      - "docker-compose.yaml exists as actual file"
      - "docker-compose config validates"
    failure_indicator: "Only manifest exists, no Dockerfile"
    blocks: "DEPLOY"
```

## Supporting Skills Usage

Before executing level skills, understand these foundational skills:

### manifest-schema

**When to use:** Before generating ANY manifest, and when validating manifests.

```yaml
manifest_schema_usage:
  before_any_level:
    action: "Read manifest-schema/SKILL.md"
    understand:
      - "item schema (id, name, kind, scope, traces, definition, status)"
      - "scope detection algorithm"
      - "validation rules"
      - "per-level category structure"
      
  when_writing_manifest:
    action: "Follow manifest-schema exactly"
    required_fields:
      - "schema_version"
      - "level (number, name, description)"
      - "source (level, manifest, version)"
      - "items array"
      - "counts"
      - "validation"
      
  when_validating:
    action: "Run all validation rules from manifest-schema"
    rules:
      - "traces_valid"
      - "counts_match"
      - "coverage_complete"
      - "scope_valid"
```

### shared-modules

**When to use:** At L9 code generation, and when determining item scope at any level.

```yaml
shared_modules_usage:
  at_any_level:
    action: "Apply scope detection algorithm"
    algorithm: |
      Shared(item) ⟺ |{module(consumer) : consumer traces to item}| ≥ 2
    scope_values: ["shared", "module", "internal"]
    
  at_L9_code_generation:
    action: "Read shared-modules/SKILL.md before generating code"
    generation_order:
      1: "Generate shared/ directory first"
      2: "Generate modules/ directories second"
      3: "Generate internal items last"
    structure: |
      generated/python/src/project/
      ├── shared/           # scope: shared
      │   ├── types/
      │   ├── errors/
      │   ├── validation/
      │   ├── interfaces/
      │   └── middleware/
      └── modules/          # scope: module
          ├── customers/
          └── orders/
          
  shared_items_by_level:
    L0: "All primitives (inherently universal)"
    L1: "AuditInfo, Pagination, AppError"
    L2: "validate_email, paginate, map_error"
    L3: "IRepository[E,Id], ICRUDService[...]"
    L4: "App monad, AppReader"
    L7: "All middleware (Auth, Logging, Metrics, etc.)"
```

## Level Reference

Quick reference for each level's responsibility:

| Level | Skill | Categorical Role | Key Output |
|-------|-------|------------------|------------|
| 0 | level-0-primitives | Type signature | Base types, monad symbols |
| 1 | level-1-entities | Objects | Product types (entities) |
| 2 | level-2-morphisms | Arrows | Operations with effects |
| 3 | level-3-modules | Groupings | Coherent operation sets |
| 4 | level-4-categories | Categories + Monads | Laws, Kleisli structure |
| 5 | level-5-functors | Functors | Structure-preserving maps |
| 6 | level-6-adjunctions | Adjunctions | L ⊣ R optimal pairs |
| 7 | level-7-transformations | Nat Trans | Middleware as η: F ⟹ G |
| 8 | level-8-proofs | Verification | Lean 4 proofs |
| 9 | level-9-code | Implementation | Executable code |
| 10 | level-10-bootstrap | Wiring | DI, lifecycle, main |
| 11 | level-11-infrastructure | Deployment | Containers, orchestration |

## Error Handling

```yaml
error_handling:
  validation_failure:
    action: "Stop pipeline, report level and error"
    output: |
      ❌ Level {N} validation failed:
        - Rule: {rule_name}
        - Expected: {expected}
        - Actual: {actual}
        - Fix: {suggestion}
    recovery: "Fix issue, re-run from level N"
    
  missing_input:
    action: "Report missing prerequisite"
    output: |
      ❌ Level {N} cannot proceed:
        - Missing: level-{M}.manifest.yaml
        - Required by: {dependency_reason}
    recovery: "Generate level M first"
    
  proof_failure:
    action: "Stop at L8, report failed proofs"
    output: |
      ❌ Proof verification failed:
        - File: {file}.lean
        - Obligation: {obligation}
        - Error: {lean_error}
    recovery: "Fix categorical structure at L4-L7, regenerate proofs"
    critical: "NEVER proceed to L9 with proof failures"
```

## Manifest Chain

The orchestrator maintains manifest chain integrity:

```yaml
manifest_chain:
  structure: |
    Each manifest links to its source:
      level-N.manifest.yaml:
        source:
          level: N-1
          manifest: "level-{N-1}.manifest.yaml"
          version: "{checksum}"
          
  validation: |
    Before executing level N:
      1. Verify level-{N-1}.manifest.yaml exists
      2. Verify checksum matches recorded version
      3. If mismatch, regenerate from N-1
      
  traceability: |
    Every item traces to lower levels:
      level-9.item → level-4.category → level-2.morphism → level-1.entity → level-0.type
```

## Output Structure

**IMPORTANT: All engineering outputs are versioned under `artifacts/engineering/v{X}/`**

The version number `{X}` (e.g., v1, v2) corresponds to the specification version.
This enables:
- Multiple versions to coexist during migration
- Clear traceability from code to specifications
- Rollback capability

```
artifacts/engineering/
└── v{X}/                              # Version matches specifications version
    ├── specifications/
    │   ├── domain-concepts.yaml
    │   ├── requirements.adt
    │   ├── constraints.yaml
    │   ├── services.spec.yaml
    │   ├── state-machines.yaml
    │   ├── architecture.categorical
    │   ├── types.curry-howard
    │   ├── versions.yaml
    │   └── validation-report.yaml
    │
    ├── manifests/
    │   ├── level-0.manifest.yaml
    │   ├── level-1.manifest.yaml
    │   ├── ...
    │   └── level-11.manifest.yaml
    │
    ├── proofs/
    │   ├── certificates/              # Proof certificates
    │   │   └── *.cert.yaml
    │   └── lean/                      # Lean 4 proofs
    │       ├── lakefile.lean
    │       ├── lean-toolchain
    │       └── LeanOS/
    │           ├── Basic.lean
    │           ├── Category.lean
    │           ├── Monad.lean
    │           └── ...
    │
    ├── generated/
    │   └── python/
    │       ├── pyproject.toml
    │       └── src/
    │           └── {project}/
    │               ├── shared/
    │               ├── domain/
    │               ├── application/
    │               ├── infrastructure/
    │               └── api/
    │
    └── infrastructure/
        ├── Dockerfile
        ├── docker-compose.yaml
        └── .env.example
```

**Version Determination:**
```yaml
version_rules:
  new_system:
    action: "Start at v1"
    path: "artifacts/engineering/v1/"

  specification_change:
    minor: "Same version, update in place"
    major: "Increment version (v1 → v2)"
    criteria: "Breaking changes to entities or morphisms"

  current_version:
    detect: "ls artifacts/engineering/ | grep -E '^v[0-9]+$' | sort -V | tail -1"
    default: "v1"
```

## Execution Modes

### Full Build

```yaml
full_build:
  trigger: "Build system for [requirements]"
  steps:
    - "specifications-architect (if needed)"
    - "L0 through L11 in order"
    - "Validate all gates"
  output: "Complete deployable system"
```

### Incremental Update

```yaml
incremental_update:
  trigger: "Add [entity/morphism/module] to system"
  steps:
    - "Identify affected levels"
    - "Update from lowest affected level"
    - "Cascade changes upward"
    - "Regenerate proofs"
    - "Regenerate code"
  optimization: "Skip unchanged levels"
```

### Validation Only

```yaml
validation_only:
  trigger: "Validate system" / "Check categorical structure"
  steps:
    - "Load all existing manifests"
    - "Verify chain integrity"
    - "Run all validation rules"
    - "Report status"
  output: "Validation report (no generation)"
```

### Resume from Failure

```yaml
resume:
  trigger: "Continue from level {N}" / "Fix and retry"
  steps:
    - "Load manifests 0 through N-1"
    - "Verify all are valid"
    - "Execute from level N"
  precondition: "Prior levels must be valid"
```

## Shared Modules Handling

The orchestrator ensures shared modules are generated correctly:

```yaml
shared_modules:
  detection: |
    At each level, items with scope: "shared" are identified
    Shared = used by 2+ modules
    
  generation_order: |
    L9 generates in order:
      1. shared/ directory first
      2. modules/ directories second
      3. Internal items last
      
  validation: |
    Verify shared items don't depend on module-scoped items
```

## Usage Examples

### Example 1: Build New System

```
User: "Build an e-commerce system with customers, orders, and payments"

Orchestrator:
  0. Determine version: v1 (new system)
     → All outputs under artifacts/engineering/v1/

  1. Route to specifications-architect
     → artifacts/engineering/v1/specifications/ generated
  2. Execute L0: primitives
     → artifacts/engineering/v1/manifests/level-0.manifest.yaml (35 items)
  3. Execute L1: entities
     → artifacts/engineering/v1/manifests/level-1.manifest.yaml
  4. Execute L2: morphisms
     → artifacts/engineering/v1/manifests/level-2.manifest.yaml
  5. Execute L3: modules
     → artifacts/engineering/v1/manifests/level-3.manifest.yaml
  6. Execute L4: categories
     → artifacts/engineering/v1/manifests/level-4.manifest.yaml
  7. Execute L5: functors
     → artifacts/engineering/v1/manifests/level-5.manifest.yaml
  8. Execute L6: adjunctions
     → artifacts/engineering/v1/manifests/level-6.manifest.yaml
  9. Execute L7: transformations
     → artifacts/engineering/v1/manifests/level-7.manifest.yaml
  10. Execute L8: proofs
      → artifacts/engineering/v1/manifests/level-8.manifest.yaml
      → artifacts/engineering/v1/proofs/lean/
      → artifacts/engineering/v1/proofs/certificates/
  11. Execute L9: code
      → artifacts/engineering/v1/manifests/level-9.manifest.yaml
      → ACTUALLY CREATE FILES:
         artifacts/engineering/v1/generated/python/src/project/
         ├── shared/
         │   ├── __init__.py
         │   ├── types/pagination.py
         │   ├── errors/base.py
         │   └── middleware/auth.py
         ├── domain/entities/
         │   ├── customer.py
         │   ├── order.py
         │   └── payment.py
         ├── modules/
         │   ├── customers/service.py
         │   ├── orders/service.py
         │   └── payments/service.py
         └── ...
  12. Execute L10: bootstrap
      → artifacts/engineering/v1/manifests/level-10.manifest.yaml
      → ACTUALLY CREATE FILES:
         artifacts/engineering/v1/generated/python/src/project/main.py
         artifacts/engineering/v1/generated/python/src/project/container.py
         artifacts/engineering/v1/generated/python/src/project/config.py
  13. Execute L11: infrastructure
      → artifacts/engineering/v1/manifests/level-11.manifest.yaml
      → ACTUALLY CREATE FILES:
         artifacts/engineering/v1/infrastructure/Dockerfile
         artifacts/engineering/v1/infrastructure/docker-compose.yaml
         artifacts/engineering/v1/infrastructure/.env.example

  Output: Complete e-commerce system with REAL FILES ready to deploy

  Verify: ls artifacts/engineering/v1/generated/python/src/project/
  Deploy: cd artifacts/engineering/v1/infrastructure && docker-compose up
```

### Example 2: Add Entity to Existing System

```
User: "Add Refund entity to the e-commerce system"

Orchestrator:
  1. Detect existing manifests (L0-L11 present)
  2. Update L1: add Refund entity
  3. Update L0: add RefundId identifier
  4. Update L2: add refund morphisms
  5. Update L3: add to PaymentModule or new RefundModule
  6. Update L4: extend category objects
  7. Update L5: extend functor mappings
  8. L6: check if adjunctions need update
  9. L7: verify middleware applies to new endpoints
  10. Regenerate L8: new proof obligations
  11. Regenerate L9: new code
  12. Update L10: wire new components
  13. Update L11: if new service needed
  
  Output: System extended with Refund capability
```

### Example 3: Debug Proof Failure

```
User: "L8 failed: Monad.lean has 'sorry'"

Orchestrator:
  1. Load L4 manifest
  2. Identify monad with missing proof
  3. Check monad laws are properly stated
  4. If laws incomplete: fix L4, regenerate L8
  5. If laws complete but proof hard: assist with Lean tactics
  6. Re-run L8 validation
  7. If passes: proceed to L9
  
  Output: Proofs complete, pipeline unblocked
```

## Critical Rules

```yaml
critical_rules:
  0_files_not_manifests:
    rule: "L9-L11 MUST create actual files, not just manifests"
    reason: "The goal is a running system, not documentation"
    wrong: "Putting code inside YAML manifest"
    right: "Writing .py/.ts/Dockerfile files to disk"
    validation: "Check artifact files exist after generation"
    
  1_order:
    rule: "Always execute levels in order 0→11"
    reason: "Each level depends on previous"
    
  2_validation:
    rule: "Never skip validation gates"
    reason: "Invalid input produces invalid output"
    
  3_proofs:
    rule: "Never generate code (L9) without proofs (L8)"
    reason: "Proofs guarantee categorical correctness"
    exception: "Exploration mode only, clearly marked"
    
  4_traces:
    rule: "Every item must trace to Level 0"
    reason: "Ensures complete derivation chain"
    
  5_manifests:
    rule: "Always write manifests, even for partial runs"
    reason: "Enables resume and debugging"
    
  6_shared_first:
    rule: "Generate shared modules before module-specific code"
    reason: "Modules depend on shared constructs"
    
  7_executable_output:
    rule: "Final output must be executable, not descriptive"
    test: "Can run 'docker-compose up' and system starts"
    if_only_manifests: "PIPELINE FAILED - no executable system"
```

## Integration with specifications-architect

The orchestrator integrates with specifications-architect for requirements:

```yaml
integration:
  when_specs_missing:
    detect: "No specifications/v{X}/ directory"
    action: |
      1. Invoke specifications-architect skill
      2. Pass requirements to it
      3. Wait for specifications/v{X}/ output
      4. Validate specification completeness
      5. Proceed to Level 0
      
  when_specs_exist:
    detect: "specifications/v{X}/ exists"
    action: |
      1. Validate specification structure
      2. Check validation-report.yaml
      3. Proceed directly to Level 0
      
  when_specs_invalid:
    detect: "specifications/ exists but validation failed"
    action: |
      1. Report validation errors
      2. Suggest re-running specifications-architect
      3. Do not proceed to Level 0
```

## Skill Dependencies

```yaml
foundational_skills:
  # READ THESE FIRST - they define structure used by all levels
  - manifest-schema          # Schema for all manifests, validation rules
  - shared-modules           # Cross-cutting constructs, scope detection

level_skills:
  # Execute in order 0→11
  - level-0-primitives       # Type signature
  - level-1-entities         # Product types
  - level-2-morphisms        # Typed arrows
  - level-3-modules          # Groupings
  - level-4-categories       # Categories + Monads + Kleisli
  - level-5-functors         # Structure-preserving maps
  - level-6-adjunctions      # L ⊣ R pairs
  - level-7-transformations  # Natural transformations (middleware)
  - level-8-proofs           # Lean 4 verification
  - level-9-code             # Executable implementation
  - level-10-bootstrap       # DI, lifecycle, main
  - level-11-infrastructure  # Containers, orchestration
  
optional_skills:
  - specifications-architect  # If starting from requirements (not specs)
```

## Success Criteria

Pipeline is complete when:

```yaml
success_criteria:
  manifests:
    - "All 12 level manifests exist"
    - "All manifests pass validation"
    - "Chain integrity verified"
    
  proofs:
    - "All Lean files compile"
    - "No 'sorry' in proofs"
    - "All obligations discharged"
    
  actual_code_files:
    # THIS IS CRITICAL - must be actual files, not YAML
    check: "Verify files exist on disk"
    required:
      - "generated/python/src/project/**/*.py exist"
      - "generated/python/pyproject.toml exists"
      - "Files contain valid Python syntax"
      - "No 'TODO' or placeholder code"
    validation: |
      import ast
      for py_file in glob("generated/**/*.py"):
          ast.parse(open(py_file).read())  # Must parse
          
  actual_infrastructure_files:
    check: "Verify infra files exist on disk"
    required:
      - "infrastructure/Dockerfile exists"
      - "infrastructure/docker-compose.yaml exists"
      - "docker-compose config validates"
    validation: |
      docker-compose -f infrastructure/docker-compose.yaml config
    
  executable_test:
    # The ultimate test - does it run?
    check: "System can start"
    command: "docker-compose up --build -d"
    success: "Containers start without error"
    
  final_output: |
    ✅ System build complete
    
    Manifests: 12/12 ✓
    Proof obligations: {N}/{N} discharged ✓
    
    Generated files:
      - Python files: {count} .py files ✓
      - Config files: pyproject.toml, etc. ✓
      - Infra files: Dockerfile, docker-compose.yaml ✓
    
    Validation:
      - All Python files parse ✓
      - docker-compose config valid ✓
    
    Deploy with: cd infrastructure && docker-compose up
    
  failure_indicators:
    # If you see these, the pipeline failed
    - "Code exists only inside YAML files"
    - "No .py files in generated/ directory"
    - "No Dockerfile in infrastructure/"
    - "Cannot run docker-compose up"
```
