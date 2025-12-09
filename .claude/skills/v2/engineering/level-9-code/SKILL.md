---
name: level-9-code
description: |
  Level 9: Code. Generate executable implementations from Levels 1-8.
  Each item from lower levels produces corresponding code with full
  traceability and certificate references.

  Input: artifacts/engineering/v{X}/manifests/level-0 through level-8
  Output: artifacts/engineering/v{X}/manifests/level-9.manifest.yaml + generated code

  IMPORTANT: All outputs are versioned under artifacts/engineering/v{X}/
  UNIVERSAL: Works for any domain. Multi-language support.
---

# Level 9: Code

Executable implementations of categorical structures.

## CRITICAL: Generate Actual Files

**Level 9 produces ACTUAL CODE FILES, not manifest descriptions of code.**

```yaml
output_distinction:
  manifest_file:
    path: "artifacts/engineering/v{X}/manifests/level-9.manifest.yaml"
    contains: "References to generated files, NOT code itself"
    example: |
      items:
        - id: "code.customer_service"
          artifact: "artifacts/engineering/v{X}/generated/python/src/project/modules/customers/service.py"
          status: "generated"

  actual_code_files:
    path: "artifacts/engineering/v{X}/generated/python/src/{project}/**/*.py"
    contains: "Real, executable Python code"
    example: |
      # FILE: generated/python/src/project/modules/customers/service.py
      from project.shared.interfaces import IRepository
      from project.domain.entities import Customer, CustomerId
      from project.shared.monads import App, Result
      
      class CustomerService:
          def __init__(self, repo: IRepository[Customer, CustomerId]):
              self._repo = repo
              
          async def get_customer(self, id: CustomerId) -> Result[AppError, Customer]:
              return await self._repo.get(id)
              
  WRONG_approach:
    description: "Code inside YAML is NOT executable"
    example: |
      # level-9.manifest.yaml - WRONG!
      items:
        - id: "code.customer_service"
          definition:
            code: |
              class CustomerService:
                  async def get_customer(self, id):
                      ...
    why_wrong: "This produces documentation, not a running system"
    
  RIGHT_approach:
    description: "Write actual .py files to disk"
    steps:
      1: "Create directory structure"
      2: "Write Python code to .py files using file creation"
      3: "Record file paths in manifest"
    validation: "Files must exist and parse with ast.parse()"
```

## Principle

Code generation is a functor from Manifest → SourceCode that preserves structure.

```
For each item in Levels 0-8:
  Generate corresponding code artifact
  Include trace to source
  Include certificate reference (where applicable)
  
Code(item) preserves:
  - Type relationships
  - Composition structure
  - Effect handling
  - Invariants
```

## Mapping

```yaml
level_to_code:
  level_0_primitives:
    types: "Type aliases / base types"
    identifiers: "NewType wrappers with factories"
    effects: "Effect type definitions"
    constraints: "Validated types with constructors"
    
  level_1_entities:
    entities: "Dataclass / struct / interface"
    enums: "Enum types"
    
  level_2_morphisms:
    morphisms: "Function signatures"
    identities: "Identity function implementations"
    
  level_3_modules:
    modules: "Service classes"
    
  level_4_categories:
    categories: "Module organization"
    
  level_5_functors:
    functors: "Transformation functions"
    http: "Handlers (to_dto, from_dto)"
    storage: "Models (to_model, from_model)"
    
  level_6_adjunctions:
    adjunctions: "Repository implementations"
    unit: "Save operations"
    counit: "Load operations"
    
  level_7_transformations:
    transformations: "Middleware / decorators"
    
  level_8_proofs:
    certificates: "Docstring references"
```

## Process

```yaml
process:
  step_1_load_all_manifests:
    inputs:
      - "level-0.manifest.yaml through level-8.manifest.yaml"
    action: "Load complete manifest chain"
    
  step_2_enumerate_code_items:
    action: "List all items that produce code"
    algorithm: |
      code_items = []
      for level in 0..8:
          for item in level.manifest.items:
              if produces_code(item):
                  code_items.append(CodeItem(item, level))
      return code_items
      
  step_3_partition_by_scope:
    action: "Separate shared from module items"
    algorithm: |
      shared_items = [i for i in code_items if i.scope == "shared"]
      module_items = [i for i in code_items if i.scope == "module"]
      internal_items = [i for i in code_items if i.scope == "internal"]
      
  step_4_topological_sort:
    action: "Order by dependencies within each partition"
    algorithm: |
      # Sort shared items by trace dependencies
      sorted_shared = topological_sort(shared_items, by=traces)
      
      # Sort module items (can depend on shared)
      sorted_module = topological_sort(module_items, by=traces)
      
      # Combine: shared first, then module
      sorted_items = sorted_shared + sorted_module + internal_items
      
  step_5_generate_shared:
    action: "Generate shared items FIRST as ACTUAL FILES"
    for_each: "item in sorted_shared"
    output_dir: "shared/{category}/"
    rationale: "Module items may import from shared"
    HOW: |
      For each shared item:
        1. Determine file path (e.g., shared/types/pagination.py)
        2. Generate Python code as string
        3. USE FILE CREATION TOOL to write actual .py file
        4. DO NOT put code inside manifest YAML
    
  step_6_generate_module:
    action: "Generate module-scoped items as ACTUAL FILES"
    for_each: "item in sorted_module"
    output_dir: "modules/{module}/ or appropriate location"
    HOW: "Same as step_5 - create actual files"
    
  step_7_generate_internal:
    action: "Generate internal items as ACTUAL FILES"
    for_each: "item in internal_items"
    output_dir: "modules/{module}/_internal/"
    HOW: "Same as step_5 - create actual files"
      
  step_8_validate_code:
    action: "Validate generated code FILES EXIST"
    checks:
      - files_exist: "All artifact paths exist on filesystem"
      - syntax_valid: "ast.parse() succeeds on each .py file"
      - types_valid: "Type checker passes"
      - imports_resolve: "All imports exist"
      - no_cycles: "No circular imports"
      - shared_before_module: "No module → shared dependencies"
    FAILURE_CHECK: |
      If only manifest exists and no .py files:
        HALT - "Code generation failed: only manifest created"
        
  step_9_produce_manifest:
    action: "Write level-9.manifest.yaml with file REFERENCES"
    note: "Manifest lists files that were created, does NOT contain code"
```

## Code Structure by Language

**All code is generated under `artifacts/engineering/v{X}/generated/`**

### Python

```
artifacts/engineering/v{X}/generated/python/src/{project}/
├── __init__.py
├── __main__.py
│
├── shared/                    # scope: shared items
│   ├── __init__.py
│   ├── types/                 # Level 1: shared entities
│   │   ├── __init__.py
│   │   ├── pagination.py      # Pagination, PaginatedResult[A]
│   │   ├── audit.py           # AuditInfo
│   │   └── sort.py            # SortSpec, SortDirection
│   ├── errors/                # Level 1: shared errors
│   │   ├── __init__.py
│   │   └── base.py            # AppError variants
│   ├── validation/            # Level 2: shared validators
│   │   ├── __init__.py
│   │   ├── email.py           # validate_email
│   │   └── common.py          # validate_not_empty, etc.
│   ├── interfaces/            # Level 3: shared interfaces
│   │   ├── __init__.py
│   │   ├── repository.py      # IRepository[E, Id]
│   │   └── service.py         # ICRUDService[E, ...]
│   ├── monads/                # Level 4: shared monads
│   │   ├── __init__.py
│   │   ├── app.py             # App, AppReader
│   │   └── result.py          # Result helpers
│   └── middleware/            # Level 7: shared transformations
│       ├── __init__.py
│       ├── auth.py            # Auth
│       ├── logging.py         # Logging
│       ├── metrics.py         # Metrics
│       └── chain.py           # compose_middleware()
│
├── primitives/                # Level 0
│   ├── __init__.py
│   ├── types.py
│   ├── identifiers.py
│   ├── effects.py
│   └── constraints.py
│
├── domain/                    # Level 1: module-scoped entities
│   ├── __init__.py
│   └── entities/
│       └── {entity_name}.py   # scope: module entities
│
├── morphisms/                 # Level 2
│   ├── __init__.py
│   └── signatures.py
│
├── application/               # Level 3
│   ├── __init__.py
│   ├── services/              # Module services
│   ├── dtos/                  # Level 5: HTTP functor objects
│   └── ports/                 # Interfaces
│
├── infrastructure/            # Levels 5, 6
│   ├── __init__.py
│   ├── models/                # Level 5: Storage functor objects
│   ├── repositories/          # Level 6: adjunction implementations
│   └── external/              # External API clients
│
└── api/                       # Levels 5, 7
    ├── __init__.py
    ├── routes/                # Level 5: HTTP functor morphisms
    └── middleware/            # References shared/middleware/
```

### TypeScript

```
artifacts/engineering/v{X}/generated/typescript/src/
├── index.ts
├── primitives/
│   ├── types.ts
│   ├── identifiers.ts
│   └── effects.ts
├── domain/
│   ├── entities/
│   └── enums/
├── application/
│   ├── services/
│   └── dtos/
├── infrastructure/
│   ├── models/
│   └── repositories/
└── api/
    ├── routes/
    └── middleware/
```

## Code Item Schema

```yaml
code_item:
  id: "code.{language}.{level}.{item_id}"
  source:
    level: N
    item: "{item_id}"
    manifest: "level-{N}.manifest.yaml"
  scope: "shared|module"           # Determines output directory
  artifact:
    path: "generated/{language}/..."
    checksum: "sha256"
  traces:
    - ref: "level-{N}.{item_id}"
      role: "specification"
    - ref: "level-8.proof.{proof_id}"
      role: "verified_by"
  status: "generated|validated"
```

## Scope-Based Generation

```yaml
generation_rules:
  shared:
    condition: "source item has scope: shared"
    output_dir: "shared/{category}/"
    generate_first: true  # Modules depend on shared
    
  module:
    condition: "source item has scope: module"
    output_dir: "modules/{module}/ or domain/entities/"
    generate_after: "shared items"
    
  internal:
    condition: "source item has scope: internal"
    output_dir: "modules/{module}/_internal/"
    export: false  # Not in __init__.py
```

## Manifest Item Schema

```yaml
manifest_item:
  id: "code.{level}.{item}"
  name: "{ItemName}"
  kind: "code"
  language: "{python|typescript|go}"
  traces:
    - ref: "level-{N}.{item_type}.{item_id}"
      role: "specification"
  definition:
    source_level: N
    source_item: "{item_id}"
    template: "{template_name}"
  artifacts:
    - path: "generated/{lang}/..."
      checksum: "sha256"
  status: "generated|validated"
```

## Validation Rules

```yaml
validation:
  completeness:
    rule: "∀ item ∈ Levels 0-7 (code-producing): ∃ code artifact"
    description: "Every item has generated code"
    critical: true
    
  syntax_valid:
    rule: "All files parse correctly"
    check: "Language-specific parser"
    critical: true
    
  types_valid:
    rule: "Type checker passes"
    check: "mypy / tsc / go vet"
    critical: true
    
  imports_resolve:
    rule: "All imports exist"
    critical: true
    
  no_circular:
    rule: "No circular import dependencies"
    critical: true
    
  traces_valid:
    rule: "All traces point to existing items"
    critical: true
```

## Output Structure

```
artifacts/engineering/v{X}/
├── manifests/
│   └── level-9.manifest.yaml
└── generated/
    ├── python/
    │   ├── pyproject.toml
    │   ├── src/{project}/
    │   │   └── ...
    │   └── tests/
    ├── typescript/
    │   ├── package.json
    │   ├── src/
    │   │   └── ...
    │   └── tests/
    └── go/
        ├── go.mod
        ├── ...
        └── tests/
```

## Invariant

```
∀ item ∈ (Level0 ∪ ... ∪ Level7) where produces_code(item):
  ∃ artifact ∈ Level9: artifact.traces(item)
  artifact.validated = true

|code_artifacts| ≥ |code_producing_items|

Violation is FATAL. Pipeline MUST NOT proceed to Level 10.
```

## Example (Illustrative Only)

```yaml
# artifacts/engineering/v1/manifests/level-9.manifest.yaml
items:
  # Level 0 → primitives
  - id: "code.python.level-0.identifier.CustomerId"
    kind: "code"
    language: "python"
    traces:
      - ref: "level-0.identifier.CustomerId"
        role: "specification"
    artifacts:
      - path: "artifacts/engineering/v1/generated/python/src/project/primitives/identifiers.py"
    status: "validated"

  # Level 1 → entities
  - id: "code.python.level-1.entity.Customer"
    kind: "code"
    language: "python"
    traces:
      - ref: "level-1.entity.Customer"
        role: "specification"
      - ref: "level-8.proof.identity.Customer"
        role: "verified_by"
    artifacts:
      - path: "artifacts/engineering/v1/generated/python/src/project/domain/entities/customer.py"
    status: "validated"

  # Level 3 → services
  - id: "code.python.level-3.module.customers"
    kind: "code"
    language: "python"
    traces:
      - ref: "level-3.module.customers"
        role: "specification"
      - ref: "level-8.proof.composition.customers"
        role: "verified_by"
    artifacts:
      - path: "artifacts/engineering/v1/generated/python/src/project/application/services/customer_service.py"
    status: "validated"

  # Level 6 → repositories
  - id: "code.python.level-6.adjunction.Free_Repository.Customer"
    kind: "code"
    language: "python"
    traces:
      - ref: "level-6.adjunction.Free_Repository"
        role: "specification"
      - ref: "level-8.proof.adjunction.Free_Repository.left_triangle"
        role: "verified_by"
    artifacts:
      - path: "artifacts/engineering/v1/generated/python/src/project/infrastructure/repositories/customer_repository.py"
    status: "validated"

  # Level 7 → middleware
  - id: "code.python.level-7.transformation.Auth"
    kind: "code"
    language: "python"
    traces:
      - ref: "level-7.transformation.Auth"
        role: "specification"
      - ref: "level-8.proof.naturality.Auth"
        role: "verified_by"
    artifacts:
      - path: "artifacts/engineering/v1/generated/python/src/project/api/middleware/auth.py"
    status: "validated"

counts:
  total: 45
  by_level:
    level_0: 15
    level_1: 8
    level_2: 10
    level_3: 3
    level_5: 4
    level_6: 3
    level_7: 2
    
validation:
  all_items_generated: true
  syntax_valid: true
  types_valid: true
  complete: true
```
