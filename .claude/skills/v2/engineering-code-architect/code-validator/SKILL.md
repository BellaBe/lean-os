---
name: code-validator
description: |
  Validate all generated code for correctness and completeness. Gate skill for code
  layer. Checks syntax, types, imports, tests, and categorical correspondence.
  Must pass before proceeding to infrastructure layer.
  Input: All generated/python/**/*.py files
  Output: generated/versions.yaml, generated/validation-report.yaml
---

# Code Validator

Validate generated code and gate to infrastructure layer.

## Purpose

Final validation before infrastructure layer:
1. All Python syntax is valid
2. Type hints pass mypy
3. Imports resolve correctly
4. No circular dependencies
5. Tests pass
6. Categorical correspondence verified

## Input

```
generated/
├── python/
│   ├── pyproject.toml
│   └── src/{project}/
│       ├── domain/
│       ├── application/
│       ├── infrastructure/
│       └── api/
└── ...
```

## Output

```
generated/
├── versions.yaml
└── validation-report.yaml
```

## Validation Categories

### 1. Syntax Validation

```yaml
syntax_checks:
  python_compile:
    command: "python -m py_compile {file}"
    expected: exit_code_0
    for_each: "**/*.py"
    
  ast_parse:
    check: "All files parse to valid AST"
```

### 2. Type Checking

```yaml
type_checks:
  mypy:
    command: "mypy src/{project} --strict"
    expected: exit_code_0
    config:
      strict: true
      ignore_missing_imports: false
      
  type_coverage:
    minimum: 95%
    check: "Percentage of code with type hints"
```

### 3. Import Validation

```yaml
import_checks:
  resolve:
    check: "All imports resolve to existing modules"
    
  no_circular:
    check: "No circular import dependencies"
    tool: "pydeps --check-circular"
    
  layer_violations:
    check: "No layer boundary violations"
    rules:
      - "domain/ cannot import from application/, infrastructure/, api/"
      - "application/ cannot import from infrastructure/, api/"
      - "infrastructure/ can import from domain/, application/"
      - "api/ can import from application/, domain/"
```

### 4. Structural Validation

```yaml
structural_checks:
  entities_complete:
    check: "All ADT types have entity implementations"
    
  repositories_complete:
    check: "All entities have repositories"
    
  services_complete:
    check: "All aggregates have services"
    
  handlers_complete:
    check: "All services have route handlers"
    
  dtos_complete:
    check: "All endpoints have request/response DTOs"
```

### 5. Categorical Correspondence

```yaml
categorical_checks:
  functor_laws:
    check: "HTTP functor implementations preserve identity and composition"
    verify:
      - "Response.from_domain(Entity.default()) preserves identity"
      - "Response.from_domain(f(g(x))) == Response.from_domain(f(Response.from_domain(g(x))))"
      
  adjunction_laws:
    check: "Repository adjunction satisfies triangle identities"
    verify:
      - "create(entity).get(id) returns equivalent entity"
      - "Round-trip preserves structure"
      
  monad_laws:
    check: "Effect handling follows monad laws"
    verify:
      - "Service methods compose associatively"
      - "Result bind is associative"
      
  naturality:
    check: "Middleware are natural transformations"
    verify:
      - "Middleware don't modify request/response content"
```

### 6. Test Validation

```yaml
test_checks:
  tests_exist:
    check: "Test files exist for all modules"
    pattern: "tests/**/*_test.py"
    
  tests_pass:
    command: "pytest tests/ -v"
    expected: exit_code_0
    
  coverage:
    command: "pytest --cov=src/{project} --cov-report=term"
    minimum: 80%
```

### 7. Linting

```yaml
lint_checks:
  ruff:
    command: "ruff check src/{project}"
    expected: exit_code_0
    
  ruff_format:
    command: "ruff format --check src/{project}"
    expected: exit_code_0
```

## Validation Process

```yaml
validation_process:
  steps:
    - name: check_structure
      action: "Verify all expected files exist"
      blocking: true
      
    - name: check_syntax
      action: "Compile all Python files"
      blocking: true
      
    - name: check_imports
      action: "Verify imports resolve"
      blocking: true
      
    - name: check_circular
      action: "Detect circular imports"
      blocking: true
      
    - name: check_types
      action: "Run mypy type checking"
      blocking: true
      
    - name: check_layers
      action: "Verify layer boundaries"
      blocking: true
      
    - name: check_categorical
      action: "Verify categorical correspondence"
      blocking: false  # Warning only
      
    - name: run_tests
      action: "Execute test suite"
      blocking: true
      
    - name: check_coverage
      action: "Verify test coverage"
      blocking: false  # Warning if below threshold
      
    - name: lint
      action: "Run linting"
      blocking: false  # Warning only
      
    - name: generate_report
      action: "Create validation report"
```

## Output Schemas

### validation-report.yaml

```yaml
# generated/validation-report.yaml

validation_report:
  timestamp: "2024-01-15T12:00:00Z"
  code_version: "1.0.0"
  maps_version: "1.0.0"
  proofs_version: "1.0.0"
  
  target: python
  python_version: "3.11"
  
  summary:
    status: pass
    total_checks: 45
    passed: 43
    failed: 0
    warnings: 2
    
  checks:
    syntax:
      status: pass
      files_checked: 42
      errors: 0
      
    types:
      status: pass
      command: "mypy src/glamyouup --strict"
      exit_code: 0
      type_coverage: 98%
      
    imports:
      status: pass
      details:
        - all_imports_resolve: true
        - circular_dependencies: 0
        - layer_violations: 0
        
    structure:
      status: pass
      entities: 5
      repositories: 5
      services: 5
      handlers: 15
      dtos: 20
      
    categorical:
      status: pass
      functor_laws: verified
      adjunction_laws: verified
      monad_laws: verified
      naturality: verified
      
    tests:
      status: pass
      total: 85
      passed: 85
      failed: 0
      coverage: 87%
      
    lint:
      status: warning
      ruff_errors: 0
      format_issues: 3
      
  warnings:
    - check: coverage
      value: 87%
      threshold: 90%
      message: "Test coverage below recommended threshold"
      
    - check: lint
      value: 3
      message: "3 formatting issues found (auto-fixable)"
      
  errors: []
  
  certificate_references:
    - proofs/certificates/functor.cert.yaml
    - proofs/certificates/adjunction.cert.yaml
    - proofs/certificates/monad.cert.yaml
    - proofs/certificates/naturality.cert.yaml
    
  gate_decision:
    result: proceed
    next_phase: infrastructure_layer
    conditions_met:
      - syntax_valid
      - types_valid
      - imports_resolve
      - no_layer_violations
      - tests_pass
      - categorical_verified
```

### versions.yaml

```yaml
# generated/versions.yaml

version: "1.0.0"
created_at: "2024-01-15T12:00:00Z"

dependencies:
  maps_version: "1.0.0"
  proofs_version: "1.0.0"
  standards_version: "1.0.0"
  specification_version: "1.0.0"

target: python
python_version: "3.11"
framework: fastapi

files:
  domain:
    - path: domain/entities/merchant.py
      hash: "sha256:abc123..."
    - path: domain/entities/profile.py
      hash: "sha256:def456..."
    # ...
    
  application:
    - path: application/services/merchant_service.py
      hash: "sha256:ghi789..."
    # ...
    
  infrastructure:
    - path: infrastructure/repositories/merchant_repository.py
      hash: "sha256:jkl012..."
    # ...
    
  api:
    - path: api/routes/merchant_routes.py
      hash: "sha256:mno345..."
    # ...

stats:
  total_files: 42
  total_lines: 4523
  entities: 5
  services: 5
  repositories: 5
  handlers: 15
  middleware: 4
  
categorical_coverage:
  functors: 100%
  adjunctions: 100%
  monads: 100%
  transformations: 100%
```

## Error Handling

```yaml
error_handling:
  blocking_errors:
    - syntax_error
    - type_error
    - import_error
    - circular_import
    - layer_violation
    - test_failure
    
  warnings:
    - coverage_low
    - lint_issues
    - missing_docstring
    - categorical_warning
    
  on_blocking_error:
    action: fail_gate
    report: detailed_error
    suggestions:
      - "Fix syntax error in {file}:{line}"
      - "Add type hint for {function}"
      - "Remove circular import between {a} and {b}"
    human_intervention: required
    
  on_warning:
    action: log_and_continue
    include_in_report: true
```

## Gate Decision

```yaml
gate_decision:
  pass_criteria:
    - syntax_valid: true
    - types_valid: true
    - imports_resolve: true
    - no_circular_imports: true
    - no_layer_violations: true
    - tests_pass: true
    - coverage >= 80%  # Soft threshold
    
  fail_reasons:
    - syntax_error: "Python compilation failed"
    - type_error: "mypy found type errors"
    - import_error: "Imports don't resolve"
    - circular_import: "Circular dependencies detected"
    - layer_violation: "Layer boundary violated"
    - test_failure: "Tests failed"
    
  on_pass:
    output:
      - versions.yaml
      - validation-report.yaml
    next: infrastructure_layer
    
  on_fail:
    output:
      - validation-report.yaml (with errors)
    action: halt_pipeline
    human_intervention: required
```

## Next Phase

On successful validation:

```
Code Validator (complete)
         │
         ▼
┌─────────────────────────────┐
│   infrastructure-architect  │ ← Next orchestrator
└─────────────────────────────┘
```
