---
name: code-lint
description: Run linters and type checkers, auto-fix where possible. Use after code generation, before testing, or for code quality checks. Handles Python (ruff, mypy) and TypeScript/JavaScript (eslint, tsc, prettier).
allowed-tools: Read, Edit, Bash, Grep, Glob
---

# Code Lint

Run linters, type checkers, formatters. Auto-fix what's fixable.

## Type Signature

```
Lint : Files → LintConfig → LintResult

Where:
  Files      : Path | Pattern | "staged" | "changed"
  LintConfig : Stack × Rules × AutoFix
  LintResult : [Error] × [Warning] × [Fixed] × PassFail
```

## When to Use

- After generating code (catch AI mistakes)
- Before running tests (fail fast)
- Before committing (pre-commit hook behavior)
- Code review / quality check

## Execution Order

```
[Format] → [Lint] → [Type Check] → [Report]
    │          │           │
    ▼          ▼           ▼
  Auto      Auto       Report
  fixed     fixed      only
```

## Stack Detection

```bash
# Python
if [ -f "pyproject.toml" ] || [ -f "ruff.toml" ]; then
  STACK="python"
fi

# TypeScript/JavaScript
if [ -f "tsconfig.json" ]; then
  STACK="typescript"
elif [ -f "package.json" ]; then
  STACK="javascript"
fi
```

---

## Python Stack

### Tools

| Tool | Purpose | Auto-fix |
|------|---------|----------|
| ruff | Linting + formatting | Yes |
| mypy | Type checking | No |
| pyright | Type checking (stricter) | No |

### Commands

```bash
# Format (auto-fix)
ruff format src/ tests/

# Lint with auto-fix
ruff check src/ tests/ --fix

# Lint (report only)
ruff check src/ tests/

# Type check
mypy src/ --ignore-missing-imports

# Or pyright (stricter)
pyright src/
```

### Configuration

**pyproject.toml:**
```toml
[tool.ruff]
line-length = 88
target-version = "py311"

[tool.ruff.lint]
select = [
    "E",    # pycodestyle errors
    "W",    # pycodestyle warnings
    "F",    # pyflakes
    "I",    # isort
    "B",    # flake8-bugbear
    "UP",   # pyupgrade
    "ANN",  # flake8-annotations (types)
]
ignore = ["ANN101"]  # self type annotation

[tool.ruff.lint.isort]
known-first-party = ["src"]

[tool.mypy]
python_version = "3.11"
strict = true
ignore_missing_imports = true
```

### Common AI Errors (Python)

| Error Code | Issue | Auto-fix |
|------------|-------|----------|
| `ANN001` | Missing function arg type | No |
| `ANN201` | Missing return type | No |
| `F401` | Unused import | Yes |
| `F821` | Undefined name | No |
| `E501` | Line too long | Yes |
| `I001` | Import order | Yes |
| `UP035` | Deprecated typing import | Yes |

### Parse ruff Output

```
src/auth/token.py:67:5: ANN001 Missing type annotation for function argument `token`
```

Extract:
- `file`: src/auth/token.py
- `line`: 67
- `col`: 5
- `code`: ANN001
- `message`: Missing type annotation for function argument `token`
- `fixable`: No (ANN codes require context)

---

## TypeScript/JavaScript Stack

### Tools

| Tool | Purpose | Auto-fix |
|------|---------|----------|
| tsc | Type checking | No |
| eslint | Linting | Partial |
| prettier | Formatting | Yes |

### Commands

```bash
# Type check only (no emit)
npx tsc --noEmit

# Lint with auto-fix
npx eslint src/ --fix

# Lint (report only)
npx eslint src/

# Format
npx prettier --write "src/**/*.{ts,tsx,js,jsx}"

# Check formatting (no write)
npx prettier --check "src/**/*.{ts,tsx,js,jsx}"
```

### Configuration

**eslint.config.js (flat config):**
```javascript
import eslint from '@eslint/js';
import tseslint from 'typescript-eslint';

export default tseslint.config(
  eslint.configs.recommended,
  ...tseslint.configs.strict,
  {
    rules: {
      '@typescript-eslint/explicit-function-return-type': 'error',
      '@typescript-eslint/no-unused-vars': 'error',
      '@typescript-eslint/no-explicit-any': 'error',
    }
  }
);
```

**tsconfig.json:**
```json
{
  "compilerOptions": {
    "strict": true,
    "noImplicitAny": true,
    "strictNullChecks": true,
    "noUnusedLocals": true,
    "noUnusedParameters": true
  }
}
```

### Common AI Errors (TypeScript)

| Error | Issue | Auto-fix |
|-------|-------|----------|
| `TS2304` | Cannot find name 'X' | No |
| `TS2339` | Property does not exist | No |
| `TS2345` | Argument type mismatch | No |
| `TS7006` | Parameter implicitly has 'any' | No |
| `TS2307` | Cannot find module | No |
| `no-unused-vars` | Unused variable | Yes (remove) |
| `@typescript-eslint/explicit-function-return-type` | Missing return type | No |

### Parse tsc Output

```
src/auth/service.ts(23,5): error TS2339: Property 'toJSON' does not exist on type 'User'.
```

Extract:
- `file`: src/auth/service.ts
- `line`: 23
- `col`: 5
- `code`: TS2339
- `message`: Property 'toJSON' does not exist on type 'User'
- `fixable`: No

---

## Auto-Fix Strategy

### Fixable (apply automatically)

```yaml
fixable:
  - formatting (ruff format, prettier)
  - import sorting (isort, eslint)
  - unused imports (remove)
  - deprecated syntax (upgrade)
  - simple lint rules with --fix
```

### Unfixable (report + suggest)

```yaml
unfixable:
  - missing_type:
      report: "Missing type for argument `token`"
      suggest: "Add type based on usage: `token: str`"
      context: "Called with string literals in tests"
      
  - nonexistent_method:
      report: "Method `toJSON` does not exist on `User`"
      suggest: "Did you mean `to_dict()`?"
      context: "Similar method found: User.to_dict()"
      
  - wrong_signature:
      report: "Expected 0 arguments, got 1"
      suggest: "Check method definition or update call"
      context: "Definition at models.py:45"
```

### Suggest Similar

For non-existent methods/properties, find similar:

```bash
# Find similar method names
grep -rn "def to" src/models/user.py | head -5

# Find class definition
grep -rn "class User" src/
```

---

## Execution Flow

```
1. Detect stack (Python/TypeScript/JavaScript)
2. Check tool availability
3. Run formatter with auto-fix
4. Run linter with auto-fix
5. Run type checker (report only)
6. Collect remaining errors
7. For unfixable: suggest fixes based on context
8. Report summary
```

## Output Contract

```yaml
lint_result:
  stack: "python" | "typescript" | "javascript"
  
  summary:
    errors: int
    warnings: int
    fixed: int
    files_checked: int
    
  fixed:
    - file: string
      changes: int
      types: ["format", "import", "lint"]
      
  errors:
    - file: string
      line: int
      col: int
      code: string
      severity: "error" | "warning"
      message: string
      fixable: boolean
      suggestion: string?
      context: string?
      
  commands_run:
    - tool: string
      command: string
      exit_code: int
```

## Integration Points

### With Testing Agent

```yaml
# testing agent calls lint before tests
pre_test:
  - skill: code-lint
    mode: auto-fix
    fail_on: error  # Block tests if unfixable errors
```

### With Code Generation

```yaml
# After generating code
post_generate:
  - skill: code-lint
    mode: auto-fix
    report: unfixable_only
```

## Quick Reference

| Task | Python | TypeScript/JS |
|------|--------|---------------|
| Format | `ruff format .` | `npx prettier --write .` |
| Lint + fix | `ruff check . --fix` | `npx eslint . --fix` |
| Lint only | `ruff check .` | `npx eslint .` |
| Type check | `mypy src/` | `npx tsc --noEmit` |
| All (fix) | `ruff format . && ruff check . --fix && mypy src/` | `npx prettier --write . && npx eslint . --fix && npx tsc --noEmit` |

## Required Packages

### Python

```bash
pip install ruff mypy --break-system-packages
```

### TypeScript/JavaScript

```bash
npm install -D typescript eslint prettier @eslint/js typescript-eslint
```

## Error Categories

| Category | Examples | Action |
|----------|----------|--------|
| **Formatting** | Indentation, spacing, line length | Auto-fix |
| **Imports** | Unused, unsorted, missing | Auto-fix (except missing) |
| **Types** | Missing annotation, wrong type | Suggest based on context |
| **Reference** | Undefined name, non-existent property | Suggest similar |
| **Logic** | Unreachable code, unused variable | Auto-fix (remove) or report |

## Output Example

```
## Lint Results

**Stack:** Python (ruff + mypy)
**Files:** 12 checked

### Summary

| Status | Count |
|--------|-------|
| ✅ Fixed | 8 |
| ❌ Errors | 2 |
| ⚠️ Warnings | 1 |

### Auto-Fixed

- `src/auth/service.py`: 3 import sorting, 1 formatting
- `src/models/user.py`: 2 unused imports removed
- `tests/test_auth.py`: 2 formatting

### Errors (require manual fix)

1. `src/auth/token.py:67:5` — **ANN001**
   Missing type annotation for `token`
   → Suggest: `token: str` (inferred from test usage)

2. `src/auth/service.py:23:10` — **F821**
   Undefined name `TokenPayload`
   → Suggest: Add `from .models import TokenPayload`

### Warnings

1. `src/utils/helpers.py:12:1` — **W293**
   Blank line contains whitespace
   → Will fix on next format run
```