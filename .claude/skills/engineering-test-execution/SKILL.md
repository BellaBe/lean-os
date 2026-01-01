---
name: test-execution
description: Execute tests and parse results for Python (pytest) and TypeScript/JavaScript (Vitest). Use when running tests, checking coverage, or capturing failures for diagnosis.
allowed-tools: Read, Bash, Glob, Grep
---

# Test Execution

Run tests, parse output, identify failures. Stack-aware execution.

## Type Signature

```
Execute : TestTarget → RunConfig → TestResult

Where:
  TestTarget : Path | Pattern | "all"
  RunConfig  : Stack × Coverage × Verbosity × Filter
  TestResult : PassCount × FailCount × [Failure] × CoverageReport?
```

## Stack Detection

```bash
# Auto-detect from project root
if [ -f "pyproject.toml" ] || [ -f "pytest.ini" ]; then
  STACK="python"
elif [ -f "vitest.config.ts" ] || [ -f "vitest.config.js" ]; then
  STACK="vitest"
elif [ -f "package.json" ]; then
  # Check for vitest in devDependencies
  STACK="vitest"  # Default for TS/JS
fi
```

## Execution Commands

### Python (pytest)

```bash
# Run all tests
pytest -v --tb=short

# Run with coverage
pytest --cov=src --cov-report=term-missing --cov-report=html

# Run specific file/pattern
pytest tests/test_auth.py -v
pytest -k "test_login" -v

# Run failed only (from last run)
pytest --lf -v

# Async tests (FastAPI)
pytest -v --asyncio-mode=auto
```

**Required packages:**
```
pytest
pytest-asyncio
pytest-cov
httpx  # For FastAPI TestClient alternative
```

### TypeScript/JavaScript (Vitest)

```bash
# Run all tests
npx vitest run

# Run with coverage
npx vitest run --coverage

# Run specific file/pattern
npx vitest run src/auth.test.ts
npx vitest run -t "login"

# Watch mode (interactive)
npx vitest

# UI mode
npx vitest --ui
```

**Required packages:**
```
vitest
@vitest/coverage-v8
@testing-library/react  # For frontend
@testing-library/dom
```

## Output Parsing

### Failure Structure

```yaml
failure:
  file: string           # tests/test_auth.py or src/auth.test.ts
  test_name: string      # test_login_success or "should login successfully"
  line: int              # Line where assertion failed
  error_type: string     # AssertionError, TypeError, etc.
  message: string        # Expected X, got Y
  stack_trace: [Frame]   # Call stack
  stdout: string?        # Captured output
  duration_ms: int
```

### Parse pytest Output

```
FAILED tests/test_auth.py::test_login - AssertionError: assert 401 == 200
```

Extract:
- `file`: tests/test_auth.py
- `test_name`: test_login
- `error_type`: AssertionError
- `message`: assert 401 == 200

### Parse Vitest Output

```
FAIL  src/auth.test.ts > AuthService > should login successfully
AssertionError: expected 401 to equal 200
```

Extract:
- `file`: src/auth.test.ts
- `test_name`: AuthService > should login successfully
- `error_type`: AssertionError
- `message`: expected 401 to equal 200

## Coverage Thresholds

```yaml
coverage:
  minimum:
    lines: 80
    branches: 75
    functions: 80
  
  critical_paths:  # Higher threshold
    - src/auth/*: 90
    - src/payments/*: 95
```

### Coverage Commands

**Python:**
```bash
pytest --cov=src --cov-fail-under=80
```

**Vitest:**
```bash
# vitest.config.ts
export default defineConfig({
  test: {
    coverage: {
      thresholds: {
        lines: 80,
        branches: 75,
        functions: 80
      }
    }
  }
})
```

## Output Contract

```yaml
test_result:
  summary:
    total: int
    passed: int
    failed: int
    skipped: int
    duration_ms: int
    
  failures: [
    {
      file: string
      test_name: string
      line: int
      error_type: string
      message: string
      stack_trace: [string]
      relevant_code: string  # Snippet around failure
    }
  ]
  
  coverage:
    lines: float
    branches: float
    functions: float
    uncovered_files: [string]
    
  stack: "python" | "vitest"
  command_used: string
```

## Execution Flow

```
1. Detect stack (Python/Vitest)
2. Check test config exists
3. Run tests with appropriate flags
4. Parse output into structured result
5. If failures: Extract failure details for bug-diagnosis
6. If coverage requested: Include coverage report
```

## Error Handling

| Error | Detection | Action |
|-------|-----------|--------|
| No tests found | "no tests ran" / "No test files found" | Check test file patterns |
| Import error | "ImportError" / "Cannot find module" | Report dependency issue |
| Fixture error | "fixture not found" | List available fixtures |
| Timeout | Process exceeds limit | Kill and report partial |
| Config error | "Error in config" | Show config validation |

## Integration Points

**To bug-diagnosis:**
```yaml
handoff:
  failures: [Failure]      # Structured failure data
  stack: string            # For stack-specific tracing
  test_command: string     # To reproduce
  relevant_files: [string] # Files touched by failing tests
```

## Quick Reference

| Task | Python | Vitest |
|------|--------|--------|
| Run all | `pytest -v` | `npx vitest run` |
| Run file | `pytest path -v` | `npx vitest run path` |
| Run pattern | `pytest -k "name"` | `npx vitest run -t "name"` |
| Coverage | `pytest --cov=src` | `npx vitest run --coverage` |
| Failed only | `pytest --lf` | `npx vitest run --changed` |
| Watch | `pytest-watch` | `npx vitest` |
| Verbose | `pytest -vv` | `npx vitest run --reporter=verbose` |