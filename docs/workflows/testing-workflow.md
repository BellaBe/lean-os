# Testing Workflow

End-to-end testing capability for Python and TypeScript/JavaScript projects.

## Components

```
┌─────────────────────────────────────────────────────────────┐
│                     testing agent                           │
│                     (orchestrator)                          │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   ┌───────────┐  ┌───────────┐  ┌───────────┐  ┌─────────┐ │
│   │   code-   │  │   test-   │  │   bug-    │  │  test-  │ │
│   │   lint    │  │ execution │  │ diagnosis │  │  design │ │
│   └─────┬─────┘  └─────┬─────┘  └─────┬─────┘  └─────────┘ │
│         │              │              │                     │
│         │              │              ▼                     │
│         │              │       ┌─────────────┐              │
│         │              │       │ reasoning-  │              │
│         │              │       │  abductive  │              │
│         │              │       └─────────────┘              │
│         │              │                                    │
└─────────┼──────────────┼────────────────────────────────────┘
          │              │
          ▼              ▼
    ┌───────────┐  ┌─────────────┐
    │ ruff/mypy │  │   pytest    │  Python
    │eslint/tsc │  │   vitest    │  TypeScript/JavaScript
    └───────────┘  └─────────────┘
```

## File Locations

```
~/.claude/
├── agents/
│   └── testing.md                  # Orchestrator agent
└── skills/
    ├── code-lint/SKILL.md          # Lint, type check, format
    ├── test-execution/SKILL.md     # Run tests, parse output
    ├── bug-diagnosis/SKILL.md      # Backward chain to root cause
    ├── test-design/SKILL.md        # Write tests, coverage analysis
    └── reasoning-abductive/SKILL.md # Hypothesis ranking (existing)
```

## Supported Stacks

| Stack | Runner | Coverage | Async |
|-------|--------|----------|-------|
| Python (FastAPI) | pytest | pytest-cov | pytest-asyncio |
| TypeScript/JS Backend | Vitest | @vitest/coverage-v8 | native |
| Frontend (React/Remix/Next) | Vitest + Testing Library | @vitest/coverage-v8 | native |

## Workflows

### 1. Run Tests

```
User: "run tests"
      "test the auth module"
      "pytest"

Flow:
┌──────────────┐
│  code-lint   │ → Format, lint, type check (auto-fix)
└──────┬───────┘
       │
       ▼
   Errors?
       │
   ┌───┴───┐
   │       │
  None   Some unfixable
   │       │
   │       ▼
   │    Report (continue anyway)
   │       │
   ▼       ▼
┌──────────────┐
│ test-execution│ → Run pytest/vitest
└──────┬───────┘
       │
       ▼
   Pass/Fail?
       │
   ┌───┴───┐
   │       │
 Pass    Fail
   │       │
   ▼       ▼
 Done   [Diagnosis workflow]
```

### 2. Fix Failing Tests

```
User: "fix this test"
      "debug test_login"
      "why is this failing"

Flow:
┌──────────────┐
│ test-execution│ → Capture failure details
└──────┬───────┘
       │
       ▼
┌──────────────┐
│ bug-diagnosis │ → Backward chain from symptom
└──────┬───────┘
       │
       ▼
┌──────────────┐
│  abductive   │ → Rank hypotheses
└──────┬───────┘
       │
       ▼
   Confidence?
       │
   ┌───┴───┐
   │       │
  ≥0.7    <0.7
   │       │
   ▼       ▼
 Apply   Escalate
  Fix    to Human
   │
   ▼
┌──────────────┐
│  code-lint   │ → Ensure fix doesn't break types/lint
└──────┬───────┘
       │
       ▼
┌──────────────┐
│ test-execution│ → Verify fix
└──────┬───────┘
       │
       ▼
   Pass/Fail?
       │
   ┌───┴───┐
   │       │
 Pass    Fail
   │       │
   ▼       ▼
 Done   Iterate (max 3x)
```

### 3. Improve Coverage

```
User: "improve test coverage"
      "we need more tests for payments"
      "coverage report"

Flow:
┌──────────────┐
│ test-execution│ → Run with --coverage
└──────┬───────┘
       │
       ▼
┌──────────────┐
│ test-design  │ → Identify gaps, prioritize
└──────┬───────┘
       │
       ▼
   Generate test cases
       │
       ▼
   Write test file
       │
       ▼
┌──────────────┐
│ test-execution│ → Verify new tests pass
└──────────────┘
```

### 4. Write New Tests

```
User: "write tests for UserService"
      "test this function"
      "add tests for the login endpoint"

Flow:
┌──────────────┐
│ test-design  │ → Analyze code, identify cases
└──────┬───────┘
       │
       ▼
   Generate scaffold
       │
       ▼
   Write test file
       │
       ▼
┌──────────────┐
│  code-lint   │ → Ensure generated tests are clean
└──────┬───────┘
       │
       ▼
┌──────────────┐
│ test-execution│ → Run to verify
└──────────────┘
```

### 5. Lint Only

```
User: "lint the code"
      "check types"
      "run mypy"

Flow:
┌──────────────┐
│  code-lint   │ → Format, lint, type check
└──────┬───────┘
       │
       ├── Fixable → Auto-fix → Report fixed
       │
       └── Unfixable → Report with suggestions
```

## Reasoning Flow (Bug Diagnosis)

```
[Failure Symptom]
    │
    │ "AssertionError: expected 200, got 401"
    │
    ▼
[Stage 1: Symptom Analysis]
    │
    │ Parse error type, message, stack trace
    │
    ▼
[Stage 2: Backward Chaining]
    │
    │ test_login:45 ← service.login:23 ← token.validate:67
    │                                         ↑
    │                                    INVESTIGATE
    ▼
[Stage 3: Candidate Locations]
    │
    │ token.py:67 (confidence: 0.7)
    │ service.py:23 (confidence: 0.5)
    │
    ▼
[Stage 4: Hypothesis Generation] ──→ reasoning-abductive
    │
    │ H1: Token expiry check inverted (0.78)
    │ H2: Test fixture invalid (0.65)
    │ H3: Environment mismatch (0.45)
    │
    ▼
[Stage 5: Verification (Deductive)]
    │
    │ If H1 true → line 67 has inverted condition
    │ Check: grep, git blame, read file
    │ Result: Confirmed
    │
    ▼
[Stage 6: Root Cause + Fix]
    │
    │ Location: token.py:67
    │ Issue: `if not token.expired` should be `if token.expired`
    │ Confidence: 0.85
    │
    ▼
[Apply Fix] → [Verify] → Done
```

## Escalation Rules

**Auto-fix (stay in workflow):**
- Logic errors, typos, inverted conditions
- Missing null checks, type mismatches
- Test setup/fixture issues
- Confidence ≥0.7

**Escalate to human:**
- Security vulnerability discovered
- Architectural flaw requiring design decision
- Breaking change to public API/contract
- Confidence <0.7 after 3 iterations
- Test infrastructure issues

## Constraints

| Constraint | Value |
|------------|-------|
| Max fix iterations | 3 |
| Max lines per fix | 20 |
| Min confidence to auto-fix | 0.7 |
| Coverage target (default) | 80% |

## Commands Quick Reference

### Lint (Python)

```bash
# Format
ruff format .

# Lint + fix
ruff check . --fix

# Type check
mypy src/ --ignore-missing-imports

# All at once
ruff format . && ruff check . --fix && mypy src/
```

### Lint (TypeScript/JavaScript)

```bash
# Format
npx prettier --write "src/**/*.{ts,tsx,js,jsx}"

# Lint + fix
npx eslint . --fix

# Type check
npx tsc --noEmit

# All at once
npx prettier --write . && npx eslint . --fix && npx tsc --noEmit
```

### Python (pytest)

```bash
# Run all
pytest -v

# Run specific
pytest tests/test_auth.py::test_login -v

# With coverage
pytest --cov=src --cov-report=term-missing

# Failed only
pytest --lf -v

# Debug
pytest --pdb tests/test_auth.py::test_login
```

### TypeScript/JavaScript (Vitest)

```bash
# Run all
npx vitest run

# Run specific
npx vitest run src/auth.test.ts -t "login"

# With coverage
npx vitest run --coverage

# Watch mode
npx vitest

# Debug
npx vitest run --inspect-brk
```

### Git (for diagnosis)

```bash
# Recent changes
git log --oneline -10 -- src/auth/

# Blame specific lines
git blame -L 60,80 src/auth/token.py

# Diff from working state
git diff HEAD~5 -- src/
```

## Integration with Existing Skills

| Skill | Role in Testing |
|-------|-----------------|
| `code-lint` | Auto-fix formatting/imports, report type errors |
| `reasoning-abductive` | Ranks bug hypotheses by evidence |
| `reasoning-causal` | Not used (testing is self-contained) |

## Usage Examples

```bash
# Lint
"lint the code"
"check types"
"run mypy"
"fix lint errors"

# Run tests
"run the tests"
"pytest"
"test auth module"

# Fix failures
"fix the failing test"
"debug test_login_success"
"why is this test failing"

# Coverage
"show coverage report"
"improve coverage for payments"
"what's not tested?"

# Write tests
"write tests for UserService"
"add tests for the login endpoint"
"test this function"

# Specific patterns
"run only failed tests"
"test with verbose output"
"run tests matching 'auth'"
```

## Output Examples

### Lint (Pass)

```
## Lint Results

**Stack:** Python (ruff + mypy)

### Summary

| Status | Count |
|--------|-------|
| ✅ Fixed | 5 |
| ❌ Errors | 0 |

### Auto-Fixed

- `src/auth/service.py`: 2 import sorting
- `src/models/user.py`: 1 unused import removed
- `tests/test_auth.py`: 2 formatting

Ready for tests.
```

### Lint (With Errors)

```
## Lint Results

**Stack:** TypeScript (eslint + tsc)

### Summary

| Status | Count |
|--------|-------|
| ✅ Fixed | 3 |
| ❌ Errors | 2 |

### Errors (require manual fix)

1. `src/auth/service.ts:23:10` — **TS2339**
   Property 'toJSON' does not exist on type 'User'
   → Suggest: Did you mean `toDict()`? (found at User:45)

2. `src/auth/token.ts:67:5` — **TS7006**
   Parameter 'token' implicitly has 'any' type
   → Suggest: Add type `token: string` (inferred from usage)
```

### Test Run (Pass)

```
## Test Results

**Status:** ✅ Pass
**Stack:** Python (pytest)

| Metric | Value |
|--------|-------|
| Total | 42 |
| Passed | 42 |
| Failed | 0 |
| Duration | 3.2s |
| Coverage | 84% |
```

### Test Run (Fail + Fix)

```
## Test Results

**Status:** ❌ 2 failures

### Failures

1. `test_auth.py::test_login_success`
   - Error: AssertionError - expected 200, got 401
   - Location: line 45

---

## Diagnosis

**Root Cause:** Token expiry check inverted
**Location:** `src/auth/token.py:67`
**Confidence:** 0.85

---

## Fix Applied

```diff
- if not token.expired:
+ if token.expired:
```

**Verification:** ✅ All tests pass (42/42)
```

### Escalation

```
## Escalation Required

**Test:** `test_payments.py::test_refund`
**Reason:** Security vulnerability

Refund validation does not check amount against original charge.
Human review required before fix.

**Evidence:**
- Refund endpoint accepts any amount
- No validation in `process_refund()`
- Could allow refunds > charge amount
```