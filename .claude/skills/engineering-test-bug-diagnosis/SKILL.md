---
name: bug-diagnosis
description: Diagnose test failures and bugs using backward chaining from symptom to root cause. Use when tests fail, errors occur, or unexpected behavior observed. Integrates with reasoning-abductive for hypothesis ranking.
allowed-tools: Read, Grep, Glob, Bash
---

# Bug Diagnosis

Backward chain from failure to root cause. The logic of debugging.

## Type Signature

```
Diagnose : Failure → BackwardChain → Hypotheses → RootCause

Where:
  Failure       : ErrorType × Message × StackTrace × Context
  BackwardChain : StackTrace → [ExecutionStep] → CandidateLocations
  Hypotheses    : CandidateLocations → [PossibleCause]  # → reasoning-abductive
  RootCause     : [ScoredHypothesis] → (Cause × Fix × Confidence)
```

## When to Use

- Test failure with unclear cause
- Runtime error in production/staging
- Unexpected behavior (wrong output, no output)
- Performance regression
- Intermittent failures

## Reasoning Flow

```
[Failure Symptom]
       ↓
[Backward Chain] ← Trace execution in reverse
       ↓
[Candidate Locations] ← Where could this originate?
       ↓
[Hypotheses] → [reasoning-abductive] ← Rank by evidence
       ↓
[Root Cause + Fix Proposal]
```

## Stage 1: Symptom Analysis

**Extract from failure:**

```yaml
symptom:
  error_type: "AssertionError"
  message: "assert response.status_code == 200, got 401"
  file: "tests/test_auth.py"
  line: 45
  test_name: "test_login_success"
  
  stack_trace:
    - frame: "test_login_success"
      file: "tests/test_auth.py"
      line: 45
    - frame: "login"
      file: "src/auth/service.py"
      line: 23
    - frame: "validate_token"
      file: "src/auth/token.py"
      line: 67
      
  context:
    last_passed: "2 days ago"
    recent_changes: ["src/auth/token.py", "src/auth/service.py"]
    environment: "test"
```

**Symptom Categories:**

| Category | Indicators | Initial Focus |
|----------|------------|---------------|
| **Assertion** | AssertionError, expect().toBe() | Test expectation vs actual |
| **Type** | TypeError, undefined is not | Data shape, null handling |
| **Reference** | NullPointerException, undefined | Missing initialization |
| **Import** | ModuleNotFoundError, Cannot find | Dependencies, paths |
| **Timeout** | TimeoutError, exceeded | Async, external calls |
| **State** | Inconsistent results | Race conditions, side effects |

## Stage 2: Backward Chaining

**Process:** Walk stack trace in reverse, identifying state changes.

```
[Failure Point] → test_auth.py:45 (assertion failed)
       ↑
[Last Known State] → service.py:23 (response received)
       ↑
[State Change] → token.py:67 (token validated) ← INVESTIGATE
       ↑
[Origin] → Where was token created?
```

**For each frame, ask:**
1. What was the expected state here?
2. What was the actual state?
3. What transformed the state between this frame and the previous?

**Tracing Commands:**

```bash
# Find function definition
grep -rn "def validate_token" src/

# Find all callers
grep -rn "validate_token(" src/ tests/

# Find recent changes to file
git log --oneline -10 -- src/auth/token.py

# Find what changed between working and broken
git diff HEAD~5 -- src/auth/
```

## Stage 3: Candidate Locations

**Narrow to likely sources:**

```yaml
candidates:
  - location: "src/auth/token.py:67"
    reason: "Last frame before failure, handles validation"
    confidence: 0.7
    
  - location: "src/auth/service.py:23"
    reason: "Calls validate_token, may pass wrong args"
    confidence: 0.5
    
  - location: "src/auth/models.py:12"
    reason: "Token model definition, recent change"
    confidence: 0.4
```

**Prioritization factors:**
- Recency of change (git log)
- Proximity to failure (stack depth)
- Complexity of code (cyclomatic)
- Test coverage gaps

## Stage 4: Hypothesis Generation

**Hand off to reasoning-abductive:**

```yaml
# Input to reasoning-abductive
observation:
  raw_data: "401 returned instead of 200 on login"
  context:
    expected: "200 OK with token"
    actual: "401 Unauthorized"
    candidate_locations: [candidates from Stage 3]
  surprise_level: 0.6

# Request hypothesis generation with debugging categories
hypothesis_categories:
  - logic_error      # Wrong condition, inverted check
  - null_reference   # Missing data, uninitialized
  - type_mismatch    # Wrong type, shape changed
  - state_corruption # Side effects, race condition
  - external_change  # API, database, environment
  - test_setup       # Fixture, mock, setup issue
```

**Receive ranked hypotheses from abductive:**

```yaml
hypotheses:
  - id: H1
    cause: "Token expiry check inverted after refactor"
    category: logic_error
    location: "src/auth/token.py:67"
    score: 0.78
    
  - id: H2
    cause: "Test fixture not providing valid token"
    category: test_setup
    location: "tests/conftest.py:23"
    score: 0.65
```

## Stage 5: Verification (Deductive)

**For each hypothesis, derive testable predictions:**

```yaml
H1_verification:
  hypothesis: "Token expiry check inverted"
  predictions:
    - "Line 67 should have `if token.expired` not `if not token.expired`"
    - "Valid tokens should pass, expired should fail"
    - "git blame shows recent change to this line"
    
  tests:
    - command: "grep -n 'expired' src/auth/token.py"
      expected: "if token.expired:"
      
    - command: "git log -1 --format='%s' -- src/auth/token.py"
      expected: "Recent commit message mentioning expiry"
```

**Verification commands:**

```bash
# Check specific line
sed -n '67p' src/auth/token.py

# Check git blame
git blame -L 65,70 src/auth/token.py

# Run minimal reproducer
pytest tests/test_auth.py::test_login_success -v --tb=long

# Add debug output
pytest tests/test_auth.py::test_login_success -v -s --capture=no
```

## Stage 6: Root Cause + Fix

**Output:**

```yaml
diagnosis:
  root_cause:
    location: "src/auth/token.py:67"
    issue: "Expiry check inverted in commit abc123"
    evidence:
      - "Line reads `if not token.expired` instead of `if token.expired`"
      - "Commit abc123 refactored expiry logic 2 days ago"
      - "All login tests passed before this commit"
    confidence: 0.85
    
  fix:
    type: "logic_correction"
    change:
      file: "src/auth/token.py"
      line: 67
      before: "if not token.expired:"
      after: "if token.expired:"
    rationale: "Condition was inverted during refactor"
    
  verification:
    command: "pytest tests/test_auth.py -v"
    expected: "All tests pass"
    
  related_risks:
    - "Check other usages of expired flag"
    - "Review commit abc123 for similar inversions"
```

## Escalation Criteria

**Stay within testing workflow (99% of cases):**
- Logic errors, typos, inverted conditions
- Missing null checks, type mismatches
- Test setup issues, fixture problems
- Dependency updates needed

**Escalate to human/causal only when:**
- Security vulnerability discovered
- Architectural flaw requiring design decision
- Breaking change affecting external contracts
- Root cause unclear after diagnosis (confidence <0.5)

```yaml
escalation:
  needed: false  # Default
  reason: null
  # If true: Flag for human review, don't auto-fix
```

## Output Contract

```yaml
bug_diagnosis:
  symptom:
    error_type: string
    message: string
    location: string
    stack_depth: int
    
  backward_chain:
    frames_analyzed: int
    candidate_count: int
    key_transition: string  # Where state went wrong
    
  root_cause:
    location: string
    issue: string
    category: string  # logic_error | null_reference | type_mismatch | state_corruption | external_change | test_setup
    confidence: float
    evidence: [string]
    commit: string?  # If identifiable
    
  fix:
    type: "one_liner" | "multi_line" | "refactor"
    changes: [
      {
        file: string
        line: int
        before: string
        after: string
      }
    ]
    rationale: string
    
  verification:
    command: string
    expected: string
    
  escalation:
    needed: boolean
    reason: string?  # security | architectural | breaking_change | low_confidence
    
  trace:
    stages_completed: [1, 2, 3, 4, 5, 6]
    hypotheses_evaluated: int
    abductive_used: boolean
```

## Common Bug Patterns

| Pattern | Symptom | Typical Cause |
|---------|---------|---------------|
| **Off-by-one** | Boundary failures | Loop/index logic |
| **Null deref** | TypeError/NullPointer | Missing guard |
| **Race condition** | Intermittent failure | Async ordering |
| **State leak** | Tests pass alone, fail together | Shared state |
| **Mock drift** | Test passes, prod fails | Mock outdated |
| **Env mismatch** | Works locally, fails CI | Missing env var |

## Quick Commands

```bash
# Reproduce with maximum verbosity
pytest path/to/test.py::test_name -vvv --tb=long -s

# Find what changed
git diff HEAD~5 -- src/

# Blame specific lines
git blame -L 60,80 src/file.py

# Search for pattern across codebase
grep -rn "pattern" src/ --include="*.py"

# Run with debugger (Python)
pytest --pdb path/to/test.py::test_name

# Run with debugger (Vitest)
npx vitest run path/to/test.ts --inspect-brk
```