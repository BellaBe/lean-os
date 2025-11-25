# LeanOS Roadmap

Future development phases for the engineering layer.

---

## Current State: Phase 1 Complete

**Version:** 1.2 (Generic Framework Release)

**Engineering skills operational:**
- `engineering-system-architecture` - Requirements → Mathematical specs
- `engineering-backend-prover` - Specs → Verified backend code
- `engineering-frontend-prover` - Specs → Type-safe frontend
- `engineering-infrastructure-prover` - Specs → Deployment configs
- `engineering-proof-composer` - Validate proof chain
- `engineering-standardization-definer` - Define cross-cutting standards
- `engineering-standardization-applier` - Apply standards to services

---

## Phase 2: Inverse Transformations & Effect System

**Focus:** Bidirectional verification and legacy system import

### New Sub-Skills (3)

#### 1.10 effect-system-analyzer (system-architect)
```
Input:  Type signatures from specifications
Output: effects.yaml
```
**Purpose:** Make side effects explicit (IO, Error, State)

**Why:** Prevent hidden IO in "pure" functions. Functions claiming to be pure but performing database calls or HTTP requests break compositional reasoning.

**Example output:**
```yaml
effects:
  sync_merchant:
    - IO: HTTP (Shopify API)
    - Error: NetworkError | ValidationError
    - State: MerchantCache (read/write)
  calculate_commission:
    - Pure: true  # No effects
```

#### 1.11 spec-to-requirements-extractor (system-architect)
```
Input:  specifications/v{X}/
Output: requirements-reconstructed.md
```
**Purpose:** Verify specs satisfy original requirements (inverse direction)

**Why:** Validate roundtrip correctness. If we can't reconstruct requirements from specs, something was lost in translation.

**Verification:**
```
Requirements → Specs → Reconstructed Requirements
         ↓                      ↓
    Compare: Should be equivalent
```

#### 2.5 code-to-spec-analyzer (backend-prover)
```
Input:  Existing Python codebase
Output: specifications-inferred/v{X}/
```
**Purpose:** Import legacy systems into LeanOS

**Why:**
- Analyze existing code for migration
- Competitive analysis of open-source projects
- Onboard brownfield projects

**Use cases:**
- Import existing FastAPI/Django codebase
- Generate specs from competitor's SDK
- Document undocumented legacy systems

### Build Pipeline Additions (Phase 2)
```bash
15-verify-effect-system.sh              # Effects explicit?
16-validate-requirements-equivalence.sh # Specs = Requirements?
17-analyze-existing-code.sh             # Optional: import legacy
18-verify-inferred-specs.sh             # Optional: validate import
```

---

## Phase 3: Behavioral Equivalence & Optimization

**Focus:** Runtime correctness and code optimization

### New Sub-Skills (2)

#### 4.5 contract-test-generator (frontend-prover)
```
Input:  api.openapi.json
Output: Property-based tests
```
**Purpose:** Verify behavioral correctness (not just types)

**Why:** Type correspondence proves structural compatibility. Contract tests prove behavioral compatibility:
- Pagination actually returns next page
- Error codes match documented responses
- Auth tokens expire when specified
- Rate limits enforced correctly

**Output:**
```python
# Generated property-based tests
@given(page=st.integers(min_value=1, max_value=100))
def test_pagination_returns_correct_page(page):
    response = api.list_items(page=page)
    assert response.meta.current_page == page
    assert len(response.items) <= response.meta.per_page
```

#### 1.6 system-optimizer enhancement
```
New capability: Coproduct optimization
Input:  Platform = {Platform-A} + {Platform-B} + {Platform-C}
Output: Unified interface + adapters
```
**Purpose:** Reduce code duplication for sum types

**Why:** When supporting multiple platforms (coproduct/sum type), naive implementation duplicates logic. Optimizer extracts shared implementation.

**Example:**
```
Before: 3 separate implementations (1000 lines each = 3000 lines)
After:  1 shared implementation + 3 thin adapters (1000 + 3×100 = 1300 lines)
Result: 57% code reduction
```

**Optimization patterns:**
- Extract common interface
- Generate adapter layer
- Prove behavioral equivalence

### Build Pipeline Additions (Phase 3)
```bash
19-generate-contract-tests.sh           # Generate behavioral tests
20-run-contract-tests.sh                # Run 10K property tests
21-verify-coproduct-optimization.sh     # Verify optimizations
22-final-verification.sh                # All phases complete?
```

---

## Complete Build Pipeline (All Phases)

```bash
# Phase 1 (Current - Complete)
01-parse-requirements.sh
02-generate-adt-specs.sh
03-prove-type-correctness.sh
04-generate-architecture.sh
05-validate-composition.sh
06-generate-api-spec.sh
07-generate-backend-maps.sh
08-validate-backend-maps.sh
09-generate-backend-code.sh
10-generate-frontend-types.sh
11-prove-type-correspondence.sh
12-generate-infrastructure.sh
13-prove-topology.sh
14-compose-system-proof.sh

# Phase 2 (Planned)
15-verify-effect-system.sh
16-validate-requirements-equivalence.sh
17-analyze-existing-code.sh             # Optional
18-verify-inferred-specs.sh             # Optional

# Phase 3 (Planned)
19-generate-contract-tests.sh
20-run-contract-tests.sh
21-verify-coproduct-optimization.sh
22-final-verification.sh
```

---

## Summary

| Phase | Focus | New Skills | Duration |
|-------|-------|------------|----------|
| 1 | Core verification pipeline | 7 skills | Complete |
| 2 | Inverse transformations & effects | 3 sub-skills | Planned |
| 3 | Behavioral equivalence & optimization | 2 sub-skills | Planned |

**Total new sub-skills:** 5
**Total build steps:** 22 (14 current + 8 new)

---

## Contributing

Phase 2 and 3 skills follow the same patterns as Phase 1:
- Each skill has `SKILL.md` with clear input/output
- Mathematical foundations documented
- Verification scripts in build pipeline
- Integration with `engineering-proof-composer`

See [CONTRIBUTING.md](CONTRIBUTING.md) for contribution guidelines.
