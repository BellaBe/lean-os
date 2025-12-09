---
name: system-architect
description: Transform natural language requirements into mathematically verified specifications with proofs. Use when building new systems or features from requirements documents. Orchestrates 9 sub-skills to produce ADT specifications, type proofs, categorical architecture, API specs, and version migration strategies.
allowed-tools: Read, Write, Bash
version: 1.0.0
---

# System Architect

## Purpose

Transform requirements from `threads/engineering/{requirement}/` into complete mathematical specifications with proofs in `artifacts/engineering/specifications/v{X}/`.

## Input Sources

1. `threads/engineering/{requirement}/1-input.md` - Natural language requirements
2. `threads/engineering/{requirement}/2-hypothesis.md` - Technical feasibility
3. `threads/engineering/{requirement}/3-implication.md` - Effort estimates, ROI
4. `threads/engineering/{requirement}/4-decision.md` - BUILD/DEFER/KILL verdict

## Output Destination

```
artifacts/engineering/specifications/
├── manifest.json                      # Content hashes (immutable)
└── v{X}/                              # Versioned snapshot
    ├── requirements.adt               # From adt-analyzer
    ├── types.curry-howard             # From curry-howard-prover
    ├── architecture.categorical       # From functor-generator + system-optimizer
    ├── api.openapi.json              # OpenAPI 3.1 spec
    ├── services.spec.yaml            # Service boundaries
    ├── state-machines.yaml           # From state-machine-validator
    └── versions.yaml                 # From version-compatibility-prover
```

## Orchestration Workflow

When invoked, execute sub-skills in this order:

### Phase 1: Requirements Analysis (3 sub-skills)

1. **adt-analyzer**: Parse requirements → `requirements.adt`
   - Input: Natural language from Stage 1
   - Output: Algebraic expression with expanded paths
   - Example: `Tenant × ({Platform} + {AltPlatform}) → 12 paths`

2. **algebraic-structure-validator**: Validate ADT correctness
   - Input: `requirements.adt`
   - Validates: Distributivity, commutativity, type consistency
   - Output: Validation report OR fixes

3. **functor-generator**: Generate functors for each pattern
   - Input: Validated ADT paths
   - Detects: Multi-tenant, optional, collections, async
   - Output: `architecture.categorical` (functor definitions)

### Phase 2: Composition & Optimization (3 sub-skills)

4. **natural-transformation-engine**: Version migrations
   - Input: Functors, version requirements
   - Generates: Natural transformations (α: V1 → V2)
   - Output: `versions.yaml`

5. **curry-howard-prover**: Type proofs
   - Input: ADT paths, functors
   - Proves: All functions total, no impossible states
   - Output: `types.curry-howard`

6. **system-optimizer**: Apply algebraic laws
   - Input: Type signatures, composition graph
   - Optimizes: Factor common expressions, parallel execution
   - Output: Optimized implementation plan in `architecture.categorical`

### Phase 3: Validation (3 sub-skills)

7. **architecture-validator**: Categorical law verification
   - Input: All specifications, proofs
   - Validates: Composition, identity, associativity, functor laws
   - Runs: 10K property-based tests
   - Output: `proofs/architecture/validation-report.json`

8. **state-machine-validator**: State transition proofs
   - Input: ADT with state annotations
   - Validates: Reachability, determinism, completeness
   - Output: `state-machines.yaml` + proofs

9. **version-compatibility-prover**: Migration correctness
   - Input: API version differences
   - Proves: Backward compatibility OR documents breaking changes
   - Output: Migration/rollback code in `versions.yaml`

## Execution Instructions

### Step 1: Initialize Output Directory

```bash
# Create version directory
VERSION=$(date +%Y%m%d_%H%M%S)
mkdir -p artifacts/engineering/specifications/v${VERSION}
mkdir -p artifacts/engineering/proofs/architecture/{adt-validation,type-proofs,composition-proofs,functor-laws,natural-transformations,state-machine-proofs,version-compatibility}

# Store version in environment
echo "SPEC_VERSION=v${VERSION}" > /tmp/system-architect-session.env
```

### Step 2: Execute Phase 1 (Requirements Analysis)

```bash
# Invoke sub-skills sequentially
{baseDir}/scripts/orchestrate.py \
  --phase 1 \
  --requirement threads/engineering/{requirement} \
  --output artifacts/engineering/specifications/v${VERSION}
```

The script will:
1. Call `adt-analyzer` → Parse requirements
2. Call `algebraic-structure-validator` → Validate ADT
3. Call `functor-generator` → Generate functors

If any sub-skill fails, stop and report error to human in `ops/today.md`.

### Step 3: Execute Phase 2 (Composition & Optimization)

```bash
{baseDir}/scripts/orchestrate.py \
  --phase 2 \
  --requirement threads/engineering/{requirement} \
  --output artifacts/engineering/specifications/v${VERSION}
```

The script will:
4. Call `natural-transformation-engine` → Version migrations
5. Call `curry-howard-prover` → Type proofs
6. Call `system-optimizer` → Optimize architecture

### Step 4: Execute Phase 3 (Validation)

```bash
{baseDir}/scripts/orchestrate.py \
  --phase 3 \
  --requirement threads/engineering/{requirement} \
  --output artifacts/engineering/specifications/v${VERSION}
```

The script will:
7. Call `architecture-validator` → Validate laws (10K tests)
8. Call `state-machine-validator` → Validate state machines
9. Call `version-compatibility-prover` → Prove migrations

### Step 5: Generate Manifest

```bash
{baseDir}/scripts/generate_manifest.py \
  --version v${VERSION} \
  --output artifacts/engineering/specifications/manifest.json
```

Manifest format:
```json
{
  "version": "v20250120_143022",
  "created_at": "2025-01-20T14:30:22Z",
  "requirement": "multi-tenant-catalog-sync",
  "files": {
    "requirements.adt": "sha256:abc123...",
    "types.curry-howard": "sha256:def456...",
    "architecture.categorical": "sha256:ghi789..."
  },
  "validation": {
    "laws_checked": 47,
    "laws_passed": 47,
    "property_tests": 10000
  }
}
```

### Step 6: Generate OpenAPI Spec

```bash
{baseDir}/scripts/generate_openapi.py \
  --input artifacts/engineering/specifications/v${VERSION} \
  --output artifacts/engineering/specifications/v${VERSION}/api.openapi.json
```

### Step 7: Report Completion

Add to `threads/engineering/{requirement}/5-actions/action-1-architecture.md`:

```markdown
## Execution Log

**Status:** COMPLETE
**Version:** v{VERSION}
**Timestamp:** {ISO8601}

### Generated Artifacts

- ✅ `requirements.adt` - 12 paths enumerated
- ✅ `types.curry-howard` - All functions proven total
- ✅ `architecture.categorical` - Functors + natural transformations
- ✅ `api.openapi.json` - OpenAPI 3.1 specification
- ✅ `services.spec.yaml` - Service boundaries
- ✅ `state-machines.yaml` - State machines validated
- ✅ `versions.yaml` - Migration strategies

### Validation Summary

- Algebraic laws: 47/47 passed
- Property tests: 10,000/10,000 passed
- Type proofs: All verified
- State machines: All reachable, deterministic

### Next Steps

Specifications ready for:
1. **backend-prover**: Generate Phase 1 maps (structural specifications)
2. **frontend-prover**: Generate client code
3. **infrastructure-prover**: Generate deployment configs
```

## Error Handling

If any sub-skill fails:

1. Log error in action log
2. Flag in `ops/today.md`:
```markdown
⚠️ System Architect Failed: {sub-skill-name}
- Thread: threads/engineering/{requirement}/
- Error: {error message}
- Action: Review and retry/abort
```
3. Do NOT proceed to next phase
4. Wait for human intervention

## Critical Rules

✅ Always execute sub-skills in order (dependencies)
✅ Validate each phase before proceeding
✅ Generate immutable manifest (content hashes)
✅ All proofs must pass before completion
✅ Store specifications in versioned snapshots (never overwrite)

✗ Never skip validation steps
✗ Never proceed if proofs fail
✗ Never modify previous specification versions
✗ Never execute phases in parallel (strict ordering)

## Success Criteria

Specifications are complete when:

1. ✅ All 9 sub-skills executed successfully
2. ✅ ADT validated (algebraic laws hold)
3. ✅ Type proofs verified (Curry-Howard)
4. ✅ Categorical laws validated (10K property tests)
5. ✅ State machines proven (reachability, determinism)
6. ✅ Version migrations proven (backward compatibility)
7. ✅ Manifest generated (immutable hashes)

## Progressive Disclosure

This SKILL.md provides orchestration logic. Sub-skill details are in:
- `{baseDir}/adt-analyzer/SKILL.md`
- `{baseDir}/algebraic-structure-validator/SKILL.md`
- `{baseDir}/functor-generator/SKILL.md`
- `{baseDir}/natural-transformation-engine/SKILL.md`
- `{baseDir}/curry-howard-prover/SKILL.md`
- `{baseDir}/system-optimizer/SKILL.md`
- `{baseDir}/architecture-validator/SKILL.md`
- `{baseDir}/state-machine-validator/SKILL.md`
- `{baseDir}/version-compatibility-prover/SKILL.md`

Load sub-skills as needed during orchestration.