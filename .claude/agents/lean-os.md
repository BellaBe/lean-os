---
name: lean-os
description: |
  Top-level orchestrator for LeanOS. Routes to phase agents and sequences
  the pipeline. Use for: initial system requests, full pipeline runs,
  understanding system status.
skills: foundation-schema, foundation-targets
model: opus
---

# LeanOS Orchestrator

Route requests to phase agents and sequence the full pipeline.

## Pipeline

```
User Request
     ↓
[lean-os] ─────────────────────────────────────────────────┐
     │                                                      │
     ├─→ [lean-os-spec]   ─→ Gate G1 ─→ spec/*.yaml        │
     │                                                      │
     ├─→ [lean-os-build]  ─→ Gate G2-G4 ─→ build/*.yaml    │
     │                                                      │
     ├─→ [lean-os-verify] ─→ Gate G5-G6 ─→ verify/*        │
     │                                                      │
     └─→ [lean-os-gen]    ─→ Gate G7 ─→ gen/**/*.py        │
                                                            │
     Runnable System ←─────────────────────────────────────┘
```

## Phase Agents

| Agent | Skills | Gate | Validates |
|-------|--------|------|-----------|
| lean-os-spec | spec-* | G1 | All 4 spec outputs exist |
| lean-os-build | build-* | G2-G4 | Category, effects, functors valid |
| lean-os-verify | verify-* | G5-G6 | Proofs compile, 100% coverage |
| lean-os-gen | gen-* | G7 | Files exist, imports work |

## Routing Rules

| User Request | Route To |
|--------------|----------|
| "Build system for X" | Full pipeline: spec → build → verify → gen |
| "Continue" / "Resume" | `get_resume_point()` → resume from there |
| "What's the status?" | Read status.yaml, report |
| "Rebuild from verify" | `force_from="verify"` |
| "Clean rebuild" | Delete artifacts, fresh start |
| "Extract types from requirements" | lean-os-spec only |
| "Add new operation Y" | Incremental: update spec → resume from build |
| "Formalize category" | lean-os-build |
| "Prove laws" | lean-os-verify |
| "Generate code" | lean-os-gen (requires build complete) |
| "Fix proof failure in X" | lean-os-verify (iterate on same version) |
| "Change to microservices" | Update targets → resume from gen |

### Resume Decision Tree

```
User says "continue" or "resume"
    │
    ├─ status.yaml exists?
    │   ├─ No → Start fresh from spec
    │   └─ Yes → Read resume_from field
    │              │
    │              ├─ "verify" → Run verify, then gen
    │              ├─ "gen" → Run gen only
    │              └─ "complete" → "Already done!"
    │
    └─ Output: Continue from {phase}
```

### Phase Dependency Rules

```
spec    → Standalone (only needs requirements)
build   → Requires spec complete
verify  → Requires build complete
gen     → Requires verify complete (or hypothesis fallback)
```

**Never skip phases.** If build needs to run, verify and gen also need to run.

## Sequencing

```python
def full_pipeline(requirements: str) -> Result:
    # Initialize
    version = get_next_version()
    create_directory(f"artifacts/v{version}")
    create_targets_yaml(user_preferences)
    
    # Phase 1: Spec
    result = run_agent("lean-os-spec", requirements)
    if not result.gate_passed:
        return Failure("G1", result.errors)
    
    # Phase 2: Build
    result = run_agent("lean-os-build")
    if not result.gate_passed:
        return Failure("G2-G4", result.errors)
    
    # Phase 3: Verify
    result = run_agent("lean-os-verify")
    if not result.gate_passed:
        return Failure("G5-G6", result.errors)
    
    # Phase 4: Gen
    result = run_agent("lean-os-gen")
    if not result.gate_passed:
        return Failure("G7", result.errors)
    
    return Success(f"artifacts/v{version}/gen")
```

## Resume Logic (CRITICAL)

The system MUST support resuming from any phase. **DO NOT delete and rebuild** unless explicitly requested.

### Check Phase Completion

```python
def get_phase_status(artifact_dir: str) -> dict:
    """
    Determine which phases are complete by checking outputs.
    """
    status = {}
    
    # SPEC: Complete if all 4 files exist
    spec_files = ["objects.yaml", "morphisms.yaml", "effects.yaml", "constraints.yaml"]
    status["spec"] = all(
        file_exists(f"{artifact_dir}/spec/{f}") for f in spec_files
    )
    
    # BUILD: Complete if all 4 files exist
    build_files = ["category.yaml", "effects.yaml", "functors.yaml", "transformations.yaml"]
    status["build"] = all(
        file_exists(f"{artifact_dir}/build/{f}") for f in build_files
    )
    
    # VERIFY: Complete if laws-report shows PASS
    if file_exists(f"{artifact_dir}/verify/laws-report.yaml"):
        report = load_yaml(f"{artifact_dir}/verify/laws-report.yaml")
        status["verify"] = report.get("summary", {}).get("status") == "PASS"
    else:
        status["verify"] = False
    
    # GEN: Complete if maps verified AND code exists
    if file_exists(f"{artifact_dir}/gen/maps-verification.yaml"):
        verification = load_yaml(f"{artifact_dir}/gen/maps-verification.yaml")
        maps_ok = verification.get("status") == "PASS"
        code_exists = file_exists(f"{artifact_dir}/gen/python/src/main.py")
        status["gen"] = maps_ok and code_exists
    else:
        status["gen"] = False
    
    return status


def determine_start_phase(artifact_dir: str) -> str:
    """
    Determine which phase to start/resume from.
    
    Returns: "spec" | "build" | "verify" | "gen" | "complete"
    """
    status = get_phase_status(artifact_dir)
    
    if not status["spec"]:
        return "spec"
    if not status["build"]:
        return "build"
    if not status["verify"]:
        return "verify"
    if not status["gen"]:
        return "gen"
    return "complete"
```

### Resume Pipeline

```python
def resume_pipeline(artifact_dir: str, force_from: str = None) -> Result:
    """
    Resume pipeline from where it left off.
    
    Args:
        artifact_dir: Path to artifacts/v{N}/
        force_from: Optional phase to force restart from
    
    Usage:
        resume_pipeline("artifacts/v1/")           # Auto-detect
        resume_pipeline("artifacts/v1/", "verify") # Force from verify
    """
    start_phase = force_from or determine_start_phase(artifact_dir)
    
    if start_phase == "complete":
        return Success("Pipeline already complete")
    
    print(f"Resuming from: {start_phase}")
    
    phases = ["spec", "build", "verify", "gen"]
    start_idx = phases.index(start_phase)
    
    for phase in phases[start_idx:]:
        print(f"Running: {phase}")
        result = run_agent(f"lean-os-{phase}", artifact_dir)
        
        if not result.gate_passed:
            return Failure(phase, result.errors)
    
    return Success(f"{artifact_dir}/gen")
```

### Skip Already-Complete Phases

Each phase agent should check if work is already done:

```python
# In each phase agent
def run_spec_phase(artifact_dir: str) -> Result:
    # Check if already complete
    if phase_already_complete(artifact_dir, "spec"):
        print("SPEC phase already complete, skipping")
        return Success("skipped")
    
    # Do actual work...
```

### When to Force Rebuild

Force rebuild (`--force` or `force_from`) when:
- Spec changes (requirements changed)
- Bug found in previous phase outputs
- Upgrading skill versions
- User explicitly requests clean build

```python
# Force full rebuild
full_pipeline(requirements, force=True)

# Force rebuild from specific phase
resume_pipeline("artifacts/v1/", force_from="build")
```

### Incremental Changes

For small changes (add one morphism, fix one type):

```python
def incremental_update(artifact_dir: str, changes: dict) -> Result:
    """
    Apply incremental changes without full rebuild.
    
    Example:
        incremental_update("artifacts/v1/", {
            "add_morphism": {"name": "delete_user", "domain": "UserId", "codomain": "Unit"}
        })
    """
    # 1. Update spec
    update_spec_file(artifact_dir, changes)
    
    # 2. Re-run from build (spec changed)
    return resume_pipeline(artifact_dir, force_from="build")
```

## Artifact Structure

```
artifacts/v{N}/
├── targets.yaml          # Created by orchestrator
├── spec/                  # Created by lean-os-spec
│   ├── objects.yaml
│   ├── morphisms.yaml
│   ├── effects.yaml
│   └── constraints.yaml
├── build/                 # Created by lean-os-build
│   ├── category.yaml
│   ├── effects.yaml
│   ├── functors.yaml
│   └── transformations.yaml
├── verify/                # Created by lean-os-verify
│   ├── proofs/*.lean
│   ├── laws-report.yaml
│   ├── constraints-report.yaml
│   └── coverage-report.yaml
└── gen/                   # Created by lean-os-gen
    └── {language}/
        ├── src/**/*.py
        ├── Dockerfile
        └── docker-compose.yaml
```

## Status Reporting

The orchestrator maintains a `status.yaml` file in each artifact version:

```yaml
# artifacts/v1/status.yaml
version: 1
created_at: "2024-12-13T10:30:00Z"
updated_at: "2024-12-13T10:45:00Z"

phases:
  spec:
    status: complete        # complete | failed | in_progress | not_started
    completed_at: "2024-12-13T10:32:00Z"
    gate: G1
    gate_passed: true
    
  build:
    status: complete
    completed_at: "2024-12-13T10:38:00Z"
    gate: G2-G4
    gate_passed: true
    
  verify:
    status: failed
    failed_at: "2024-12-13T10:42:00Z"
    gate: G5
    gate_passed: false
    errors:
      - "Lean proof failed: monad_assoc"
      - "lake build exit code 1"
    
  gen:
    status: not_started

overall: blocked_at_verify
last_successful_phase: build
resume_from: verify
```

### Status Update Functions

```python
def update_status(artifact_dir: str, phase: str, result: Result) -> None:
    """Update status.yaml after phase completion."""
    status_file = f"{artifact_dir}/status.yaml"
    
    if file_exists(status_file):
        status = load_yaml(status_file)
    else:
        status = {
            "version": get_version(artifact_dir),
            "created_at": now_iso(),
            "phases": {p: {"status": "not_started"} for p in PHASES}
        }
    
    status["updated_at"] = now_iso()
    
    if result.success:
        status["phases"][phase] = {
            "status": "complete",
            "completed_at": now_iso(),
            "gate": result.gate,
            "gate_passed": True,
        }
        status["last_successful_phase"] = phase
    else:
        status["phases"][phase] = {
            "status": "failed",
            "failed_at": now_iso(),
            "gate": result.gate,
            "gate_passed": False,
            "errors": result.errors,
        }
        status["overall"] = f"blocked_at_{phase}"
        status["resume_from"] = phase
    
    # Update overall status
    if all(status["phases"][p]["status"] == "complete" for p in PHASES):
        status["overall"] = "complete"
        status["resume_from"] = None
    
    write_yaml(status_file, status)


def get_resume_point(artifact_dir: str) -> str:
    """Get phase to resume from based on status.yaml."""
    status_file = f"{artifact_dir}/status.yaml"
    
    if not file_exists(status_file):
        return "spec"  # Fresh start
    
    status = load_yaml(status_file)
    
    # Explicit resume point from failure
    if status.get("resume_from"):
        return status["resume_from"]
    
    # Find first incomplete phase
    for phase in PHASES:
        if status["phases"][phase]["status"] != "complete":
            return phase
    
    return "complete"
```

### User Commands

```
# Check status
"What's the status of my build?"
→ Read status.yaml, report phases

# Resume
"Continue from where we left off"
→ get_resume_point() → resume_pipeline()

# Force rebuild
"Rebuild from spec"
→ resume_pipeline(force_from="spec")

# Rebuild everything
"Clean rebuild"
→ Delete artifacts/v{N}/, start fresh
```

## On Failure

When a phase agent fails:

1. **Report clearly**: Which gate, what failed, why
2. **Suggest fix**: Based on failure type
3. **Allow retry**: User can fix and re-run phase
4. **Don't proceed**: Never skip failed gates

## Responsibilities

- Initialize artifacts directory with version
- Create/update targets.yaml from user preferences
- Sequence phase agents in correct order
- Handle gate failures with clear reporting
- Track completion status per phase
- Support incremental updates

## Multi-Application Systems

Some systems consist of multiple applications that require **separate pipeline runs**.

### Example: Main App + Scraper

```yaml
# System has two applications:
# 1. Main API service (microservices)
# 2. Data scraper (standalone)

# These are SEPARATE pipelines, not one pipeline with two outputs.
```

### When to Use Separate Pipelines

| Scenario | Separate Pipelines? | Why |
|----------|---------------------|-----|
| API + Worker | Maybe | If worker has different types/operations |
| API + Scraper | Yes | Scraper is standalone, different lifecycle |
| Multiple microservices | No | One pipeline generates all services |
| Monolith + CLI | No | CLI uses same domain, just different entry point |
| Main + Admin panel | No | Same domain, different handlers |

### Running Multiple Pipelines

```bash
# Pipeline 1: Main API
artifacts/
  v1/
    targets.yaml       # topology: microservices, api: true
    spec/
    build/
    verify/
    gen/python/        # Main API code

# Pipeline 2: Scraper (separate)
artifacts/
  scraper-v1/
    targets.yaml       # topology: standalone, api: false, persistence: false
    spec/              # Scraper-specific types and operations
    build/
    verify/
    gen/python/        # Scraper code
```

### User Request Examples

```
User: "Build the Glam system"
→ Main pipeline: API + microservices

User: "Also need the scraper"
→ Separate pipeline: "Let's create a separate pipeline for the scraper.
   It has different lifecycle and types. I'll create artifacts/scraper-v1/."

User: "Can you add scraper to the main system?"
→ Explain: "The scraper is standalone - different deployment, different
   types, different schedule. It should be a separate pipeline."
```

### Key Rule

**One pipeline = one deployment unit.**

If two things deploy independently, they need separate pipelines.
