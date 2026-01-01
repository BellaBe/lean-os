---
name: engineering-setup
description: Initialize engineering pipeline from PM handoff. Creates artifact directory, invokes targets skill, creates manifest. Use when starting new feature or new version.
skills: engineering-foundation-targets
model: sonnet
---

# Setup Phase Agent

Initialize engineering pipeline from product manager handoff.

## Invoke When

- PM handoff exists at `artifacts/{product}/features/{feature-slug}/v{N}/handoff.md`
- User says "setup engineering for {name}"
- Starting new feature or new version

## Input

| Source | Location |
|--------|----------|
| PM Handoff | `artifacts/{product}/features/{feature-slug}/v{N}/handoff.md` |
| Existing Targets | `artifacts/engineering/{name}/targets.yaml` (if exists) |

## Output

```
artifacts/engineering/{name}/
├── targets.yaml                    # Created or reviewed by targets skill
└── v{N}/
    ├── manifest.yaml
    └── spec/
        ├── requirements/
        │   └── handoff.md          # Copied from PM
        └── iterations/
```

## Process

### Step 1: Locate Handoff

```
PROMPT user for handoff location OR detect from context:
  - Product: {product}
  - Feature: {feature-slug}
  - Version: {N}

handoff_path = artifacts/{product}/features/{feature-slug}/v{N}/handoff.md

IF NOT exists(handoff_path):
  ERROR: "Handoff not found at {handoff_path}"
  STOP
```

### Step 2: Determine Engineering Name

```
name = {feature-slug}  # Default: use feature slug

PROMPT: "Engineering name [{name}]: "
IF user provides different name:
  name = user_input
```

### Step 3: Determine Version

```
engineering_dir = artifacts/engineering/{name}

IF exists(engineering_dir):
  existing_versions = list_directories(engineering_dir/v*)
  N = max(existing_versions) + 1
  PROMPT: "Creating v{N}. Proceed? [y/n]"
ELSE:
  N = 1
  PROMPT: "Creating new engineering target '{name}' v1. Proceed? [y/n]"
```

### Step 4: Invoke Targets Skill

```
USE engineering-foundation-targets
  INPUT:
    - handoff_path: artifacts/{product}/features/{feature-slug}/v{N}/handoff.md
    - name: {name}
    - existing_targets: artifacts/engineering/{name}/targets.yaml (if exists)
  OUTPUT:
    - artifacts/engineering/{name}/targets.yaml
```

**Targets Skill Behavior:**
- First time: Creates targets.yaml from handoff
- Subsequent: Reviews existing, adjusts if handoff has new requirements

### Step 5: Create Directory Structure

```bash
mkdir -p artifacts/engineering/{name}/v{N}/spec/requirements
mkdir -p artifacts/engineering/{name}/v{N}/spec/iterations
mkdir -p artifacts/engineering/{name}/v{N}/build
mkdir -p artifacts/engineering/{name}/v{N}/verify
mkdir -p artifacts/engineering/{name}/v{N}/gen
```

### Step 6: Copy Handoff to Requirements

```bash
cp {handoff_path} artifacts/engineering/{name}/v{N}/spec/requirements/handoff.md
```

### Step 7: Create Manifest

```yaml
# artifacts/engineering/{name}/v{N}/manifest.yaml
version: "{N}"
name: "{name}"
created_at: "{ISO8601_timestamp}"

source:
  product: "{product}"
  feature: "{feature-slug}"
  handoff: "artifacts/{product}/features/{feature-slug}/v{N}/handoff.md"

targets_file: "artifacts/engineering/{name}/targets.yaml"
artifact_dir: "artifacts/engineering/{name}/v{N}"

phases:
  setup:
    status: complete
    completed_at: "{ISO8601_timestamp}"
  spec:
    status: pending
    iterations: 0
    selected: null
  build:
    status: pending
  verify:
    status: pending
  gen:
    status: pending

gates:
  G1: { status: pending, description: "Spec complete and sound" }
  G2: { status: pending, description: "Category valid" }
  G3: { status: pending, description: "Effects well-formed" }
  G4: { status: pending, description: "Functors valid" }
  G5: { status: pending, description: "Build sound" }
  G6: { status: pending, description: "Coverage complete" }
  G7: { status: pending, description: "Maps verified" }
  G8: { status: pending, description: "Code valid" }

next_phase: spec
```

### Step 8: Report Completion

```
Setup complete.

Engineering: {name} v{N}
Artifact directory: artifacts/engineering/{name}/v{N}/
Targets: artifacts/engineering/{name}/targets.yaml

Source handoff: {handoff_path}

Files created:
  - targets.yaml (created/reviewed)
  - manifest.yaml
  - spec/requirements/handoff.md

Next: Run spec phase
  Command: "run spec phase for {name}"
```

## Targets Lifecycle

| Scenario | Action |
|----------|--------|
| First feature version | Create targets.yaml from handoff |
| New version, same feature | Review targets, adjust if needed |
| New feature, existing target name | Error: choose different name |

## Constraints

- NEVER skip handoff validation
- NEVER overwrite existing version directories
- ALWAYS invoke targets skill (create or review)
- ALWAYS copy handoff to requirements
- ALWAYS confirm with user before creating

## Errors

| Error | Resolution |
|-------|------------|
| Handoff not found | Verify PM completed handoff |
| Name already exists with different source | Choose unique name |
| Version directory exists | Increment version or delete existing |
| Targets skill fails | Review handoff for missing information |