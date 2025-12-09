---
name: specifications-architect
description: |
  Orchestrator for the specification layer. Takes natural language requirements and produces
  complete, validated specifications ready for the standards layer. Coordinates 10 sub-skills
  in correct dependency order, manages data flow, handles iteration, and enforces validation gate.

  IMPORTANT: All outputs are versioned under artifacts/engineering/v{X}/specifications/
---

# Specifications Architect

Entry point for the LeanOS categorical system builder. Transforms requirements into mathematically structured specifications.

## Purpose

Orchestrate the complete specification pipeline:
1. Parse requirements into domain concepts
2. Synthesize algebraic data types
3. Formalize constraints and morphisms
4. Detect categorical structure
5. Generate proof obligations
6. Validate and gate to standards

## Input

Natural language requirements in any form:
- User stories
- Feature descriptions
- Existing system documentation
- Conversation/chat requirements
- Formal specifications

## Output

Complete specification directory under versioned artifacts:

```
artifacts/engineering/v{X}/specifications/
├── domain-concepts.yaml      # Domain model
├── requirements.adt          # Algebraic types
├── constraints.yaml          # Formal propositions
├── services.spec.yaml        # Morphisms with effects + resilience
├── state-machines.yaml       # Lifecycle categories
├── architecture.categorical  # Categorical structure
├── types.curry-howard        # Proof obligations
├── versions.yaml             # Version tracking
└── validation-report.yaml    # Validation results
```

**Version Determination:**
- New system: Start at v1 → `artifacts/engineering/v1/specifications/`
- Breaking changes: Increment version → `artifacts/engineering/v2/specifications/`
- Minor updates: Same version, update in place

## Pipeline

```
                              SPECIFICATIONS ARCHITECT
┌─────────────────────────────────────────────────────────────────────────────┐
│                                                                             │
│  ┌─────────────────┐                                                        │
│  │  Requirements   │                                                        │
│  │  (Natural Lang) │                                                        │
│  └────────┬────────┘                                                        │
│           │                                                                 │
│           ▼                                                                 │
│  ┌─────────────────┐                                                        │
│  │ domain-extractor│ ─────────────────────────────────────┐                 │
│  └────────┬────────┘                                      │                 │
│           │ domain-concepts.yaml                          │                 │
│           │                                               │                 │
│     ┌─────┴─────┬─────────────────────────┐              │                 │
│     │           │                         │              │                 │
│     ▼           ▼                         ▼              ▼                 │
│  ┌──────────┐ ┌──────────────┐ ┌───────────────┐ ┌────────────────┐        │
│  │  type-   │ │  morphism-   │ │  constraint-  │ │ state-machine- │        │
│  │synthesizer│ │  specifier   │ │  specifier    │ │   extractor    │        │
│  └────┬─────┘ └──────┬───────┘ └───────┬───────┘ └───────┬────────┘        │
│       │              │                 │                 │                 │
│       │              ▼                 │                 │                 │
│       │       ┌──────────────┐         │                 │                 │
│       │       │effect-analyzer│         │                 │                 │
│       │       └──────┬───────┘         │                 │                 │
│       │              │                 │                 │                 │
│       │              ▼                 │                 │                 │
│       │       ┌────────────────┐       │                 │                 │
│       │       │ resilience-    │       │                 │                 │
│       │       │ specifier      │       │                 │                 │
│       │       └──────┬─────────┘       │                 │                 │
│       │              │                 │                 │                 │
│       └──────────────┴─────────────────┴─────────────────┘                 │
│                      │                                                      │
│                      ▼                                                      │
│           ┌─────────────────────────┐                                       │
│           │ categorical-structure-  │                                       │
│           │      detector           │                                       │
│           └───────────┬─────────────┘                                       │
│                       │                                                     │
│                       ▼                                                     │
│           ┌─────────────────────────┐                                       │
│           │ proof-obligation-       │                                       │
│           │      generator          │                                       │
│           └───────────┬─────────────┘                                       │
│                       │                                                     │
│                       ▼                                                     │
│           ┌─────────────────────────┐                                       │
│           │ specification-validator │                                       │
│           └───────────┬─────────────┘                                       │
│                       │                                                     │
│              ┌────────┴────────┐                                            │
│              │                 │                                            │
│              ▼                 ▼                                            │
│           [PASS]            [FAIL]                                          │
│              │                 │                                            │
│              ▼                 ▼                                            │
│      Standards Layer     Fix & Retry                                        │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Sub-Skills

| Order | Skill | Purpose | Dependencies |
|-------|-------|---------|--------------|
| 1 | domain-extractor | Extract domain concepts | Requirements |
| 2a | type-synthesizer | Create ADTs | domain-concepts |
| 2b | morphism-specifier | Define operations | domain-concepts, requirements.adt |
| 2c | constraint-specifier | Formalize rules | domain-concepts, requirements.adt |
| 2d | state-machine-extractor | Extract lifecycles | domain-concepts, requirements.adt |
| 3 | effect-analyzer | Tag with effects | services.spec |
| 4 | resilience-specifier | Add fault tolerance | services.spec |
| 5 | categorical-structure-detector | Identify structure | All specs |
| 6 | proof-obligation-generator | Create proof obligations | architecture.categorical, constraints |
| 7 | specification-validator | Validate & gate | All specs |

**Parallel execution:** Steps 2a-2d can run in parallel after step 1.

## Execution Modes

### Mode 1: Full Generation

Start from scratch with requirements:

```yaml
mode: full
input: |
  Build a Shopify app that analyzes customer photos to determine 
  face shape and skin tone, then recommends products from the 
  merchant's catalog that would suit them.
  
  - Merchants install via Shopify OAuth
  - Customers upload selfies
  - AI analyzes photos
  - System matches to products
  - Results shown in widget
  
output_version: 1
```

**Process:**
1. Run all skills in order
2. Generate complete specification
3. Validate
4. Output version 1

### Mode 2: Incremental Update

Add requirements to existing specification:

```yaml
mode: incremental
base_version: 1
additions: |
  - Add subscription tiers (Free, Pro, Enterprise)
  - Pro tier gets priority analysis
  - Enterprise gets custom branding
  
output_version: 2
```

**Process:**
1. Load existing specs (v1)
2. Run domain-extractor with additions
3. Merge with existing domain-concepts
4. Re-run affected downstream skills
5. Detect breaking changes
6. Output version 2

### Mode 3: Analysis Only

Analyze existing system without generating:

```yaml
mode: analyze
input: |
  [Existing codebase description or architecture]
  
output: analysis-report.yaml
```

**Process:**
1. Run domain-extractor
2. Run categorical-structure-detector
3. Output analysis without full generation

### Mode 4: Validation Only

Re-validate existing specifications:

```yaml
mode: validate
specification_version: 2
```

**Process:**
1. Load existing specs
2. Run specification-validator
3. Report issues

## Orchestration Logic

### Dependency Resolution

```yaml
dependencies:
  domain-extractor: []
  type-synthesizer: [domain-extractor]
  morphism-specifier: [domain-extractor, type-synthesizer]
  constraint-specifier: [domain-extractor, type-synthesizer]
  state-machine-extractor: [domain-extractor, type-synthesizer]
  effect-analyzer: [morphism-specifier]
  resilience-specifier: [effect-analyzer]
  categorical-structure-detector: 
    - type-synthesizer
    - morphism-specifier
    - constraint-specifier
    - state-machine-extractor
    - resilience-specifier
  proof-obligation-generator:
    - categorical-structure-detector
    - constraint-specifier
  specification-validator:
    - proof-obligation-generator
    - ALL  # Needs all files
```

### Change Propagation

When a skill output changes, re-run dependents:

```yaml
change_propagation:
  domain-concepts.yaml:
    invalidates:
      - requirements.adt
      - constraints.yaml
      - services.spec.yaml
      - state-machines.yaml
      - architecture.categorical
      - types.curry-howard
    action: re-run from type-synthesizer
    
  requirements.adt:
    invalidates:
      - constraints.yaml
      - services.spec.yaml
      - architecture.categorical
      - types.curry-howard
    action: re-run affected skills
    
  services.spec.yaml:
    invalidates:
      - architecture.categorical
      - types.curry-howard
    action: re-run from categorical-structure-detector
```

### Error Handling

```yaml
error_handling:
  skill_failure:
    action: stop pipeline
    report: which skill failed and why
    suggestion: how to fix
    
  validation_failure:
    action: report issues
    categorize: blocking vs warning
    suggestion: which skills to re-run
    
  circular_dependency:
    action: detect during planning
    report: dependency cycle
    never: should not happen with correct ordering
```

## Inter-Skill Validation

Validate outputs before passing to next skill:

```yaml
inter_skill_validation:
  strategy: halt_on_error
  
  after_each_skill:
    - name: schema_valid
      check: "Output matches expected schema"
      on_failure: halt
      
    - name: references_resolve
      check: "All type/morphism references exist"
      on_failure: halt
      
    - name: no_contradictions
      check: "New output doesn't contradict existing"
      on_failure: halt
      
  on_halt:
    present_to_human:
      context: "Previous skill outputs"
      error: "What validation failed"
      suggestions: 
        - "Modify input and retry"
        - "Fix upstream skill output"
        - "Override with warning"
    await_decision:
      options:
        - retry: "Re-run skill with modifications"
        - fix_upstream: "Go back to earlier skill"
        - override: "Continue anyway (warning logged)"
        - abort: "Stop pipeline"
```

## Feedback Loops

When downstream skill detects issues with upstream output:

```yaml
feedback_loops:
  enabled: true
  
  patterns:
    # Type issues bubble up to type-synthesizer
    - from: categorical-structure-detector
      to: type-synthesizer
      triggers:
        - "Non-composable type pair detected"
        - "Missing product/coproduct structure"
      action:
        notify: true
        suggest_fix: true
        auto_fix: false  # Human decides
        
    # Constraint issues bubble up
    - from: proof-obligation-generator
      to: constraint-specifier
      triggers:
        - "Unprovable constraint"
        - "Contradictory constraints"
      action:
        notify: true
        suggest_fix: true
        
    # Missing domain concepts
    - from: specification-validator
      to: domain-extractor
      triggers:
        - "Orphan type reference"
        - "Missing entity relationship"
      action:
        notify: true
        suggest_fix: true
        
    # Effect misclassification
    - from: resilience-specifier
      to: effect-analyzer
      triggers:
        - "IO morphism without effect tag"
        - "External call missing resilience"
      action:
        notify: true
        suggest_fix: true
        
  human_escalation:
    trigger: "Cannot auto-resolve after 2 iterations"
    present:
      - error_context
      - affected_files
      - attempted_fixes
      - suggested_manual_fixes
    await: human_decision
```

## Validation Gates

```yaml
validation_gates:
  # Gate 1: After domain extraction
  post_domain:
    skill: domain-extractor
    checks:
      - entities_have_identity
      - relationships_bidirectional
      - operations_have_actors
    blocking: true
    
  # Gate 2: After type synthesis
  post_types:
    skill: type-synthesizer
    checks:
      - no_undefined_refs
      - products_have_factors
      - coproducts_have_variants
    blocking: true
    
  # Gate 3: After morphisms defined
  post_morphisms:
    skill: effect-analyzer
    checks:
      - all_morphisms_typed
      - effects_classified
      - compositions_type_check
    blocking: true
    
  # Gate 4: After categorical detection
  post_categorical:
    skill: categorical-structure-detector
    checks:
      - categories_have_identity
      - functors_preserve_composition
      - adjunctions_have_unit_counit
    blocking: true
    
  # Gate 5: Final validation
  final:
    skill: specification-validator
    checks:
      - all_references_resolve
      - no_circular_deps
      - proof_obligations_complete
      - version_incremented
    blocking: true
    gate_to: standards_layer
```

## Interactive Workflow

### Step 1: Requirements Gathering

```
User: Build a photo analysis system for Shopify merchants

Specifications Architect: I'll extract domain concepts. Let me clarify:
- What triggers photo analysis? (customer upload, merchant request)
- What analysis types? (face shape, skin tone, style)
- How are results used? (product recommendations, reports)

User: Customers upload selfies, AI analyzes face shape and skin tone,
      system recommends products from merchant's Shopify catalog.

Specifications Architect: Running domain-extractor...
```

### Step 2: Review Domain Model

```
Specifications Architect: Extracted domain concepts:

Entities:
- Merchant (identity: merchant_id, lifecycle: false)
- Profile (identity: profile_id, lifecycle: false)  
- Analysis (identity: analysis_id, lifecycle: true)
- Recommendation (identity: recommendation_id)

Relationships:
- Merchant has many Profiles
- Profile has many Analyses
- Analysis has one RecommendationSet

External Dependencies:
- Shopify Admin API
- Groq AI API

Does this capture your domain correctly?

User: Yes, but add subscription management for merchants

Specifications Architect: Adding Subscription entity, re-running pipeline...
```

### Step 3: Review Types

```
Specifications Architect: Synthesized types:

Products (×):
- Merchant = MerchantId × ShopDomain × Subscription × Settings
- Profile = ProfileId × MerchantId × Demographics × Preferences
- Analysis = AnalysisId × ProfileId × Photo × Status × Result?

Coproducts (+):
- AnalysisStatus = Pending | Processing | Completed | Failed
- SubscriptionTier = Free | Pro | Enterprise

Confirm or modify?
```

### Step 4: Review Morphisms

```
Specifications Architect: Defined morphisms:

Merchant Module:
- create_merchant: CreateMerchantInput → IO[Either[E, Merchant]]
- get_merchant: MerchantId → IO[Either[E, Merchant]]
- update_subscription: (MerchantId × SubscriptionTier) → IO[Either[E, Merchant]]

Analysis Module:
- request_analysis: (ProfileId × Photo) → IO[Either[E, Analysis]]
- process_analysis: Analysis → IO[Either[E, AnalysisResult]]

Effects tagged, resilience added for external calls.
```

### Step 5: Validation Gate

```
Specifications Architect: Running specification-validator...

Validation Report:
✓ 48/50 checks passed
⚠ 2 warnings:
  - Unused type: MatchReasoning (consider removing or using)
  - Missing circuit breaker for custom_api_call

Gate Decision: PASS (warnings only)

Ready to proceed to Standards Layer?

User: Yes, proceed

Specifications Architect: Specifications complete. Output: artifacts/engineering/v1/specifications/
Next phase: standardization-definer
```

## Iteration Patterns

### Pattern 1: Add Feature

```yaml
trigger: "Add subscription billing"
process:
  1. Re-run domain-extractor with new requirements
  2. Merge entities (add BillingEvent, Invoice)
  3. Re-run type-synthesizer (new ADTs)
  4. Re-run morphism-specifier (new operations)
  5. Re-run downstream skills
  6. Validate
  7. Output new version
```

### Pattern 2: Fix Validation Error

```yaml
trigger: "Circular ownership detected"
process:
  1. Identify problematic relationships
  2. Present options to user
  3. User chooses fix
  4. Re-run from domain-extractor
  5. Re-validate
```

### Pattern 3: Refine Types

```yaml
trigger: "Split Profile into CustomerProfile and AnonymousProfile"
process:
  1. Update requirements.adt (new coproduct)
  2. Re-run constraint-specifier
  3. Re-run morphism-specifier
  4. Re-run downstream
  5. Validate
```

## Configuration

```yaml
specifications_architect:
  # Execution settings
  parallel_execution: true  # Run independent skills in parallel
  max_iterations: 5         # Prevent infinite loops

  # Output settings
  output_dir: "artifacts/engineering/v{X}/specifications"
  version_strategy: semantic  # major.minor.patch
  
  # Validation settings
  strict_mode: false  # true = warnings become errors
  require_proofs: true  # Must have proof obligations
  
  # Interaction settings
  interactive: true   # Prompt for clarification
  auto_fix: false     # Don't auto-fix warnings
  
  # Sub-skill settings
  skills:
    domain-extractor:
      include_external_deps: true
    effect-analyzer:
      default_io_layer: [repository, external]
    resilience-specifier:
      default_timeout_ms: 5000
      default_retry_attempts: 3
```

## Output Artifacts

### Primary Output

```
artifacts/engineering/v{X}/specifications/
├── domain-concepts.yaml      # Domain model
├── requirements.adt          # Algebraic types
├── constraints.yaml          # Formal propositions
├── services.spec.yaml        # Morphisms + effects + resilience
├── state-machines.yaml       # Lifecycle categories
├── architecture.categorical  # Categorical structure
├── types.curry-howard        # Proof obligations
├── versions.yaml             # Version metadata
└── validation-report.yaml    # Validation results
```

### Metadata Output

```yaml
# artifacts/engineering/v{X}/specifications/versions.yaml
version: "1.0.0"
created_at: "2024-01-15T10:30:00Z"
created_by: specifications-architect
  
pipeline_run:
  duration_ms: 5230
  skills_executed:
    - name: domain-extractor
      duration_ms: 1200
      status: success
    - name: type-synthesizer
      duration_ms: 800
      status: success
    # ...
  
validation:
  status: pass
  checks_passed: 48
  checks_failed: 0
  warnings: 2
  
dependencies:
  - from: requirements.adt
    to: domain-concepts.yaml
  # ... dependency graph

gate_decision: proceed_to_standards
```

## Integration Points

### Input From

- User requirements (natural language)
- Existing system documentation
- Previous specification versions
- External schema definitions (OpenAPI, GraphQL)

### Output To

- **standardization-definer** → extracts universal properties
- **primitives-mapper** → maps types to implementations
- **kleisli-mapper** → maps effects to async/await
- **proof-composer** → generates Lean 4 proofs

## Categorical Interpretation

Specifications Architect implements the specification functor:

```
Spec: Requirements → Specifications

Where:
- Requirements = Natural language category (informal)
- Specifications = Categorical specification category (formal)

The functor preserves:
- Domain concepts → Objects
- Operations → Morphisms
- Relationships → Functorial structure
- Constraints → Proof obligations
```

## Checklist

Before marking specification complete:

- [ ] All entities have identity
- [ ] All relationships are bidirectional or explicitly one-way
- [ ] All operations have signatures
- [ ] All effects are classified
- [ ] External dependencies have resilience
- [ ] Lifecycle entities have state machines
- [ ] Categorical structure is detected
- [ ] Proof obligations are generated
- [ ] Validation passes
- [ ] Version is incremented correctly

## Next Phase

On successful validation, hand off to Standards Layer:

```
Specifications Architect (complete)
         │
         ▼
┌─────────────────────────┐
│ standardization-definer │ ← Next skill
└─────────────────────────┘
```