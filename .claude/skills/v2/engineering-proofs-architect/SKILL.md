---
name: proofs-architect
description: |
  Orchestrator for the proofs layer. Takes validated maps and generates Lean 4 proofs
  for all categorical laws. Coordinates 8 sub-skills covering identity, composition,
  functors, adjunctions, monads, natural transformations, and certificate generation.
  Use after maps-architect completes successfully.
---

# Proofs Architect

Entry point for the Proofs Layer. Generates formal verification of categorical properties.

## Purpose

Orchestrate the complete proof pipeline:
1. Prove identity laws for all categories
2. Prove composition/associativity laws
3. Prove functor laws (preserves identity, composition)
4. Prove adjunction laws (unit, counit, triangles)
5. Prove monad laws (left/right identity, associativity)
6. Prove naturality of transformations
7. Generate runtime certificates
8. Validate all proofs compile

## Input

Validated maps and previous artifacts:

```
maps/
├── primitives/*.map.yaml
├── kleisli/*.map.yaml
├── adjunctions/*.map.yaml
├── functors/*.map.yaml
├── transformations/*.map.yaml
├── monads/*.map.yaml
├── modules/*.map.yaml
└── versions.yaml

standards/
├── categories/*.std.yaml
└── ...

specifications/v{X}/
├── architecture.categorical
└── ...
```

## Output

Lean 4 proofs and runtime certificates:

```
proofs/
├── lean/
│   ├── LeanOS.lean              # Main module
│   ├── LeanOS/
│   │   ├── Basic.lean           # Basic definitions
│   │   ├── Category.lean        # Category structure
│   │   ├── Identity.lean        # Identity proofs
│   │   ├── Composition.lean     # Composition proofs
│   │   ├── Functor.lean         # Functor proofs
│   │   ├── Adjunction.lean      # Adjunction proofs
│   │   ├── Monad.lean           # Monad proofs
│   │   ├── NaturalTransformation.lean
│   │   └── Tactics.lean         # Custom tactics
│   ├── lakefile.lean            # Build configuration
│   └── lean-toolchain           # Lean version
├── certificates/
│   ├── identity.cert.yaml       # Identity certificates
│   ├── composition.cert.yaml    # Composition certificates
│   ├── functor.cert.yaml        # Functor certificates
│   ├── adjunction.cert.yaml     # Adjunction certificates
│   ├── monad.cert.yaml          # Monad certificates
│   ├── naturality.cert.yaml     # Naturality certificates
│   └── manifest.yaml            # All certificates
├── versions.yaml                # Version tracking
└── validation-report.yaml       # Proof results
```

## Pipeline

```
                               PROOFS ARCHITECT
┌─────────────────────────────────────────────────────────────────────────────┐
│                                                                             │
│  ┌─────────────────────┐                                                    │
│  │  Maps + Standards   │                                                    │
│  │   (from Phase 2)    │                                                    │
│  └──────────┬──────────┘                                                    │
│             │                                                               │
│             ▼                                                               │
│  ┌─────────────────────┐                                                    │
│  │ identity-law-prover │                                                    │
│  └──────────┬──────────┘                                                    │
│             │                                                               │
│             ▼                                                               │
│  ┌──────────────────────────┐                                               │
│  │ composition-law-prover   │                                               │
│  └──────────┬───────────────┘                                               │
│             │                                                               │
│     ┌───────┴───────┬───────────────┐                                      │
│     │               │               │                                      │
│     ▼               ▼               ▼                                      │
│  ┌────────┐  ┌────────────┐  ┌────────────┐                                │
│  │functor │  │ adjunction │  │   monad    │                                │
│  │-prover │  │  -prover   │  │  -prover   │                                │
│  └───┬────┘  └─────┬──────┘  └─────┬──────┘                                │
│      │             │               │                                       │
│      └─────────────┴───────────────┘                                       │
│                    │                                                        │
│                    ▼                                                        │
│           ┌─────────────────────┐                                           │
│           │  naturality-prover  │                                           │
│           └─────────┬───────────┘                                           │
│                     │                                                       │
│                     ▼                                                       │
│           ┌──────────────────────┐                                          │
│           │ certificate-generator│                                          │
│           └─────────┬────────────┘                                          │
│                     │                                                       │
│                     ▼                                                       │
│           ┌────────────────┐                                                │
│           │ proofs-validator│                                               │
│           └────────┬───────┘                                                │
│                    │                                                        │
│          ┌─────────┴────────┐                                               │
│          │                  │                                               │
│          ▼                  ▼                                               │
│       [PASS]             [FAIL]                                             │
│          │                  │                                               │
│          ▼                  ▼                                               │
│     Code Layer         Fix & Retry                                          │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Sub-Skills

| Order | Skill | Purpose | Dependencies |
|-------|-------|---------|--------------|
| 1 | identity-law-prover | Prove id ∘ f = f = f ∘ id | Maps |
| 2 | composition-law-prover | Prove (h∘g)∘f = h∘(g∘f) | identity |
| 3a | functor-law-prover | Prove F(id) = id, F(g∘f) = F(g)∘F(f) | composition |
| 3b | adjunction-law-prover | Prove η, ε, triangle identities | composition |
| 3c | monad-law-prover | Prove monad laws | composition |
| 4 | naturality-prover | Prove α_B ∘ F(f) = G(f) ∘ α_A | functors |
| 5 | certificate-generator | Generate runtime certificates | All proofs |
| 6 | proofs-validator | Gate to code layer | All |

**Parallel execution:** Steps 3a-3c can run in parallel after step 2.

## Execution Modes

### Mode 1: Full Proof Generation

Generate all proofs from scratch:

```yaml
mode: full
maps_version: 1
output_dir: proofs/
lean_version: "4.3.0"
mathlib_version: "latest"
```

### Mode 2: Incremental Proofs

Update proofs when maps change:

```yaml
mode: incremental
maps_version: 2
base_proofs_version: 1
changes:
  - modified: functors/http.map.yaml
  - added: monads/state.map.yaml
```

### Mode 3: Verification Only

Re-verify existing proofs:

```yaml
mode: verify
proofs_version: 1
check_certificates: true
```

### Mode 4: Certificate Generation Only

Generate certificates from existing proofs:

```yaml
mode: certificates_only
proofs_version: 1
```

## Lean 4 Structure

### Project Layout

```lean
-- lakefile.lean
import Lake
open Lake DSL

package LeanOS where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib LeanOS where
  globs := #[.submodules `LeanOS]
```

### Core Definitions

```lean
-- LeanOS/Category.lean
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

namespace LeanOS

/-- Domain category objects -/
inductive DomainObj where
  | Merchant
  | Profile
  | Analysis
  | Product
  deriving DecidableEq

/-- Domain morphisms -/
structure DomainMor (A B : DomainObj) where
  name : String
  pure : Bool  -- Is this a pure function?

/-- Category instance for Domain -/
instance : Category DomainObj where
  Hom := DomainMor
  id A := ⟨"id", true⟩
  comp f g := ⟨s!"{g.name} ∘ {f.name}", f.pure ∧ g.pure⟩

end LeanOS
```

## Proof Strategies

### Identity Proofs

```lean
-- For each morphism f, prove id ∘ f = f and f ∘ id = f
theorem left_identity (f : A ⟶ B) : 𝟙 A ≫ f = f := by
  simp [Category.id_comp]

theorem right_identity (f : A ⟶ B) : f ≫ 𝟙 B = f := by
  simp [Category.comp_id]
```

### Composition Proofs

```lean
-- Prove associativity: (h ∘ g) ∘ f = h ∘ (g ∘ f)
theorem composition_assoc (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) := by
  simp [Category.assoc]
```

### Functor Proofs

```lean
-- Prove functor laws
theorem functor_id (F : C ⥤ D) (A : C) : F.map (𝟙 A) = 𝟙 (F.obj A) := by
  simp [Functor.map_id]

theorem functor_comp (F : C ⥤ D) (f : A ⟶ B) (g : B ⟶ C) :
    F.map (f ≫ g) = F.map f ≫ F.map g := by
  simp [Functor.map_comp]
```

## Orchestration Logic

### Dependency Resolution

```yaml
dependencies:
  identity-law-prover: [maps, standards]
  composition-law-prover: [identity-law-prover]
  functor-law-prover: [composition-law-prover]
  adjunction-law-prover: [composition-law-prover]
  monad-law-prover: [composition-law-prover]
  naturality-prover:
    - functor-law-prover
  certificate-generator:
    - ALL_PROVERS
  proofs-validator:
    - ALL
```

### Change Propagation

```yaml
change_propagation:
  Identity.lean:
    invalidates: [ALL]
    action: full_reproof
    
  Functor.lean:
    invalidates:
      - Adjunction.lean
      - NaturalTransformation.lean
    action: re-run affected provers
    
  certificates/*.cert.yaml:
    invalidates: []
    action: regenerate_manifest
```

## Inter-Skill Validation

```yaml
inter_skill_validation:
  strategy: halt_on_error
  
  after_each_skill:
    - name: proof_compiles
      check: "Lean 4 typechecks successfully"
      on_failure: halt
      
    - name: proof_complete
      check: "No sorry or admit"
      on_failure: halt
      
    - name: proof_matches_spec
      check: "Proves correct property"
      on_failure: halt
      
  on_halt:
    present_to_human:
      context: "Proof attempt + error"
      error: "What failed"
      suggestions:
        - "Adjust theorem statement"
        - "Add lemma"
        - "Change proof strategy"
    await_decision:
      options:
        - retry_with_hint
        - add_axiom
        - skip_with_warning
        - abort
```

## Feedback Loops

```yaml
feedback_loops:
  enabled: true
  
  patterns:
    - from: functor-law-prover
      to: functor-mapper
      triggers:
        - "Functor laws don't hold"
        - "Missing map implementation"
      action:
        notify: true
        suggest_fix: true
        
    - from: monad-law-prover
      to: monad-mapper
      triggers:
        - "Monad laws violated"
        - "Bind not associative"
      action:
        notify: true
        suggest_fix: true
        
    - from: adjunction-law-prover
      to: adjunction-mapper
      triggers:
        - "Triangle identity fails"
        - "Unit/counit mismatch"
      action:
        notify: true
        suggest_fix: true
        
  human_escalation:
    trigger: "Cannot prove after 3 attempts"
    present:
      - theorem_statement
      - proof_attempts
      - error_messages
    options:
      - provide_hint
      - add_axiom
      - mark_unproven
```

## Validation Gates

```yaml
validation_gates:
  # Gate 1: After identity proofs
  post_identity:
    skill: identity-law-prover
    checks:
      - all_identity_proofs_compile
      - no_sorry_in_identity
    blocking: true
    
  # Gate 2: After composition proofs
  post_composition:
    skill: composition-law-prover
    checks:
      - associativity_proven
      - composition_closed
    blocking: true
    
  # Gate 3: After categorical structure proofs
  post_categorical:
    skills:
      - functor-law-prover
      - adjunction-law-prover
      - monad-law-prover
    checks:
      - all_functor_laws_proven
      - all_adjunction_laws_proven
      - all_monad_laws_proven
    blocking: true
    
  # Gate 4: After naturality proofs
  post_naturality:
    skill: naturality-prover
    checks:
      - all_squares_commute
    blocking: true
    
  # Gate 5: Final validation
  final:
    skill: proofs-validator
    checks:
      - all_proofs_compile
      - no_sorry_anywhere
      - certificates_generated
      - manifest_complete
    blocking: true
    gate_to: code_layer
```

## Configuration

```yaml
proofs_architect:
  # Execution settings
  parallel_execution: true
  max_proof_attempts: 3
  timeout_per_proof: 300  # seconds
  
  # Lean settings
  lean:
    version: "4.3.0"
    mathlib: true
    threads: 4
    
  # Output settings
  output_dir: "proofs"
  generate_certificates: true
  
  # Proof settings
  allow_axioms: false
  allow_sorry: false  # Strict mode
  
  # Certificate settings
  certificates:
    format: yaml
    include_proof_hash: true
    include_timestamp: true
```

## Proof Coverage Matrix

```yaml
coverage:
  # What we prove
  categorical_laws:
    identity:
      - "∀ f: A → B, id_A ∘ f = f"
      - "∀ f: A → B, f ∘ id_B = f"
    composition:
      - "∀ f g h, (h ∘ g) ∘ f = h ∘ (g ∘ f)"
      
  functor_laws:
    - "F(id_A) = id_{F(A)}"
    - "F(g ∘ f) = F(g) ∘ F(f)"
    
  adjunction_laws:
    - "η: Id → R∘L exists"
    - "ε: L∘R → Id exists"
    - "(ε∘L) ∘ (L∘η) = id_L"
    - "(R∘ε) ∘ (η∘R) = id_R"
    
  monad_laws:
    - "pure(a) >>= f = f(a)"
    - "m >>= pure = m"
    - "(m >>= f) >>= g = m >>= (x → f(x) >>= g)"
    
  naturality:
    - "α_B ∘ F(f) = G(f) ∘ α_A"
```

## Checklist

Before marking proofs complete:

- [ ] All identity laws proven
- [ ] Composition associativity proven
- [ ] All functor laws proven
- [ ] All adjunction laws proven
- [ ] All monad laws proven
- [ ] All naturality squares commute
- [ ] No `sorry` or `admit` in proofs
- [ ] All proofs compile with Lean 4
- [ ] Certificates generated for runtime
- [ ] Validation passes

## Next Phase

On successful validation, hand off to Code Layer:

```
Proofs Architect (complete)
         │
         ▼
┌─────────────────────┐
│   code-architect    │ ← Next orchestrator
└─────────────────────┘
```
