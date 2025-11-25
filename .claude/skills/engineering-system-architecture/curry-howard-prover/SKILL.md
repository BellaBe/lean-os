---
name: curry-howard-prover
description: Generate type proofs using Curry-Howard correspondence. Proves all functions are total (no partial functions), validates type signatures are implementable, and ensures no impossible states exist. Outputs constructive proofs.
allowed-tools: Read, Write, Bash
version: 1.0.0
---

# Curry-Howard Prover

## Purpose

Apply Curry-Howard correspondence to prove type signatures are implementable and functions are total. Every type is a proposition, every function is a proof.

## Curry-Howard Correspondence

```
Types         ↔   Logic
A → B         ↔   A implies B
A × B         ↔   A and B
A + B         ↔   A or B
Never         ↔   False (⊥)
Unit          ↔   True (⊤)
```

## Input

```
artifacts/engineering/specifications/v{X}/requirements.adt
artifacts/engineering/specifications/v{VERSION}/architecture.categorical
```

## Output

```
artifacts/engineering/specifications/v{VERSION}/types.curry-howard
artifacts/engineering/proofs/architecture/type-proofs/
```

## Proof Generation

### Proof 1: Function Totality

**Theorem:** `sync_{domain}: Credentials → Entities` is total

**Proof by construction:**
```
Given: credentials: Credentials
Show: ∃ entities: Entities

Case analysis on Platform:
  Case {Platform}:
    {platform}_sync(credentials) : Entities ✓

  Case {AltPlatform}:
    {altplatform}_sync(credentials) : Entities ✓

All cases covered → Function is total. QED
```

**Type signature:**
```python
def sync_{domain}(credentials: Credentials, platform: Platform) -> Entities:
    """
    Proof of totality:
    - Platform is finite coproduct ({Platform} + {AltPlatform})
    - Each variant has implementation
    - Pattern match exhaustive
    - ∴ Function always returns Entities
    """
    match platform:
        case {Platform}(config):
            return {platform}_sync(credentials, config)
        case {AltPlatform}(config):
            return {altplatform}_sync(credentials, config)
```

### Proof 2: No Impossible States

**Theorem:** No path contains `Never` type

**Proof:**
```
For all paths p in ADT:
  If Never ∈ components(p):
    Then p × Never = Never (annihilation)
    → Path is impossible (uninhabited type)

Check: ∄ path p where Never ∈ components(p)

∴ All paths are implementable. QED
```

### Proof 3: Recursive Type Termination

**Theorem:** Recursive type `Tree` has base case

**Definition:**
```
Tree = Leaf + (Node × Tree × Tree)
```

**Proof:**
```
Base case: Leaf : Tree (no recursion)
Inductive case: Node(value, left: Tree, right: Tree) : Tree

Termination:
  1. Leaf case terminates immediately
  2. Recursive calls on smaller trees
  3. Structural recursion guarantees termination

∴ Tree is well-founded. QED
```

## Execution Steps

### Step 1: Extract Type Signatures

```bash
python {baseDir}/scripts/extract_signatures.py \
  --adt artifacts/engineering/specifications/v{VERSION}/requirements.adt \
  --functors artifacts/engineering/specifications/v{VERSION}/architecture.categorical \
  --output /tmp/type-signatures.json
```

### Step 2: Generate Proofs

```bash
python {baseDir}/scripts/prove_totality.py \
  --signatures /tmp/type-signatures.json \
  --output artifacts/engineering/specifications/v{VERSION}/types.curry-howard
```

### Step 3: Verify Proofs

```bash
python {baseDir}/scripts/verify_proofs.py \
  --proofs artifacts/engineering/specifications/v{VERSION}/types.curry-howard \
  --output artifacts/engineering/proofs/architecture/type-proofs/verification.json
```

## Output Format

```yaml
# artifacts/engineering/specifications/v{VERSION}/types.curry-howard

version: v{VERSION}
generated_at: "2025-01-15T11:00:00Z"

type_signatures:
  sync_{domain}:
    signature: "Credentials → Platform → Entities"
    proposition: "Given Credentials and Platform, can produce Entities"

    proof_of_totality: |
      Theorem: ∀ credentials platform. ∃ entities

      Proof:
        Given: credentials : Credentials, platform : Platform

        Case platform:
          {Platform} → {platform}_sync(credentials) : Entities ✓
          {AltPlatform} → {altplatform}_sync(credentials) : Entities ✓

        All cases covered.
        ∴ Function is total. QED

    verified: true
    proof_method: "case_analysis"
  
  validate_user:
    signature: "UserInput → Either[Error, User]"
    proposition: "Given UserInput, produce User or Error"
    
    proof_of_totality: |
      Theorem: ∀ input. ∃ result : Either[Error, User]
      
      Proof:
        Given: input : UserInput
        
        If valid(input):
          Right(User(input)) : Either[Error, User] ✓
        Else:
          Left(ValidationError) : Either[Error, User] ✓
        
        All branches covered (if-else exhaustive).
        ∴ Function is total. QED
    
    verified: true
    proof_method: "conditional_exhaustion"

impossible_states:
  checked: 47
  found: 0
  proof: "No path contains Never type. All paths implementable."

recursive_types:
  Tree:
    definition: "Leaf + (Node × Tree × Tree)"
    base_case: "Leaf"
    termination_proof: |
      Structural recursion on Tree:
        Base case: Leaf terminates
        Inductive: Recursive calls on smaller trees
      ∴ Well-founded. QED
    verified: true

summary:
  total_signatures: 23
  all_total: true
  no_impossible_states: true
  all_recursive_types_terminate: true
```

## Success Criteria

1. ✅ All function signatures proven total
2. ✅ No impossible states (no Never types)
3. ✅ Recursive types terminate
4. ✅ All proofs verified

## Next Steps

- Pass to **system-optimizer** for optimization
- Use in **architecture-validator** for law verification