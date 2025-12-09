---
name: certificate-generator
description: |
  Generate runtime certificates from proven theorems. Creates YAML certificate files
  that can be used for runtime verification and documentation. Aggregates all proofs
  into a manifest for the code layer.
  Input: All proofs/lean/LeanOS/*.lean files
  Output: proofs/certificates/*.cert.yaml, proofs/certificates/manifest.yaml
---

# Certificate Generator

Generate runtime certificates from Lean proofs.

## Purpose

Transform proven theorems into runtime-usable certificates:
1. Extract proof metadata (theorem name, status, hash)
2. Generate per-category certificates
3. Create aggregate manifest
4. Enable runtime property checking

## Input

All Lean proof files:
```
proofs/lean/LeanOS/
├── Identity.lean
├── Composition.lean
├── Functor.lean
├── Adjunction.lean
├── Monad.lean
└── NaturalTransformation.lean
```

## Output

```
proofs/certificates/
├── identity.cert.yaml       # Identity law certificates
├── composition.cert.yaml    # Composition certificates
├── functor.cert.yaml        # Functor certificates
├── adjunction.cert.yaml     # Adjunction certificates
├── monad.cert.yaml          # Monad certificates
├── naturality.cert.yaml     # Naturality certificates
└── manifest.yaml            # Aggregate manifest
```

## Certificate Structure

### Individual Certificate Schema

```yaml
# proofs/certificates/{category}.cert.yaml

certificate:
  category: "{category}"
  generated_at: "2024-01-15T12:00:00Z"
  lean_version: "4.3.0"
  mathlib_version: "latest"
  
  proofs:
    - theorem: "{theorem_name}"
      file: "LeanOS/{File}.lean"
      line: 42
      status: proven  # proven | partial | axiom
      hash: "sha256:abc123..."
      dependencies:
        - theorem: "other_theorem"
          file: "LeanOS/Other.lean"
      statement: |
        ∀ f : A ⟶ B, 𝟙 A ≫ f = f
      proof_strategy: "simp [Category.id_comp]"
      
  summary:
    total: 12
    proven: 12
    partial: 0
    axioms: 0
```

### Certificate Templates

#### identity.cert.yaml

```yaml
certificate:
  category: identity
  generated_at: "{timestamp}"
  lean_version: "4.3.0"
  
  proofs:
    # Domain category
    - theorem: domain_left_id
      file: LeanOS/Identity.lean
      status: proven
      statement: "∀ f : A ⟶ B, 𝟙 A ≫ f = f"
      runtime_check: |
        assert compose(identity(A), f) == f
        
    - theorem: domain_right_id
      file: LeanOS/Identity.lean
      status: proven
      statement: "∀ f : A ⟶ B, f ≫ 𝟙 B = f"
      runtime_check: |
        assert compose(f, identity(B)) == f
        
    # HTTP category
    - theorem: http_left_id
      file: LeanOS/Identity.lean
      status: proven
      statement: "∀ handler, id ∘ handler = handler"
      
    - theorem: http_right_id
      file: LeanOS/Identity.lean
      status: proven
      statement: "∀ handler, handler ∘ id = handler"
      
    # Kleisli category
    - theorem: kleisli_io_left_id
      file: LeanOS/Identity.lean
      status: proven
      statement: "pure >>= f = f"
      runtime_check: |
        assert await (pure(a).bind(f)) == await f(a)
        
    - theorem: kleisli_io_right_id
      file: LeanOS/Identity.lean
      status: proven
      statement: "m >>= pure = m"
      runtime_check: |
        assert await (m.bind(pure)) == await m
        
  summary:
    total: 6
    proven: 6
    partial: 0
    axioms: 0
```

#### functor.cert.yaml

```yaml
certificate:
  category: functor
  generated_at: "{timestamp}"
  lean_version: "4.3.0"
  
  proofs:
    # HTTP Functor
    - theorem: http_functor_id
      file: LeanOS/Functor.lean
      status: proven
      statement: "HTTPFunctor.map(id) = id"
      implementation_check: |
        # Verify in code: HTTP adapter maps identity to identity
        assert http_adapter.map(domain_id) == http_id
        
    - theorem: http_functor_comp
      file: LeanOS/Functor.lean
      status: proven
      statement: "HTTPFunctor.map(g ∘ f) = HTTPFunctor.map(g) ∘ HTTPFunctor.map(f)"
      implementation_check: |
        # Verify composition preserved
        assert http_adapter.map(compose(g, f)) == compose(http_adapter.map(g), http_adapter.map(f))
        
    # Storage Functor
    - theorem: storage_functor_id
      file: LeanOS/Functor.lean
      status: proven
      statement: "StorageFunctor.map(id) = id"
      
    - theorem: storage_functor_comp
      file: LeanOS/Functor.lean
      status: proven
      statement: "StorageFunctor.map(g ∘ f) = StorageFunctor.map(g) ∘ StorageFunctor.map(f)"
      
  summary:
    total: 4
    proven: 4
```

#### adjunction.cert.yaml

```yaml
certificate:
  category: adjunction
  generated_at: "{timestamp}"
  
  proofs:
    # Repository adjunction
    - theorem: repository_adjunction_exists
      file: LeanOS/Adjunction.lean
      status: proven
      statement: "Free ⊣ Repository"
      
    - theorem: repository_left_triangle
      file: LeanOS/Adjunction.lean
      status: proven
      statement: "(ε ∘ Free) ∘ (Free ∘ η) = id"
      implementation_check: |
        # Round-trip: save then load = identity (up to iso)
        entity = create_entity()
        saved = await repository.save(entity)
        loaded = await repository.get(saved.id)
        assert loaded.to_domain() == entity
        
    - theorem: repository_right_triangle
      file: LeanOS/Adjunction.lean
      status: proven
      statement: "(Repository ∘ ε) ∘ (η ∘ Repository) = id"
      
    # Cache adjunction
    - theorem: cache_left_triangle
      file: LeanOS/Adjunction.lean
      status: proven
      statement: "get(put(a)) = a"
      implementation_check: |
        # Cache round-trip
        await cache.set(key, value)
        cached = await cache.get(key)
        assert cached == value
```

#### monad.cert.yaml

```yaml
certificate:
  category: monad
  generated_at: "{timestamp}"
  
  proofs:
    # IO Monad
    - theorem: io_left_identity
      file: LeanOS/Monad.lean
      status: proven
      statement: "pure(a) >>= f = f(a)"
      runtime_check: |
        assert await (asyncio.coroutine(lambda: a)().bind(f)) == await f(a)
        
    - theorem: io_right_identity
      file: LeanOS/Monad.lean
      status: proven
      statement: "m >>= pure = m"
      
    - theorem: io_associativity
      file: LeanOS/Monad.lean
      status: proven
      statement: "(m >>= f) >>= g = m >>= (x => f(x) >>= g)"
      runtime_check: |
        # Effect composition is associative
        result1 = await ((await m()).bind(f)).bind(g)
        result2 = await m().bind(lambda x: f(x).bind(g))
        assert result1 == result2
        
    # Either Monad
    - theorem: either_left_identity
      file: LeanOS/Monad.lean
      status: proven
      statement: "Success(a).bind(f) = f(a)"
      
    - theorem: either_right_identity
      file: LeanOS/Monad.lean
      status: proven
      
    - theorem: either_associativity
      file: LeanOS/Monad.lean
      status: proven
      
    # Transaction Monad
    - theorem: transaction_left_identity
      file: LeanOS/Monad.lean
      status: proven
      
    - theorem: transaction_right_identity
      file: LeanOS/Monad.lean
      status: partial
      note: "Requires IO-specific axioms"
      
    - theorem: transaction_associativity
      file: LeanOS/Monad.lean
      status: partial
      note: "Requires IO-specific axioms"
```

### Manifest Schema

```yaml
# proofs/certificates/manifest.yaml

manifest:
  version: "1.0.0"
  generated_at: "2024-01-15T12:00:00Z"
  
  lean_project:
    version: "4.3.0"
    mathlib: true
    build_command: "lake build"
    
  specification_version: "1.0.0"
  standards_version: "1.0.0"
  maps_version: "1.0.0"
  
  certificates:
    - file: identity.cert.yaml
      category: identity
      proofs: 6
      all_proven: true
      
    - file: composition.cert.yaml
      category: composition
      proofs: 8
      all_proven: true
      
    - file: functor.cert.yaml
      category: functor
      proofs: 8
      all_proven: true
      
    - file: adjunction.cert.yaml
      category: adjunction
      proofs: 6
      all_proven: true
      
    - file: monad.cert.yaml
      category: monad
      proofs: 12
      all_proven: false
      partial: 2
      note: "Transaction monad requires IO axioms"
      
    - file: naturality.cert.yaml
      category: naturality
      proofs: 10
      all_proven: true
      
  summary:
    total_theorems: 50
    proven: 48
    partial: 2
    axioms: 0
    coverage: 96%
    
  runtime_guards:
    enabled: true
    categories:
      - identity
      - composition
      - functor
      - monad
    check_on:
      - startup
      - deployment
      
  verification:
    all_lean_compiles: true
    no_sorry: true
    no_admit: true
    mathlib_compatible: true
```

## Generation Process

```yaml
generation:
  steps:
    - name: parse_lean_files
      action: "Extract theorem definitions from .lean files"
      
    - name: verify_compilation
      action: "Run `lake build` to verify all proofs compile"
      
    - name: extract_metadata
      action: "Extract theorem names, statements, line numbers"
      
    - name: compute_hashes
      action: "SHA-256 hash of each proof"
      
    - name: generate_certificates
      action: "Create per-category certificate files"
      
    - name: generate_manifest
      action: "Aggregate into manifest.yaml"
      
    - name: validate_certificates
      action: "Verify certificate structure"
```

## Runtime Guard Generation

```yaml
runtime_guards:
  purpose: |
    Generate Python/TypeScript code that can verify properties at runtime.
    Used for defense-in-depth when formal proofs exist.
    
  template:
    python: |
      def verify_{property}() -> bool:
          """
          Runtime verification of {theorem}.
          
          Proven in Lean: {file}:{line}
          Certificate: {cert_file}
          """
          {implementation_check}
          return True
          
      # Example generated guard
      def verify_monad_left_identity() -> bool:
          """Verify pure(a) >>= f = f(a)"""
          a = "test_value"
          f = lambda x: Success(x.upper())
          lhs = Success(a).bind(f)
          rhs = f(a)
          return lhs == rhs
```

## Validation Checks

```yaml
validation:
  certificates_valid:
    check: "All certificate files have valid YAML"
    
  manifest_complete:
    check: "Manifest includes all certificates"
    
  hashes_match:
    check: "Proof hashes match actual file content"
    
  coverage_complete:
    check: "All required theorems have certificates"
```

## Next Skills

Output feeds into:
- `proofs-validator`
- (future) `code-architect`
