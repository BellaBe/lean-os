---
name: proof-obligation-generator
description: Generate type-level proof obligations from constraints and categorical structure. Outputs types.curry-howard defining dependent types, invariant proofs, and categorical law obligations. Creates the bridge between specification and formal verification in Lean 4.
---

# Proof Obligation Generator

Transform constraints and categorical structure into proof obligations. Uses Curry-Howard correspondence: types are propositions, programs are proofs.

## Input

Requires:
- `artifacts/engineering/v{X}/specifications/constraints.yaml`
- `artifacts/engineering/v{X}/specifications/architecture.categorical`
- `artifacts/engineering/v{X}/specifications/requirements.adt`

## Output

Generate `artifacts/engineering/v{X}/specifications/types.curry-howard`:

```yaml
version: "1.0"
sources:
  - constraints.yaml
  - architecture.categorical
  - requirements.adt

dependent_types:
  # Types that carry their proofs
  - name: TypeName
    base: BaseType
    predicate: "P(x)"
    curry_howard: "Σ(x: Base). P(x)"
    lean_type: "{x : Base // P x}"

proof_obligations:
  # Things that must be proven
  - name: ObligationName
    statement: "What must be proven"
    formal: "Logical formula"
    curry_howard: "Type that proves this"
    source: constraints | categorical | invariant
    difficulty: trivial | decidable | requires_proof
    lean_signature: "theorem name : statement"

categorical_laws:
  # Laws from categorical structure
  - category: CategoryName
    laws:
      - name: LawName
        statement: "Law statement"
        lean_obligation: "Lean 4 type"

type_inhabitants:
  # Proof that types are inhabited
  - type: TypeName
    inhabitant: "Example value"
    proof: "Why this satisfies the type"

totality_proofs:
  # Functions are total
  - morphism: morphism_name
    domain_coverage: "Covers all inputs"
    termination: "Always terminates"
```

## Curry-Howard Correspondence

### Propositions as Types

| Logic | Type Theory | Lean 4 |
|-------|-------------|--------|
| P ∧ Q | P × Q (product) | `P × Q` |
| P ∨ Q | P + Q (coproduct) | `P ⊕ Q` or `Sum P Q` |
| P → Q | P → Q (function) | `P → Q` |
| ∀x. P(x) | Π(x: A). P(x) | `∀ x : A, P x` |
| ∃x. P(x) | Σ(x: A). P(x) | `∃ x : A, P x` or `{x : A // P x}` |
| ¬P | P → ⊥ | `P → False` |
| True | Unit | `Unit` or `True` |
| False | Empty | `Empty` or `False` |

### From Constraints to Types

```yaml
# Constraint (from constraints.yaml)
invariants:
  - name: PositiveOrderTotal
    type: Order
    formal: "∀o: Order. o.total > 0"

# Proof obligation (to types.curry-howard)
dependent_types:
  - name: ValidOrder
    base: Order
    predicate: "total > 0"
    curry_howard: "Σ(o: Order). o.total > 0"
    lean_type: "{o : Order // o.total > 0}"

proof_obligations:
  - name: OrderTotalPositive
    statement: "Every created order has positive total"
    formal: "∀o: Order. o.total > 0"
    curry_howard: "Π(o: Order). Proof(o.total > 0)"
    lean_signature: "theorem order_total_positive (o : Order) : o.total > 0"
```

## Proof Obligation Patterns

### Invariant Proofs

```yaml
# Type invariant
proof_obligations:
  - name: MerchantHasValidShop
    statement: "Merchant shop domain is valid Shopify domain"
    formal: "∀m: Merchant. IsValidShopifyDomain(m.shop_domain)"
    curry_howard: "Π(m: Merchant). ValidShopDomain(m.shop_domain)"
    source: invariant
    difficulty: decidable
    lean_signature: |
      theorem merchant_shop_valid (m : Merchant) : 
        IsValidShopifyDomain m.shop_domain
```

### Pre/Post Condition Proofs

```yaml
# Pre-condition becomes dependent function type
proof_obligations:
  - name: AnalysisRequiresPhoto
    statement: "request_analysis requires photo"
    formal: "photo ≠ ∅ → can_request_analysis"
    curry_howard: "NonEmptyPhoto → IO[Either[E, Analysis]]"
    source: constraints
    difficulty: trivial  # Type system enforces
    lean_signature: |
      def request_analysis (photo : NonEmptyPhoto) : IO (Except E Analysis)

# Post-condition becomes return type refinement
proof_obligations:
  - name: CreatedMerchantHasId
    statement: "created merchant has valid ID"
    formal: "create_merchant(...) → result.id ≠ null"
    curry_howard: "CreateInput → IO[Either[E, {m: Merchant // m.id ≠ null}]]"
    source: constraints
    difficulty: trivial
```

### Categorical Law Proofs

```yaml
categorical_laws:
  - category: Domain
    laws:
      - name: composition_associativity
        statement: "(h ∘ g) ∘ f = h ∘ (g ∘ f)"
        lean_obligation: |
          theorem comp_assoc {A B C D : Type} 
            (f : A → B) (g : B → C) (h : C → D) :
            (h ∘ g) ∘ f = h ∘ (g ∘ f) := rfl

      - name: left_identity
        statement: "id ∘ f = f"
        lean_obligation: |
          theorem left_id {A B : Type} (f : A → B) :
            id ∘ f = f := rfl

      - name: right_identity
        statement: "f ∘ id = f"
        lean_obligation: |
          theorem right_id {A B : Type} (f : A → B) :
            f ∘ id = f := rfl

  - category: Kleisli_IO_Either
    laws:
      - name: kleisli_left_identity
        statement: "return >=> f = f"
        lean_obligation: |
          theorem kleisli_left_id {A B : Type} {E : Type}
            (f : A → IO (Except E B)) :
            (fun a => pure (Except.ok a)) >=> f = f

      - name: kleisli_associativity
        statement: "(f >=> g) >=> h = f >=> (g >=> h)"
        lean_obligation: |
          theorem kleisli_assoc {A B C D : Type} {E : Type}
            (f : A → IO (Except E B))
            (g : B → IO (Except E C))
            (h : C → IO (Except E D)) :
            (f >=> g) >=> h = f >=> (g >=> h)
```

### Functor Law Proofs

```yaml
categorical_laws:
  - category: Functors
    laws:
      - name: repository_preserves_identity
        statement: "Repository(id_A) = id_{Repository(A)}"
        lean_obligation: |
          theorem repo_id {A : Type} :
            Repository.map id = id

      - name: repository_preserves_composition
        statement: "Repository(g ∘ f) = Repository(g) ∘ Repository(f)"
        lean_obligation: |
          theorem repo_comp {A B C : Type} (f : A → B) (g : B → C) :
            Repository.map (g ∘ f) = Repository.map g ∘ Repository.map f
```

### Adjunction Proofs

```yaml
categorical_laws:
  - category: Adjunctions
    laws:
      - name: left_triangle_identity
        statement: "(ε ∘ F) ∘ (F ∘ η) = id_F"
        lean_obligation: |
          theorem left_triangle {F : Storage → Domain} {G : Domain → Storage}
            (adj : F ⊣ G) :
            (adj.counit.app ∘ F.map) ∘ (F.map ∘ adj.unit.app) = id

      - name: right_triangle_identity
        statement: "(G ∘ ε) ∘ (η ∘ G) = id_G"
        lean_obligation: |
          theorem right_triangle {F : Storage → Domain} {G : Domain → Storage}
            (adj : F ⊣ G) :
            (G.map ∘ adj.counit.app) ∘ (adj.unit.app ∘ G.map) = id
```

### Monad Law Proofs

```yaml
categorical_laws:
  - category: Monads
    laws:
      - name: io_either_left_identity
        statement: "return a >>= f = f a"
        lean_obligation: |
          theorem left_id {A B : Type} {E : Type}
            (a : A) (f : A → IO (Except E B)) :
            (pure (Except.ok a) >>= f) = f a

      - name: io_either_right_identity
        statement: "m >>= return = m"
        lean_obligation: |
          theorem right_id {A : Type} {E : Type}
            (m : IO (Except E A)) :
            (m >>= fun a => pure (Except.ok a)) = m

      - name: io_either_associativity
        statement: "(m >>= f) >>= g = m >>= (λx. f x >>= g)"
        lean_obligation: |
          theorem assoc {A B C : Type} {E : Type}
            (m : IO (Except E A))
            (f : A → IO (Except E B))
            (g : B → IO (Except E C)) :
            ((m >>= f) >>= g) = (m >>= fun x => f x >>= g)
```

### Natural Transformation Proofs

```yaml
categorical_laws:
  - category: NaturalTransformations
    laws:
      - name: auth_naturality
        statement: "For all f: A → B, α_B ∘ F(f) = G(f) ∘ α_A"
        lean_obligation: |
          theorem auth_naturality {A B : Type}
            (f : A → B) :
            auth_transform B ∘ HTTP.map f = AuthHTTP.map f ∘ auth_transform A
```

## Type Inhabitedness

```yaml
type_inhabitants:
  - type: Merchant
    inhabitant: |
      Merchant {
        id = MerchantId("uuid"),
        shop_domain = ShopDomain("test.myshopify.com"),
        subscription = Subscription { tier = Free, expires_at = None }
      }
    proof: "All fields have valid values satisfying constraints"

  - type: ValidOrder
    inhabitant: |
      ValidOrder {
        order = Order { id = OrderId("1"), total = Money(100) },
        proof = positive_proof  -- Proof that 100 > 0
      }
    proof: "Refinement type is inhabited when base type has valid value"
```

## Totality Proofs

```yaml
totality_proofs:
  - morphism: validate_email
    domain: String
    codomain: Either[ValidationError, Email]
    domain_coverage: "Handles empty, invalid format, valid"
    termination: "Pattern match terminates"
    
  - morphism: analyze_photo
    domain: Photo
    codomain: IO[Either[AnalysisError, AnalysisResult]]
    domain_coverage: "All photo formats handled"
    termination: "Bounded by timeout"
    note: "Partial due to external dependency - Either captures failure"
```

## Proof Difficulty Classification

| Difficulty | Meaning | Verification |
|------------|---------|--------------|
| trivial | Type system enforces | Compilation |
| decidable | Runtime checkable | Property tests |
| requires_proof | Needs formal proof | Lean 4 |

## Validation Checklist

Before outputting, verify:

- [ ] All constraints have proof obligations
- [ ] Categorical laws are captured
- [ ] Dependent types have valid Lean signatures
- [ ] Types are inhabited (not empty)
- [ ] Proof difficulty is classified
- [ ] Sources are tracked

## Next Skill

Output feeds into:
- **specification-validator** → validates completeness
- Proof layer → Lean 4 verification
