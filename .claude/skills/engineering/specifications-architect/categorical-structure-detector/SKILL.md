---
name: categorical-structure-detector
description: Identify categorical structures from types, morphisms, and state machines. Detects categories, functors, adjunctions, natural transformations, limits, and Kleisli categories. Outputs architecture.categorical defining the mathematical structure of the system.
---

# Categorical Structure Detector

Analyze specifications to identify categorical structures. This skill bridges domain modeling and mathematical verification.

## Input

Requires all specification files:
- `artifacts/engineering/v{X}/specifications/requirements.adt`
- `artifacts/engineering/v{X}/specifications/services.spec.yaml`
- `artifacts/engineering/v{X}/specifications/state-machines.yaml`
- `artifacts/engineering/v{X}/specifications/constraints.yaml`

## Output

Generate `artifacts/engineering/v{X}/specifications/architecture.categorical`:

```yaml
version: "1.0"
sources:
  - requirements.adt
  - services.spec.yaml
  - state-machines.yaml
  - constraints.yaml

categories:
  - name: CategoryName
    description: "What this category represents"
    objects: [Object1, Object2]
    morphisms:
      - name: morphism_name
        domain: Object1
        codomain: Object2
    initial: InitialObject | null
    terminal: TerminalObject | null
    composition: "How morphisms compose"
    identity: "Identity morphism pattern"

functors:
  - name: FunctorName
    description: "What this functor does"
    source: SourceCategory
    target: TargetCategory
    object_map:
      SourceObject: TargetObject
    morphism_map:
      source_morphism: target_morphism
    preserves:
      - identity
      - composition

adjunctions:
  - name: AdjunctionName
    description: "What this adjunction represents"
    left: LeftFunctor
    right: RightFunctor
    unit:
      name: η
      components: "For each A, η_A: A → R(L(A))"
    counit:
      name: ε
      components: "For each B, ε_B: L(R(B)) → B"
    triangle_identities: true

natural_transformations:
  - name: TransformationName
    description: "What this transformation does"
    source_functor: F
    target_functor: G
    components:
      ObjectName: "α_A: F(A) → G(A)"
    naturality:
      domain: [morphism_names]  # Where naturality holds
      failures: [morphism_names]  # Where it breaks

monads:
  - name: MonadName
    description: "What effect this monad handles"
    functor: FunctorName
    unit:
      name: return | pure
      signature: "A → M[A]"
    multiplication:
      name: join | flatten
      signature: "M[M[A]] → M[A]"
    kleisli_composition:
      signature: "(A → M[B]) → (B → M[C]) → (A → M[C])"

limits:
  - name: LimitName
    type: product | pullback | equalizer | terminal
    diagram: "Shape of the diagram"
    limit_object: ObjectName
    projections: [projection_morphisms]
    universal_property: "Uniqueness statement"

colimits:
  - name: ColimitName
    type: coproduct | pushout | coequalizer | initial
    diagram: "Shape of the diagram"
    colimit_object: ObjectName
    injections: [injection_morphisms]
    universal_property: "Uniqueness statement"
```

## Detection Patterns

### Detecting Categories

**Domain Category**
```yaml
# From requirements.adt types + services.spec morphisms
categories:
  - name: Domain
    description: "Business domain types and operations"
    objects:
      - Merchant
      - Profile
      - Analysis
      - Recommendation
    morphisms:
      - name: create_merchant
        domain: CreateMerchantInput
        codomain: Merchant
      - name: analyze_profile
        domain: Profile
        codomain: Analysis
    initial: Unit  # Empty input
    terminal: Void  # No output
    composition: "Function composition"
    identity: "id_A: A → A"
```

**Storage Category**
```yaml
# Repository operations form a category
categories:
  - name: Storage
    description: "Database models and CRUD"
    objects:
      - MerchantModel
      - ProfileModel
      - AnalysisModel
    morphisms:
      - name: save
        domain: Model
        codomain: ModelId
      - name: find
        domain: ModelId
        codomain: Model
```

**Kleisli Category**
```yaml
# From effect-analyzer IO_Either morphisms
categories:
  - name: Kleisli_IO_Either
    description: "Effectful operations"
    objects: [A, B, C]  # Same as Domain objects
    morphisms:
      # f: A → IO[Either[E, B]] becomes A →_K B
      - name: create_merchant_k
        domain: CreateMerchantInput
        codomain: Merchant
    composition: "Kleisli composition (>=>)"
    identity: "return: A → IO[Either[E, A]]"
```

**Finite Categories**
```yaml
# From state-machines.yaml
categories:
  - name: AnalysisLifecycle
    description: "Analysis state machine"
    objects: [Pending, Processing, Completed, Failed]
    morphisms:
      - name: start
        domain: Pending
        codomain: Processing
      - name: complete
        domain: Processing
        codomain: Completed
      - name: fail
        domain: Processing
        codomain: Failed
    initial: Pending
    terminal: [Completed, Failed]
```

### Detecting Functors

**Repository Functor** (Domain → Storage)
```yaml
functors:
  - name: Repository
    source: Domain
    target: Storage
    object_map:
      Merchant: MerchantModel
      Profile: ProfileModel
      Analysis: AnalysisModel
    morphism_map:
      create_merchant: insert_merchant
      get_merchant: select_merchant
    preserves:
      - identity
      - composition
```

**Free Functor** (Storage → Domain)
```yaml
functors:
  - name: Free
    source: Storage
    target: Domain
    object_map:
      MerchantModel: Merchant
      ProfileModel: Profile
    morphism_map:
      select_merchant: get_merchant
    # Adjoint to Repository
```

**HTTP Functor** (Domain → HTTP)
```yaml
functors:
  - name: HTTP
    source: Domain
    target: HTTP
    object_map:
      Merchant: MerchantResponse
      CreateMerchantInput: CreateMerchantRequest
    morphism_map:
      create_merchant: POST /merchants
      get_merchant: GET /merchants/{id}
```

### Detecting Adjunctions

**Free ⊣ Repository**
```yaml
adjunctions:
  - name: FreeRepository
    description: "Domain-Storage adjunction"
    left: Free
    right: Repository
    unit:
      name: η
      components: "η_m: Merchant → Repository(Free(Merchant))"
      interpretation: "to_model then from_model"
    counit:
      name: ε
      components: "ε_M: Free(Repository(M)) → M"
      interpretation: "from_model then to_model"
    triangle_identities: true
```

### Detecting Natural Transformations

**Middleware as Natural Transformations**
```yaml
natural_transformations:
  - name: Auth
    description: "Authentication middleware"
    source_functor: HTTP
    target_functor: AuthHTTP
    components:
      Request: "auth_check: Request → AuthRequest"
      Response: "id: Response → Response"  # Identity on responses
    naturality:
      domain: [GET, POST, PUT, DELETE]
      failures: []  # Naturality holds everywhere

  - name: Validation
    source_functor: AuthHTTP
    target_functor: ValidHTTP
    components:
      CreateMerchantRequest: "validate: Create → ValidatedCreate"
    naturality:
      domain: [POST, PUT, PATCH]
      failures: [GET, DELETE]  # No validation needed
```

### Detecting Products and Coproducts

**Products**
```yaml
limits:
  - name: MerchantProfile
    type: product
    factors: [Merchant, Profile]
    limit_object: MerchantWithProfile
    projections:
      - π1: MerchantWithProfile → Merchant
      - π2: MerchantWithProfile → Profile
    universal_property: |
      For any Z with f: Z → Merchant and g: Z → Profile,
      exists unique h: Z → MerchantWithProfile
      such that π1 ∘ h = f and π2 ∘ h = g
```

**Coproducts**
```yaml
colimits:
  - name: AppError
    type: coproduct
    summands: [DomainError, InfraError, ExternalError]
    colimit_object: AppError
    injections:
      - inl: DomainError → AppError
      - inm: InfraError → AppError
      - inr: ExternalError → AppError
    universal_property: |
      For any Z with handlers for each error type,
      exists unique h: AppError → Z
```

### Detecting Monads

**IO Monad**
```yaml
monads:
  - name: IO
    description: "Side effects"
    functor: IO
    unit:
      name: pure
      signature: "A → IO[A]"
      implementation: "async def pure(a): return a"
    multiplication:
      name: flatten
      signature: "IO[IO[A]] → IO[A]"
      implementation: "await (await outer)"
    kleisli_composition: |
      (f >=> g)(a) = f(a).flatMap(g)
```

**Either Monad**
```yaml
monads:
  - name: Either
    description: "Error handling"
    functor: Either
    unit:
      name: Right
      signature: "A → Either[E, A]"
    multiplication:
      name: flatten
      signature: "Either[E, Either[E, A]] → Either[E, A]"
```

**Composed Monad**
```yaml
monads:
  - name: IO_Either
    description: "IO with errors"
    base: IO
    transformer: EitherT
    distributive_law:
      name: δ
      signature: "Either[E, IO[A]] → IO[Either[E, A]]"
```

## Validation Checklist

Before outputting, verify:

- [ ] Every category has identity morphisms
- [ ] Composition is associative
- [ ] Functors preserve identity and composition
- [ ] Adjunction triangle identities hold
- [ ] Natural transformation components are defined
- [ ] Monad laws are satisfiable
- [ ] Limits have universal property

## Structure Detection Heuristics

| Pattern | Indicates |
|---------|-----------|
| Matching to_/from_ functions | Adjunction |
| Middleware chain | Natural transformations |
| Union types | Coproduct |
| Tuple/record types | Product |
| Async operations | IO functor |
| Result/Either returns | Either monad |
| State transitions | Finite category |
| CRUD for entity | Repository functor |

## Next Skill

Output feeds into:
- **proof-obligation-generator** → categorical laws become proofs
- Standards layer → laws to verify
