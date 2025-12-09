---
name: level-4-categories
description: |
  Level 4: Categories and Monads. Formalize the category structure from Levels 1-3,
  including Kleisli categories for effectful composition.
  
  A category has objects, morphisms, identity, and composition with laws.
  A monad enables composition of effectful morphisms via Kleisli category.
  
  Input: level-0.manifest.yaml (effects), level-1.manifest.yaml, level-2.manifest.yaml, level-3.manifest.yaml
  Output: level-4.manifest.yaml + category definitions + monad definitions + laws
  
  UNIVERSAL: Works for any domain. Examples are illustrative only.
---

# Level 4: Categories and Monads

Formalization of categorical structure including effectful composition.

## Principle

A category C consists of:
- Objects: ob(C)
- Morphisms: hom(C)  
- Identity: id_A for each object A
- Composition: g ∘ f for composable morphisms
- Laws: Identity and associativity

```
Category C:
  Objects: Level 1 entities
  Morphisms: Level 2 morphisms
  Identity: id_A: A → A (∀ A ∈ ob(C))
  Composition: g ∘ f: A → C (when f: A → B, g: B → C)
  
Laws:
  Left identity:  id_B ∘ f = f
  Right identity: f ∘ id_A = f
  Associativity:  (h ∘ g) ∘ f = h ∘ (g ∘ f)
```

**Critical insight:** Most Level 2 morphisms are NOT `A → B`. They are `A → M[B]` where M is an effect monad. These compose via Kleisli composition, not regular composition.

## Monads

A monad M consists of:

```
Monad M:
  Functor:  M: Type → Type
  Unit:     pure: A → M[A]           (also: return, unit, η)
  Bind:     (>>=): M[A] → (A → M[B]) → M[B]
  
Laws:
  Left identity:   pure a >>= f      ≡  f a
  Right identity:  m >>= pure        ≡  m
  Associativity:   (m >>= f) >>= g   ≡  m >>= (λx. f x >>= g)
```

Equivalently via join:

```
  Join:     join: M[M[A]] → M[A]     (also: flatten, μ)
  
Laws:
  join ∘ pure      = id
  join ∘ M(pure)   = id
  join ∘ join      = join ∘ M(join)
```

## Standard Monads

From Level 0 effects:

```yaml
monads:
  IO:
    type: "IO[A]"
    description: "Deferred side effects"
    pure: "IO.pure(a) - wrap value without side effect"
    bind: "io.flatMap(f) - sequence effects"
    use_case: "Database, network, file system, logging"
    
  Either:
    type: "Either[E, A]"
    description: "Computation that may fail"
    pure: "Right(a) - success value"
    bind: "either.flatMap(f) - short-circuit on Left"
    use_case: "Validation, error handling"
    
  Reader:
    type: "Reader[R, A]"
    description: "Computation requiring environment"
    pure: "Reader.pure(a) - ignore environment"
    bind: "reader.flatMap(f) - thread environment"
    use_case: "Dependency injection, configuration"
    
  State:
    type: "State[S, A]"
    description: "Stateful computation"
    pure: "State.pure(a) - no state change"
    bind: "state.flatMap(f) - thread state"
    use_case: "Accumulators, generators"
    
  Option:
    type: "Option[A]"
    description: "Optional value"
    pure: "Some(a)"
    bind: "option.flatMap(f) - short-circuit on None"
    use_case: "Missing values, partial functions"
```

## Monad Transformers

For stacking effects:

```yaml
transformers:
  ReaderT:
    definition: "ReaderT[R, M, A] = R → M[A]"
    lifts: "Reader into M"
    
  EitherT:
    definition: "EitherT[E, M, A] = M[Either[E, A]]"
    lifts: "Either into M"
    
  StateT:
    definition: "StateT[S, M, A] = S → M[(A, S)]"
    lifts: "State into M"
    
  OptionT:
    definition: "OptionT[M, A] = M[Option[A]]"
    lifts: "Option into M"
```

## The App Monad

Most service morphisms live in a stacked monad:

```yaml
app_monad:
  name: "App"
  definition: "App[A] = ReaderT[Config, IO, Either[Error, A]]"
  simplified: "Config → IO[Either[Error, A]]"
  
  components:
    - Reader[Config]: "Dependency injection"
    - IO: "Side effects"
    - Either[Error, _]: "Error handling"
    
  operations:
    pure: "App.pure(a) = _ → IO.pure(Right(a))"
    bind: |
      app.flatMap(f) = config → 
        app(config).flatMap {
          case Right(a) => f(a)(config)
          case Left(e) => IO.pure(Left(e))
        }
        
  laws: "Inherits from component monads"
```

## Kleisli Categories

For each monad M, there is a Kleisli category:

```
Kleisli[M]:
  Objects: Same as base category (types)
  Morphisms: A → M[B]  (Kleisli arrows)
  Identity: pure: A → M[A]
  Composition: (>=>) : (A → M[B]) → (B → M[C]) → (A → M[C])
               f >=> g = λa. f(a) >>= g
```

Kleisli composition:

```
(>=>): (A → M[B]) → (B → M[C]) → (A → M[C])
(f >=> g)(a) = f(a).flatMap(g)

Laws (equivalent to monad laws):
  Left identity:   pure >=> f      ≡  f
  Right identity:  f >=> pure      ≡  f
  Associativity:   (f >=> g) >=> h ≡  f >=> (g >=> h)
```

## Standard Categories

```yaml
categories:
  Domain:
    type: "category"
    description: "Pure domain - no effects"
    objects: "Level 1 entities"
    morphisms: "Pure functions A → B"
    composition: "Regular (∘)"
    role: "Source of truth for domain model"
    
  Kleisli_IO:
    type: "kleisli_category"
    monad: "IO"
    description: "Effectful computations"
    objects: "Types"
    morphisms: "A → IO[B]"
    identity: "IO.pure"
    composition: "(>=>)"
    role: "Side-effecting operations"
    
  Kleisli_Result:
    type: "kleisli_category"
    monad: "Either[Error, _]"
    description: "Fallible computations"
    objects: "Types"
    morphisms: "A → Either[Error, B]"
    identity: "Right"
    composition: "(>=>)"
    role: "Validation, parsing"
    
  Kleisli_App:
    type: "kleisli_category"
    monad: "App"
    description: "Full application effect stack"
    objects: "Types"
    morphisms: "A → App[B]"
    identity: "App.pure"
    composition: "(>=>)"
    role: "WHERE MOST SERVICE MORPHISMS LIVE"
    note: "Level 2 morphisms with effects are Kleisli_App arrows"
    
  Storage:
    type: "category"
    description: "Persistent storage representation"
    objects: "Database models/tables"
    morphisms: "CRUD operations (in Kleisli_IO)"
    role: "Target for Repository functor"
    
  HTTP:
    type: "category"
    description: "HTTP request/response"
    objects: "Request/Response DTOs"
    morphisms: "HTTP handlers (in Kleisli_App)"
    role: "Target for HTTP functor"
    
  External:
    type: "category"
    description: "External service APIs"
    objects: "External DTOs"
    morphisms: "API client operations (in Kleisli_App)"
    role: "Target for External functor"
```

## Process

```yaml
process:
  step_1_load_inputs:
    inputs:
      - "level-0.manifest.yaml"   # Effects (monads)
      - "level-1.manifest.yaml"   # Objects
      - "level-2.manifest.yaml"   # Morphisms
      - "level-3.manifest.yaml"   # Modules (for grouping context)
    action: "Load and validate inputs exist"
    
  step_2_enumerate_monads:
    action: "Identify monads from Level 0 effects and Level 2 signatures"
    algorithm: |
      monads = []
      
      # Base monads from Level 0
      for effect in level_0.effects:
          monads.append(Monad(effect))
          
      # Determine App monad stack from morphism patterns
      effect_stack = analyze_morphism_effects(level_2.morphisms)
      app_monad = build_app_monad(effect_stack)
      monads.append(app_monad)
      
      return monads
    
  step_3_enumerate_categories:
    action: "Determine categories needed"
    algorithm: |
      categories = [Domain]  # Always have Domain
      
      # Kleisli category for each monad
      for monad in monads:
          categories.append(Kleisli(monad))
          
      # Target categories
      if has_persistence:
          categories.append(Storage)
      if has_http_api:
          categories.append(HTTP)
      if has_external_services:
          categories.append(External)
          
      return categories
    
  step_4_classify_morphisms:
    action: "Classify each Level 2 morphism into appropriate category"
    algorithm: |
      for morphism in level_2.morphisms:
          if morphism.effects == []:
              assign_to(morphism, Domain)
          else:
              kleisli_cat = determine_kleisli_category(morphism.effects)
              assign_to(morphism, kleisli_cat)
    critical: "Every morphism must belong to exactly one category"
    
  step_5_define_domain_category:
    action: "Define Domain category (pure morphisms only)"
    algorithm: |
      Domain = Category(
          objects = level_1.items.where(kind="entity"),
          morphisms = level_2.items.where(effects=[]),
          identities = level_2.items.where(kind="identity")
      )
      
  step_6_define_kleisli_categories:
    action: "Define Kleisli category for each monad"
    for_each: "monad in monads"
    algorithm: |
      Kleisli[monad] = KleisliCategory(
          monad = monad,
          objects = level_1.items.where(kind="entity"),
          morphisms = level_2.items.where(effects contains monad),
          identity = monad.pure,
          composition = kleisli_compose
      )
      
  step_7_define_target_categories:
    action: "Define target categories (Storage, HTTP, External)"
    note: "These live in appropriate Kleisli categories"
    
  step_8_validate_laws:
    action: "Generate proof obligations for all laws"
    checks:
      # Category laws
      - identity_left: "∀ f: id ∘ f = f"
      - identity_right: "∀ f: f ∘ id = f"
      - associativity: "∀ f,g,h: (h ∘ g) ∘ f = h ∘ (g ∘ f)"
      # Monad laws
      - monad_left_id: "∀ monad M: pure >=> f ≡ f"
      - monad_right_id: "∀ monad M: f >=> pure ≡ f"
      - monad_assoc: "∀ monad M: (f >=> g) >=> h ≡ f >=> (g >=> h)"
    critical: "All laws generate proof obligations for Level 8"
    
  step_9_produce_manifest:
    action: "Write level-4.manifest.yaml"
    includes:
      - monads
      - categories
      - kleisli_categories
      - proof_obligations
```

## Monad Manifest Schema

```yaml
monad_item:
  id: "monad.{Name}"
  name: "{Name}"
  kind: "monad"
  traces:
    - ref: "level-0.effect.{Effect}"
      role: "effect"
  definition:
    type_constructor: "{M[_]}"
    pure:
      signature: "A → M[A]"
      implementation: "{how to lift pure value}"
    bind:
      signature: "M[A] → (A → M[B]) → M[B]"
      implementation: "{how to sequence}"
    # Alternative: join formulation
    map:
      signature: "(A → B) → M[A] → M[B]"
    join:
      signature: "M[M[A]] → M[A]"
  laws:
    left_identity:
      statement: "pure a >>= f  ≡  f a"
      proof_obligation: "level-8.proof.monad.{Name}.left_id"
    right_identity:
      statement: "m >>= pure  ≡  m"
      proof_obligation: "level-8.proof.monad.{Name}.right_id"
    associativity:
      statement: "(m >>= f) >>= g  ≡  m >>= (λx. f x >>= g)"
      proof_obligation: "level-8.proof.monad.{Name}.assoc"
  status: "pending|defined|laws_verified"
```

## Kleisli Category Manifest Schema

```yaml
kleisli_category_item:
  id: "kleisli.{MonadName}"
  name: "Kleisli[{MonadName}]"
  kind: "kleisli_category"
  traces:
    - ref: "monad.{MonadName}"
      role: "monad"
    - ref: "level-1.entity.{Entity}"
      role: "object"
    - ref: "level-2.morphism.{module}.{op}"
      role: "morphism"
  definition:
    monad: "{MonadName}"
    objects:
      source: "Same as base category"
      count: N
    morphisms:
      type: "A → M[B]"
      items: ["morphisms with this effect"]
    identity:
      is: "pure: A → M[A]"
    composition:
      operator: "(>=>)"
      definition: "f >=> g = λa. f(a) >>= g"
  laws:
    # Kleisli laws (equivalent to monad laws)
    left_identity:
      statement: "pure >=> f  ≡  f"
      proof_obligation: "level-8.proof.kleisli.{MonadName}.left_id"
    right_identity:
      statement: "f >=> pure  ≡  f"
      proof_obligation: "level-8.proof.kleisli.{MonadName}.right_id"
    associativity:
      statement: "(f >=> g) >=> h  ≡  f >=> (g >=> h)"
      proof_obligation: "level-8.proof.kleisli.{MonadName}.assoc"
  status: "pending|defined|laws_verified"
```

## App Monad Schema

```yaml
app_monad_item:
  id: "monad.App"
  name: "App"
  kind: "monad"
  subkind: "transformer_stack"
  traces:
    - ref: "monad.IO"
      role: "base"
    - ref: "monad.Either"
      role: "layer"
    - ref: "monad.Reader"
      role: "layer"
  definition:
    stack:
      - {position: "outer", transformer: "ReaderT", param: "Config"}
      - {position: "middle", monad: "IO"}
      - {position: "inner", transformer: "EitherT", param: "Error"}
    expanded: "Config → IO[Either[Error, A]]"
    pure:
      signature: "A → App[A]"
      implementation: "λa. λconfig. IO.pure(Right(a))"
    bind:
      signature: "App[A] → (A → App[B]) → App[B]"
      implementation: |
        λma. λf. λconfig.
          ma(config).flatMap {
            case Right(a) => f(a)(config)
            case Left(e)  => IO.pure(Left(e))
          }
  laws:
    note: "Inherited from component monads - transformer laws preserve monad laws"
  status: "defined"
```

```yaml
category_pattern:
  name: "{CategoryName}"
  
  objects:
    source: "Level 1 or derived"
    items:
      - ref: "level-1.entity.{Entity}"
      # All objects in this category
      
  morphisms:
    source: "Level 2 or derived"
    items:
      - ref: "level-2.morphism.{module}.{operation}"
      # All morphisms in this category
      
  identities:
    source: "Level 2 identities"
    items:
      - ref: "level-2.morphism.identity.{Entity}"
      # One identity per object
      
  composition:
    defined_by: "Type matching: codomain(f) = domain(g)"
    
  laws:
    identity_left:
      statement: "∀ f: A → B. id_B ∘ f = f"
      proof_obligation: "Verify for all morphisms"
    identity_right:
      statement: "∀ f: A → B. f ∘ id_A = f"
      proof_obligation: "Verify for all morphisms"
    associativity:
      statement: "∀ f: A → B, g: B → C, h: C → D. (h ∘ g) ∘ f = h ∘ (g ∘ f)"
      proof_obligation: "Verify for all composable triples"
```

## Manifest Item Schema

Each category in the manifest:

```yaml
category_item:
  id: "category.{Name}"
  name: "{Name}"
  kind: "category"
  traces:
    - ref: "level-1.entity.{Entity}"
      role: "object"
    - ref: "level-2.morphism.{module}.{op}"
      role: "morphism"
    - ref: "level-2.morphism.identity.{Entity}"
      role: "identity"
  definition:
    objects:
      count: N
      items: ["Entity1", "Entity2", ...]
    morphisms:
      count: M
      items: ["op1", "op2", ...]
    identities:
      count: N  # Same as objects
    composition_pairs:
      # List of valid (f, g) where g ∘ f is defined
      - {f: "op1", g: "op2", result: "op1_then_op2"}
  laws:
    identity_left: {verified: true, proof_ref: "..."}
    identity_right: {verified: true, proof_ref: "..."}
    associativity: {verified: true, proof_ref: "..."}
  status: "pending|defined|laws_verified"
```

## Derived Categories

Target categories derived from Domain:

```yaml
derived_categories:
  Storage:
    derive_from: "Domain"
    object_transformation: "Entity → Model (database table)"
    morphism_transformation: "Operation → SQL query"
    additional_morphisms:
      - "to_model: Entity → Model"
      - "from_model: Model → Entity"
      
  HTTP:
    derive_from: "Domain"
    object_transformation: "Entity → (Request, Response) DTOs"
    morphism_transformation: "Operation → Handler"
    additional_morphisms:
      - "to_dto: Entity → ResponseDTO"
      - "from_dto: RequestDTO → EntityData"
      
  External:
    derive_from: "Domain"
    object_transformation: "Entity → ExternalDTO"
    morphism_transformation: "Operation → API call"
    additional_morphisms:
      - "to_external: Entity → ExternalRequest"
      - "from_external: ExternalResponse → Entity"
```

## Validation Rules

```yaml
validation:
  # Category validations
  objects_defined:
    rule: "∀ category: objects ≠ ∅"
    description: "Every category has at least one object"
    
  identities_exist:
    rule: "∀ object ∈ category: ∃ id_object"
    description: "Every object has an identity morphism"
    critical: true
    
  composition_closed:
    rule: "∀ f: A → B, g: B → C ∈ category: g ∘ f ∈ category"
    description: "Composition stays within category"
    critical: true
    
  category_laws_hold:
    rule: "Identity and associativity laws verified"
    description: "Category laws must hold"
    critical: true
    
  domain_complete:
    rule: "Domain category contains all Level 1 entities and Level 2 morphisms"
    description: "Domain category is comprehensive"
    critical: true
    
  # Monad validations
  monad_laws_hold:
    rule: "Left identity, right identity, associativity for each monad"
    description: "Monad laws must hold"
    critical: true
    
  kleisli_laws_hold:
    rule: "Kleisli composition laws (equivalent to monad laws)"
    description: "Kleisli category laws must hold"
    critical: true
    
  morphism_classification:
    rule: "∀ morphism ∈ Level2: assigned to exactly one category"
    description: "Every morphism belongs to Domain or a Kleisli category"
    critical: true
    
  effect_consistency:
    rule: "Morphism effects match its Kleisli category's monad"
    description: "Effect types are consistent"
    critical: true
```

## Output Structure

```
level-4.manifest.yaml
generated/{language}/src/{project}/
├── categories/
│   ├── domain.{ext}           # Domain category definition
│   ├── storage.{ext}          # Storage category definition
│   ├── http.{ext}             # HTTP category definition
│   └── external.{ext}         # External category definition
├── monads/
│   ├── io.{ext}               # IO monad
│   ├── result.{ext}           # Either/Result monad
│   ├── reader.{ext}           # Reader monad
│   ├── app.{ext}              # App monad (stacked)
│   └── kleisli.{ext}          # Kleisli composition helpers
└── laws/
    ├── identity.{ext}         # Identity law statements
    ├── composition.{ext}      # Composition law statements
    └── monad_laws.{ext}       # Monad law statements
```

## Invariant

```
Domain.objects = Level 1 entities (all)
Domain.morphisms = Level 2 morphisms (all)
Domain.identities = Level 2 identities (all)

∀ category: laws.verified = true

Violation is FATAL. Pipeline MUST NOT proceed to Level 5.
```

## Example (Illustrative Only)

Given 3 entities and 10 morphisms from Levels 1-2, where most morphisms have effects:

```yaml
# level-4.manifest.yaml
items:
  # ═══════════════════════════════════════════════════════════
  # MONADS
  # ═══════════════════════════════════════════════════════════
  
  - id: "monad.IO"
    kind: "monad"
    traces:
      - ref: "level-0.effect.IO"
        role: "effect"
    definition:
      type_constructor: "IO[A]"
      pure:
        signature: "A → IO[A]"
        implementation: "IO.pure"
      bind:
        signature: "IO[A] → (A → IO[B]) → IO[B]"
        implementation: "io.flatMap(f)"
    laws:
      left_identity:
        statement: "IO.pure(a).flatMap(f) ≡ f(a)"
        proof_obligation: "level-8.proof.monad.IO.left_id"
      right_identity:
        statement: "io.flatMap(IO.pure) ≡ io"
        proof_obligation: "level-8.proof.monad.IO.right_id"
      associativity:
        statement: "io.flatMap(f).flatMap(g) ≡ io.flatMap(a => f(a).flatMap(g))"
        proof_obligation: "level-8.proof.monad.IO.assoc"
        
  - id: "monad.Result"
    kind: "monad"
    traces:
      - ref: "level-0.effect.Either"
        role: "effect"
    definition:
      type_constructor: "Either[Error, A]"
      pure:
        signature: "A → Either[Error, A]"
        implementation: "Right"
      bind:
        signature: "Either[Error, A] → (A → Either[Error, B]) → Either[Error, B]"
        implementation: "either.flatMap(f) // short-circuits on Left"
    laws:
      left_identity:
        proof_obligation: "level-8.proof.monad.Result.left_id"
      right_identity:
        proof_obligation: "level-8.proof.monad.Result.right_id"
      associativity:
        proof_obligation: "level-8.proof.monad.Result.assoc"
        
  - id: "monad.App"
    kind: "monad"
    subkind: "transformer_stack"
    traces:
      - ref: "monad.IO"
        role: "base"
      - ref: "monad.Result"
        role: "layer"
    definition:
      stack:
        - {monad: "IO"}
        - {transformer: "EitherT", param: "Error"}
      expanded: "IO[Either[Error, A]]"
      pure:
        signature: "A → IO[Either[Error, A]]"
        implementation: "a => IO.pure(Right(a))"
      bind:
        implementation: |
          app.flatMap { 
            case Right(a) => f(a)
            case Left(e) => IO.pure(Left(e))
          }
    note: "This is where most service morphisms live"
        
  # ═══════════════════════════════════════════════════════════
  # CATEGORIES
  # ═══════════════════════════════════════════════════════════
  
  - id: "category.Domain"
    kind: "category"
    description: "Pure domain - no effects"
    traces:
      - ref: "level-1.entity.Customer"
        role: "object"
      - ref: "level-1.entity.Order"
        role: "object"
      - ref: "level-1.entity.Product"
        role: "object"
      - ref: "level-2.morphism.identity.Customer"
        role: "identity"
      - ref: "level-2.morphism.identity.Order"
        role: "identity"
      - ref: "level-2.morphism.identity.Product"
        role: "identity"
    definition:
      objects:
        count: 3
        items: ["Customer", "Order", "Product"]
      morphisms:
        count: 0  # Most morphisms have effects, so they're in Kleisli_App
        items: []
        note: "Pure domain morphisms only (validation, etc.)"
      identities:
        count: 3
        items: ["id_Customer", "id_Order", "id_Product"]
    laws:
      identity_left:
        proof_obligation: "level-8.proof.category.Domain.identity_left"
      identity_right:
        proof_obligation: "level-8.proof.category.Domain.identity_right"
      associativity:
        proof_obligation: "level-8.proof.category.Domain.associativity"
        
  # ═══════════════════════════════════════════════════════════
  # KLEISLI CATEGORIES
  # ═══════════════════════════════════════════════════════════
  
  - id: "kleisli.App"
    kind: "kleisli_category"
    description: "WHERE MOST SERVICE MORPHISMS LIVE"
    traces:
      - ref: "monad.App"
        role: "monad"
      - ref: "level-2.morphism.customers.create_customer"
        role: "morphism"
      - ref: "level-2.morphism.customers.get_customer"
        role: "morphism"
      - ref: "level-2.morphism.customers.update_customer"
        role: "morphism"
      - ref: "level-2.morphism.orders.place_order"
        role: "morphism"
      - ref: "level-2.morphism.orders.get_order"
        role: "morphism"
      # ... all effectful morphisms
    definition:
      monad: "App"
      objects:
        count: 3
        items: ["Customer", "Order", "Product"]
      morphisms:
        type: "A → App[B]"
        count: 10
        items:
          - "create_customer: CreateCustomerDTO → App[Customer]"
          - "get_customer: CustomerId → App[Customer]"
          - "update_customer: (CustomerId, UpdateDTO) → App[Customer]"
          - "place_order: PlaceOrderDTO → App[Order]"
          - "get_order: OrderId → App[Order]"
          # ...
      identity:
        is: "App.pure: A → App[A]"
      composition:
        operator: "(>=>)"
        example: "get_customer >=> validate >=> update"
        definition: "f >=> g = λa. f(a).flatMap(g)"
    laws:
      left_identity:
        statement: "App.pure >=> f  ≡  f"
        proof_obligation: "level-8.proof.kleisli.App.left_id"
      right_identity:
        statement: "f >=> App.pure  ≡  f"
        proof_obligation: "level-8.proof.kleisli.App.right_id"
      associativity:
        statement: "(f >=> g) >=> h  ≡  f >=> (g >=> h)"
        proof_obligation: "level-8.proof.kleisli.App.assoc"
        
  - id: "category.Storage"
    kind: "category"
    traces:
      - ref: "category.Domain"
        role: "source"
    definition:
      objects:
        count: 3
        items: ["CustomerModel", "OrderModel", "ProductModel"]
        derived_from: "Domain objects"
      note: "Operations live in Kleisli_IO"
      
  - id: "category.HTTP"
    kind: "category"
    traces:
      - ref: "category.Domain"
        role: "source"
    definition:
      objects:
        count: 6
        items: ["CustomerRequest", "CustomerResponse", ...]
        derived_from: "Domain objects"
      note: "Handlers live in Kleisli_App"

counts:
  total: 7
  by_kind:
    monad: 3
    category: 3
    kleisli_category: 1
    
validation:
  all_monads_defined: true
  all_laws_stated: true
  morphisms_classified: true
  complete: true
```

## Law Proof Obligations

Each structure generates proof obligations for Level 8:

```yaml
proof_obligations:
  # Category laws
  - id: "proof.category.{Cat}.identity_left"
    statement: "∀ f: A → B ∈ {Cat}. id_B ∘ f = f"
    
  - id: "proof.category.{Cat}.identity_right"
    statement: "∀ f: A → B ∈ {Cat}. f ∘ id_A = f"
    
  - id: "proof.category.{Cat}.associativity"
    statement: "∀ composable (f, g, h) ∈ {Cat}. (h ∘ g) ∘ f = h ∘ (g ∘ f)"
    
  # Monad laws
  - id: "proof.monad.{M}.left_identity"
    statement: "∀ a, f. pure(a) >>= f  ≡  f(a)"
    
  - id: "proof.monad.{M}.right_identity"
    statement: "∀ m. m >>= pure  ≡  m"
    
  - id: "proof.monad.{M}.associativity"
    statement: "∀ m, f, g. (m >>= f) >>= g  ≡  m >>= (λx. f(x) >>= g)"
    
  # Kleisli laws (equivalent to monad laws)
  - id: "proof.kleisli.{M}.left_identity"
    statement: "∀ f: A → M[B]. pure >=> f  ≡  f"
    
  - id: "proof.kleisli.{M}.right_identity"
    statement: "∀ f: A → M[B]. f >=> pure  ≡  f"
    
  - id: "proof.kleisli.{M}.associativity"
    statement: "∀ f, g, h. (f >=> g) >=> h  ≡  f >=> (g >=> h)"
    note: "This is what guarantees service composition is associative"
```

These obligations MUST be discharged in Level 8 (Proofs).

## Invariant

```
# Categories
Domain.objects = Level 1 entities (all)
Domain.identities = Level 2 identities (all)

# Morphism classification
∀ morphism ∈ Level 2:
  (effects = [] → morphism ∈ Domain) ∧
  (effects ≠ [] → morphism ∈ Kleisli[effects])

# Monad completeness
∀ effect ∈ Level 0.effects:
  ∃ monad ∈ Level 4: monad.type = effect

# Kleisli completeness  
∀ monad ∈ Level 4.monads:
  ∃ kleisli ∈ Level 4.categories: kleisli.monad = monad

# Laws
∀ category: category_laws.stated = true
∀ monad: monad_laws.stated = true
∀ kleisli: kleisli_laws.stated = true

Violation is FATAL. Pipeline MUST NOT proceed to Level 5.
```

## Code Generation Implications

The monad structure directly impacts code generation in Level 9:

```python
# Without monad awareness (wrong):
def get_then_update(id: CustomerId) -> Customer:
    customer = get_customer(id)  # Returns App[Customer], not Customer!
    return update_customer(customer)  # Type error

# With monad awareness (correct):
async def get_then_update(id: CustomerId) -> Result[Error, Customer]:
    # Using Kleisli composition (>=>)
    return await (get_customer >=> update_customer)(id)
    
    # Or explicit bind:
    customer_result = await get_customer(id)
    match customer_result:
        case Ok(customer):
            return await update_customer(customer)
        case Err(e):
            return Err(e)
```

This is why Level 4 monad definitions are critical - they determine how Level 3 module compositions actually work.
