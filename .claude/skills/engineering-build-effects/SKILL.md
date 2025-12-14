---
name: build-effects
description: |
  Build the effect algebra (monad stack). Formalizes unit, bind, and monad
  laws for the application's effect system. Use when: formalizing effect
  handling, building monad transformers, preparing effect proofs.
---

# Build Effects

Formalize the monad stack for effectful morphisms.

## Categorical Foundation

A monad M on category C consists of:
- **Endofunctor**: M : C → C
- **Unit (return)**: η : Id → M
- **Multiplication (join)**: μ : M∘M → M

Equivalently (Kleisli):
- **Return**: A → M[A]
- **Bind**: M[A] → (A → M[B]) → M[B]

## Input

- `artifacts/v{N}/spec/effects.yaml`
- `artifacts/v{N}/build/category.yaml`

## Output

`artifacts/v{N}/build/effects.yaml`

## Process

1. **Identify effect stack** from spec/effects.yaml
2. **Order effects** (outer to inner)
3. **Define unit and bind** for each effect
4. **Define composed monad** (App)
5. **State monad laws**

## Monad Stack Architecture

Most applications use a stacked monad:

```
App[A] = Reader[Env, IO[Either[AppError, A]]]

Stack (outer → inner):
  Reader[Env, _]    -- Environment/dependency injection
  IO[_]             -- Side effects (DB, network)
  Either[Error, _]  -- Error handling
```

This can be built with monad transformers:

```
App = ReaderT[Env, EitherT[AppError, IO, _], _]
```

Or more practically, as an opaque type with custom operations.

## Effect Layer Definitions

### IO Layer

```yaml
- effect: "IO"
  position: 2  # Middle of stack
  description: "Side-effectful computation"
  
  functor:
    map:
      signature: "(A → B) → IO[A] → IO[B]"
      implementation: "λf. λma. ma.map(f)"
      
  unit:
    signature: "A → IO[A]"
    implementation: "λa. IO.pure(a)"
    
  bind:
    signature: "IO[A] → (A → IO[B]) → IO[B]"
    implementation: "λma. λf. ma.flatMap(f)"
```

### Either Layer

```yaml
- effect: "Either[E, _]"
  position: 3  # Inner
  description: "Computation that may fail"
  
  functor:
    map:
      signature: "(A → B) → Either[E, A] → Either[E, B]"
      implementation: "λf. λea. ea.map(f)"
      
  unit:
    signature: "A → Either[E, A]"
    implementation: "λa. Right(a)"
    
  bind:
    signature: "Either[E, A] → (A → Either[E, B]) → Either[E, B]"
    implementation: "λea. λf. ea.flatMap(f)"
```

### Reader Layer

```yaml
- effect: "Reader[R, _]"
  position: 1  # Outer
  description: "Computation reading from environment"
  
  functor:
    map:
      signature: "(A → B) → Reader[R, A] → Reader[R, B]"
      implementation: "λf. λra. Reader(λr. f(ra.run(r)))"
      
  unit:
    signature: "A → Reader[R, A]"
    implementation: "λa. Reader(λr. a)"
    
  bind:
    signature: "Reader[R, A] → (A → Reader[R, B]) → Reader[R, B]"
    implementation: "λra. λf. Reader(λr. f(ra.run(r)).run(r))"
    
  ask:
    signature: "Reader[R, R]"
    implementation: "Reader(λr. r)"
    description: "Get the environment"
```

## Output Format

```yaml
version: "1.0"

monad_stack:
  name: "App"
  description: "Application effect monad"
  full_type: "Reader[Env, IO[Either[AppError, A]]]"
  
  # ========================================
  # Stack Layers (outer to inner)
  # ========================================
  layers:
    - effect: "Reader[Env, _]"
      position: 1
      description: "Environment access (config, dependencies)"
      
      functor:
        map:
          signature: "(A → B) → Reader[Env, A] → Reader[Env, B]"
          
      unit:
        signature: "A → Reader[Env, A]"
        implementation: "λa. Reader(λenv. a)"
        
      bind:
        signature: "Reader[Env, A] → (A → Reader[Env, B]) → Reader[Env, B]"
        implementation: "λra. λf. Reader(λenv. f(ra.run(env)).run(env))"
        
      operations:
        - name: "ask"
          signature: "Reader[Env, Env]"
          description: "Get the environment"
        - name: "asks"
          signature: "(Env → A) → Reader[Env, A]"
          description: "Get a projection of the environment"
          
    - effect: "IO"
      position: 2
      description: "Side effects (database, network, file system)"
      
      functor:
        map:
          signature: "(A → B) → IO[A] → IO[B]"
          
      unit:
        signature: "A → IO[A]"
        implementation: "async λa. a"
        
      bind:
        signature: "IO[A] → (A → IO[B]) → IO[B]"
        implementation: "async λma. λf. await ma |> f |> await"
        
    - effect: "Either[AppError, _]"
      position: 3
      description: "Error handling"
      
      functor:
        map:
          signature: "(A → B) → Either[AppError, A] → Either[AppError, B]"
          
      unit:
        signature: "A → Either[AppError, A]"
        implementation: "λa. Right(a)"
        
      bind:
        signature: "Either[AppError, A] → (A → Either[AppError, B]) → Either[AppError, B]"
        implementation: |
          λea. λf. match ea:
            Left(e) → Left(e)
            Right(a) → f(a)
            
      operations:
        - name: "raise"
          signature: "AppError → Either[AppError, A]"
          description: "Raise an error"
        - name: "catch"
          signature: "Either[AppError, A] → (AppError → Either[AppError, A]) → Either[AppError, A]"
          description: "Handle an error"
          
  # ========================================
  # Composed Monad
  # ========================================
  composed:
    description: "Combined App monad operations"
    
    unit:
      signature: "A → App[A]"
      implementation: |
        λa. Reader(λenv. 
          IO.pure(Right(a))
        )
        
    bind:
      signature: "App[A] → (A → App[B]) → App[B]"
      implementation: |
        λma. λf. Reader(λenv.
          IO.flatMap(ma.run(env), λea.
            match ea:
              Left(e) → IO.pure(Left(e))
              Right(a) → f(a).run(env)
          )
        )
        
    map:
      signature: "(A → B) → App[A] → App[B]"
      implementation: "λf. λma. ma.bind(λa. unit(f(a)))"
      
    # Lifting from inner monads
    lift:
      from_io:
        signature: "IO[A] → App[A]"
        implementation: "λio. Reader(λenv. io.map(Right))"
        
      from_either:
        signature: "Either[AppError, A] → App[A]"
        implementation: "λea. Reader(λenv. IO.pure(ea))"
        
      from_reader:
        signature: "Reader[Env, A] → App[A]"
        implementation: "λra. Reader(λenv. IO.pure(Right(ra.run(env))))"
        
    # Error handling
    raise:
      signature: "AppError → App[A]"
      implementation: "λe. Reader(λenv. IO.pure(Left(e)))"
      
    catch:
      signature: "App[A] → (AppError → App[A]) → App[A]"
      implementation: |
        λma. λhandler. Reader(λenv.
          IO.flatMap(ma.run(env), λea.
            match ea:
              Left(e) → handler(e).run(env)
              Right(a) → IO.pure(Right(a))
          )
        )
        
    # Environment access
    ask:
      signature: "App[Env]"
      implementation: "Reader(λenv. IO.pure(Right(env)))"
      
    asks:
      signature: "(Env → A) → App[A]"
      implementation: "λf. Reader(λenv. IO.pure(Right(f(env))))"
      
    # Running
    run:
      signature: "App[A] → Env → IO[Either[AppError, A]]"
      implementation: "λma. λenv. ma.run(env)"
      
  # ========================================
  # Monad Laws
  # ========================================
  laws:
    left_identity:
      statement: "unit(a).bind(f) = f(a)"
      formal: "∀ a: A, f: A → App[B]. unit(a) >>= f ≡ f(a)"
      status: stated
      
    right_identity:
      statement: "m.bind(unit) = m"
      formal: "∀ m: App[A]. m >>= unit ≡ m"
      status: stated
      
    associativity:
      statement: "(m.bind(f)).bind(g) = m.bind(λx. f(x).bind(g))"
      formal: "∀ m: App[A], f: A → App[B], g: B → App[C]. (m >>= f) >>= g ≡ m >>= (λx. f(x) >>= g)"
      status: stated
      
  # ========================================
  # Error Type
  # ========================================
  error_type:
    id: "AppError"
    description: "Unified application error type"
    variants:
      - name: "Validation"
        payload: "ValidationError"
      - name: "User"
        payload: "UserError"
      - name: "Email"
        payload: "EmailError"
      - name: "Order"
        payload: "OrderError"
      # From spec/effects.yaml error_types
      
  # ========================================
  # Environment Type
  # ========================================
  environment_type:
    id: "Env"
    description: "Application environment"
    note: "Concrete fields defined by gen phase based on targets"

# ========================================
# Kleisli Category
# ========================================
kleisli_category:
  name: "Kleisli[App]"
  description: "Category of Kleisli arrows for App monad"
  
  objects: "Same as Domain category objects"
  
  morphisms:
    description: "Kleisli arrows A → App[B]"
    from_pure: "f: A → B becomes λa. unit(f(a))"
    
  identity:
    signature: "A → App[A]"
    implementation: "unit"
    
  composition:
    signature: "(A → App[B]) → (B → App[C]) → (A → App[C])"
    implementation: "λf. λg. λa. f(a).bind(g)"
    notation: "f >=> g"
    
  laws:
    - "unit >=> f = f"
    - "f >=> unit = f"
    - "(f >=> g) >=> h = f >=> (g >=> h)"
```

## Monad Transformer Laws

If using transformers explicitly:

```yaml
transformer_laws:
  lift_return:
    statement: "lift(return(a)) = return(a)"
    
  lift_bind:
    statement: "lift(m >>= f) = lift(m) >>= (lift ∘ f)"
```

## Validation Rules

1. **All effects covered**: Every effect from spec has layer definition
2. **Order consistent**: Position numbers form valid sequence
3. **Laws stated**: All monad laws listed
4. **Unit and bind defined**: For each layer and composed
5. **Error type complete**: Covers all domain errors

## Validation Checklist

- [ ] All effects from spec/effects.yaml have layer
- [ ] Layer positions are sequential (1, 2, 3, ...)
- [ ] Composed monad has unit, bind, map
- [ ] Monad laws stated with status: stated
- [ ] Lifting operations defined
- [ ] Error and environment types referenced

## Do NOT

- **Skip any effect** — All must be formalized
- **Assume laws proven** — Status starts as "stated"
- **Define concrete Env fields** — That's gen phase
- **Implement in target language** — Just signatures and abstract impl
