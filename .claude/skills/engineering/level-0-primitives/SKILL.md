---
name: level-0-primitives
description: |
  Level 0: Primitives. The TYPE SIGNATURE for the entire system.
  
  NOT A CATEGORY. Level 0 provides the raw type/effect language that
  Levels 1-3 use to build entity and morphism signatures. Categories
  with laws come at Level 4.
  
  This is a signature in the sense of type theory:
  - Base types (ground types)
  - Type functors (type → type)
  - Monad symbols (effect constructors, laws come at L4)
  - Refinements (constrained types)
  - Identifier schema (pattern for entity IDs)
  
  Input: specifications
  Output: level-0.manifest.yaml + primitive definitions
  
  UNIVERSAL: Works for any domain. No domain-specific content.
---

# Level 0: Primitives (Type Signature)

The foundational TYPE SIGNATURE for the system. Not yet a category.

## Principle

Level 0 defines the raw syntactic material:

```
Signature Σ:
  BaseTypes:     Bool, String, Int, Float, DateTime, UUID, ...
  TypeFunctors:  Option[_], List[_], Set[_], Map[_,_], ...
  MonadSymbols:  IO[_], Either[E,_], Reader[R,_], State[S,_], ...
  Refinements:   Email <: String, Money <: Decimal, ...
  IdSchema:      {Entity}Id := NewType(UUID) for each entity
```

**Critical distinction:**
- Level 0: SYNTAX only (type constructors, monad symbols)
- Level 4: SEMANTICS (category structure, monad laws, Kleisli)

## Kind Classification

Every Level 0 item has a `kind` that determines its categorical role:

```yaml
kinds:
  base_type:
    description: "Ground type with no type parameters"
    examples: ["Bool", "String", "Int", "DateTime", "UUID"]
    role: "Objects in the base Type category"
    categorical_note: "Terminal objects in type formation"
    
  type_functor:
    description: "Type constructor: Type → Type (or Type² → Type)"
    examples: ["Option[_]", "List[_]", "Set[_]", "Map[_,_]"]
    role: "Endofunctors on Type category"
    categorical_note: "Functor laws stated at L4, proven at L8"
    parameters:
      arity: "1 or 2"
      variance: "covariant | contravariant | invariant"
    
  monad_symbol:
    description: "Effect constructor - monad structure declared at L4"
    examples: ["IO[_]", "Either[E,_]", "Reader[R,_]", "State[S,_]"]
    role: "Syntax for effectful types"
    categorical_note: |
      At L0: just a type constructor (syntax)
      At L4: gets unit/bind/laws (semantics)
      At L8: laws proven in Lean
    
  refinement:
    description: "Constrained subtype via predicate"
    examples: ["Email", "Money", "PositiveInt", "NonEmptyString"]
    role: "Subobject in type category"
    categorical_note: "Subobject classifier; proof obligations at L8"
    structure:
      base: "The unrestricted type"
      predicate: "Condition that must hold"
      smart_constructor: "Validated construction"
      
  id_schema:
    description: "Pattern for generating entity identifiers"
    template: "{Entity}Id := NewType(UUID)"
    role: "Instantiated by L1 entities"
    categorical_note: |
      This is a SCHEMA, not concrete types.
      Concrete {Entity}Id types are generated when L1 entities are defined.
      E.g., if L1 defines Customer, then CustomerId is instantiated.
```

## Items by Kind

### Base Types

```yaml
base_types:
  # Boolean
  - id: "type.Bool"
    kind: "base_type"
    description: "True or False"
    mappings:
      python: "bool"
      typescript: "boolean"
      go: "bool"
      lean: "Bool"
      
  # Textual  
  - id: "type.String"
    kind: "base_type"
    description: "UTF-8 text of arbitrary length"
    mappings:
      python: "str"
      typescript: "string"
      go: "string"
      lean: "String"
      
  - id: "type.Char"
    kind: "base_type"
    description: "Single Unicode code point"
    mappings:
      python: "str"  # length 1
      typescript: "string"
      go: "rune"
      lean: "Char"
      
  # Numeric - Integers
  - id: "type.Int"
    kind: "base_type"
    description: "Arbitrary precision integer"
    mappings:
      python: "int"
      typescript: "number"
      go: "int64"
      lean: "Int"
      
  - id: "type.Nat"
    kind: "base_type"
    description: "Natural number (0, 1, 2, ...)"
    mappings:
      python: "int"  # with runtime >= 0 check
      typescript: "number"
      go: "uint64"
      lean: "Nat"
      
  # Numeric - Floating point
  - id: "type.Float"
    kind: "base_type"
    description: "IEEE 754 double precision"
    mappings:
      python: "float"
      typescript: "number"
      go: "float64"
      lean: "Float"
      
  - id: "type.Decimal"
    kind: "base_type"
    description: "Arbitrary precision decimal (for money)"
    mappings:
      python: "decimal.Decimal"
      typescript: "Decimal"  # decimal.js
      go: "shopspring/decimal.Decimal"
      lean: "Rat"
      
  # Temporal
  - id: "type.DateTime"
    kind: "base_type"
    description: "UTC timestamp with timezone"
    mappings:
      python: "datetime.datetime"
      typescript: "Date"
      go: "time.Time"
      lean: "Nat"  # Unix timestamp
      
  - id: "type.Date"
    kind: "base_type"
    description: "Calendar date without time"
    mappings:
      python: "datetime.date"
      typescript: "Date"
      go: "time.Time"
      lean: "Nat × Nat × Nat"
      
  - id: "type.Duration"
    kind: "base_type"
    description: "Time interval"
    mappings:
      python: "datetime.timedelta"
      typescript: "number"  # milliseconds
      go: "time.Duration"
      lean: "Nat"
      
  # Identity
  - id: "type.UUID"
    kind: "base_type"
    description: "Universally unique identifier (v4)"
    mappings:
      python: "uuid.UUID"
      typescript: "string"
      go: "uuid.UUID"
      lean: "String"
      
  # Binary
  - id: "type.Bytes"
    kind: "base_type"
    description: "Raw byte sequence"
    mappings:
      python: "bytes"
      typescript: "Uint8Array"
      go: "[]byte"
      lean: "ByteArray"
      
  # Structured
  - id: "type.Json"
    kind: "base_type"
    description: "Arbitrary JSON value"
    mappings:
      python: "dict[str, Any]"
      typescript: "Record<string, unknown>"
      go: "map[string]interface{}"
      lean: "Json"
      
  # Unit
  - id: "type.Unit"
    kind: "base_type"
    description: "Single value type (void)"
    mappings:
      python: "None"
      typescript: "void"
      go: "struct{}"
      lean: "Unit"
```

### Type Functors

```yaml
type_functors:
  - id: "functor.Option"
    kind: "type_functor"
    arity: 1
    variance: "covariant"
    signature: "Type → Type"
    description: "Optional value: None | Some(A)"
    mappings:
      python: "A | None"
      typescript: "A | null"
      go: "*A"
      lean: "Option A"
    note: "Functor and Monad instance declared at L4"
    
  - id: "functor.List"
    kind: "type_functor"
    arity: 1
    variance: "covariant"
    signature: "Type → Type"
    description: "Ordered collection"
    mappings:
      python: "list[A]"
      typescript: "A[]"
      go: "[]A"
      lean: "List A"
      
  - id: "functor.NonEmptyList"
    kind: "type_functor"
    arity: 1
    variance: "covariant"
    signature: "Type → Type"
    description: "List with at least one element"
    mappings:
      python: "NonEmptyList[A]"  # custom
      typescript: "[A, ...A[]]"
      go: "[]A"  # with runtime check
      lean: "List A"  # with proof of non-empty
      
  - id: "functor.Set"
    kind: "type_functor"
    arity: 1
    variance: "covariant"
    signature: "Type → Type"
    description: "Unordered unique collection"
    constraint: "A requires Eq"
    mappings:
      python: "set[A]"
      typescript: "Set<A>"
      go: "map[A]struct{}"
      lean: "Finset A"
      
  - id: "functor.Map"
    kind: "type_functor"
    arity: 2
    variance: ["invariant", "covariant"]  # K invariant, V covariant
    signature: "Type × Type → Type"
    description: "Key-value mapping"
    constraint: "K requires Eq, Hash"
    mappings:
      python: "dict[K, V]"
      typescript: "Map<K, V>"
      go: "map[K]V"
      lean: "K → Option V"
      
  - id: "functor.Tuple2"
    kind: "type_functor"
    arity: 2
    variance: ["covariant", "covariant"]
    signature: "Type × Type → Type"
    description: "Pair of values"
    mappings:
      python: "tuple[A, B]"
      typescript: "[A, B]"
      go: "struct{A; B}"
      lean: "A × B"
```

### Monad Symbols

```yaml
monad_symbols:
  # ═══════════════════════════════════════════════════════════
  # CRITICAL: These are SYNTAX only at L0.
  # Monad laws (unit, bind, associativity) are DECLARED at L4.
  # Proofs of laws are at L8.
  # ═══════════════════════════════════════════════════════════
  
  - id: "monad.IO"
    kind: "monad_symbol"
    signature: "Type → Type"
    description: "Deferred side effect producing A"
    semantics_at: "level-4"
    mappings:
      python: "Coroutine[Any, Any, A]"  # async
      typescript: "Promise<A>"
      go: "func() (A, error)"
      lean: "IO A"
    use_cases: ["Database", "Network", "FileSystem", "Logging"]
    note: "At L0, just syntax. At L4, declared as monad with laws."
    
  - id: "monad.Either"
    kind: "monad_symbol"
    signature: "Type × Type → Type"
    description: "Either[E, A] = Left(E) | Right(A)"
    semantics_at: "level-4"
    mappings:
      python: "Result[E, A]"
      typescript: "Either<E, A>"
      go: "(A, error)"
      lean: "Except E A"
    use_cases: ["Error handling", "Validation", "Parsing"]
    
  - id: "monad.Reader"
    kind: "monad_symbol"
    signature: "Type × Type → Type"
    description: "Reader[R, A] = R → A"
    semantics_at: "level-4"
    mappings:
      python: "Callable[[R], A]"
      typescript: "(r: R) => A"
      go: "func(R) A"
      lean: "ReaderT R Id A"
    use_cases: ["Dependency injection", "Configuration"]
    
  - id: "monad.State"
    kind: "monad_symbol"
    signature: "Type × Type → Type"
    description: "State[S, A] = S → (A, S)"
    semantics_at: "level-4"
    mappings:
      python: "Callable[[S], tuple[A, S]]"
      typescript: "(s: S) => [A, S]"
      go: "func(S) (A, S)"
      lean: "StateT S Id A"
    use_cases: ["Stateful computation", "Accumulators"]
    
  - id: "monad.IOEither"
    kind: "monad_symbol"
    signature: "Type × Type → Type"
    description: "IO[Either[E, A]] - the common App effect"
    semantics_at: "level-4"
    mappings:
      python: "async def f() -> Result[E, A]"
      typescript: "Promise<Either<E, A>>"
      go: "func() (A, error)"
      lean: "ExceptT E IO A"
    note: |
      At L0: just a composed type constructor
      At L4: declared as ExceptT E IO with monad transformer laws
      This becomes the "App" monad for most service operations
```

### Refinements

```yaml
refinements:
  # String refinements
  - id: "refinement.NonEmptyString"
    kind: "refinement"
    base: "String"
    predicate: "length > 0"
    smart_constructor: "NonEmptyString.from(s) → Option[NonEmptyString]"
    
  - id: "refinement.Email"
    kind: "refinement"
    base: "String"
    predicate: "matches RFC 5322 email format"
    smart_constructor: "Email.from(s) → Either[ValidationError, Email]"
    
  - id: "refinement.Url"
    kind: "refinement"
    base: "String"
    predicate: "valid URL per RFC 3986"
    smart_constructor: "Url.from(s) → Either[ValidationError, Url]"
    
  # Numeric refinements
  - id: "refinement.PositiveInt"
    kind: "refinement"
    base: "Int"
    predicate: "n > 0"
    smart_constructor: "PositiveInt.from(n) → Option[PositiveInt]"
    
  - id: "refinement.NonNegativeInt"
    kind: "refinement"
    base: "Int"
    predicate: "n >= 0"
    
  - id: "refinement.Percentage"
    kind: "refinement"
    base: "Decimal"
    predicate: "0 <= p <= 100"
    
  - id: "refinement.Money"
    kind: "refinement"
    base: "Decimal"
    predicate: "amount >= 0 ∧ scale <= 2"
    additional_fields:
      currency: "ISO 4217 code (optional)"
```

### Identifier Schema

```yaml
id_schema:
  # ═══════════════════════════════════════════════════════════
  # This is a PATTERN, not concrete types.
  # Concrete {Entity}Id types are generated at L1 based on entities.
  # ═══════════════════════════════════════════════════════════
  
  - id: "schema.EntityId"
    kind: "id_schema"
    template: "{Entity}Id"
    underlying: "UUID"
    description: |
      For each entity E defined at Level 1:
        Generate: {E}Id := NewType(UUID)
        
      Example:
        Level 1 entity "Customer" →
        Generates "CustomerId := NewType(UUID)"
        
    factory_template: "{entity}_id() → {Entity}Id"
    mappings:
      python: |
        {Entity}Id = NewType('{Entity}Id', UUID)
        def {entity}_id() -> {Entity}Id:
            return {Entity}Id(uuid4())
      typescript: |
        type {Entity}Id = string & { readonly __brand: '{Entity}Id' }
        const {entity}Id = (): {Entity}Id => uuidv4() as {Entity}Id
      go: |
        type {Entity}ID struct { uuid.UUID }
        func New{Entity}ID() {Entity}ID { return {Entity}ID{uuid.New()} }
      lean: |
        def {Entity}Id := String
        
    instantiation_note: |
      The manifest lists concrete IDs as they're created from L1 entities.
      E.g., if L1 has Customer, Order, Product entities,
      L0 manifest will include CustomerId, OrderId, ProductId items
      with kind: "identifier" (instances of this schema).
```

## Process

```yaml
process:
  step_1_define_base:
    action: "Include all base types (these are universal)"
    output: "Base type items in manifest"
    
  step_2_define_functors:
    action: "Include all type functors"
    output: "Type functor items in manifest"
    note: "These are syntax only; functor laws come at L4"
    
  step_3_define_monads:
    action: "Include monad symbols"
    output: "Monad symbol items in manifest"
    note: "These are syntax only; monad laws come at L4"
    
  step_4_define_refinements:
    action: "Extract refinements needed from specifications"
    output: "Refinement items in manifest"
    
  step_5_scan_entities:
    action: "Look ahead at L1 entities to generate identifiers"
    algorithm: |
      for entity in specifications.entities:
          add_identifier(f"{entity.name}Id", entity.name)
    output: "Identifier items (instances of id_schema)"
    
  step_6_generate_manifest:
    action: "Produce level-0.manifest.yaml"
    validation:
      - "All kinds are valid"
      - "All mappings defined"
      - "Identifier count matches entity count"
      
  step_7_generate_code:
    action: "Generate primitive definitions"
    output: "generated/{language}/src/{project}/primitives/"
```

## Output Structure

```
level-0.manifest.yaml
generated/{language}/src/{project}/primitives/
├── __init__.py           # Exports all primitives
├── types.py              # Base types
├── functors.py           # Type constructors  
├── effects.py            # Monad symbols (syntax only)
├── refinements.py        # Constrained types
├── identifiers.py        # Entity ID newtypes
└── result.py             # Result[E, A] implementation
```

## Validation Rules

```yaml
validation:
  kind_validity:
    rule: "∀ item: item.kind ∈ {base_type, type_functor, monad_symbol, refinement, identifier}"
    critical: true
    
  mapping_completeness:
    rule: "∀ item: all target languages have mappings"
    critical: true
    
  identifier_entity_match:
    rule: "|identifiers| = |Level 1 entities|"
    critical: true
    
  monad_semantics_deferred:
    rule: "∀ monad_symbol: no laws defined (laws at L4)"
    critical: true
    description: "L0 is syntax only"
```

## Manifest Schema

```yaml
# level-0.manifest.yaml

schema_version: "1.0"

level:
  number: 0
  name: "primitives"
  description: "Type signature - syntax for types and effects"

source:
  level: null  # No source - primitives are axiomatic
  manifest: null
  
items:
  # Base types
  - id: "type.Bool"
    name: "Bool"
    kind: "base_type"
    scope: "shared"  # All L0 items are shared
    traces: []  # Primitives don't trace
    definition:
      mappings:
        python: "bool"
        typescript: "boolean"
    status: "validated"
    
  # Type functors
  - id: "functor.Option"
    name: "Option"
    kind: "type_functor"
    scope: "shared"
    traces: []
    definition:
      arity: 1
      variance: "covariant"
      signature: "Type → Type"
      semantics_at: "level-4"  # Functor/Monad laws there
    status: "validated"
    
  # Monad symbols
  - id: "monad.IO"
    name: "IO"
    kind: "monad_symbol"
    scope: "shared"
    traces: []
    definition:
      signature: "Type → Type"
      semantics_at: "level-4"  # Monad laws there
    status: "validated"
    
  # Refinements
  - id: "refinement.Email"
    name: "Email"
    kind: "refinement"
    scope: "shared"
    traces: []
    definition:
      base: "type.String"
      predicate: "valid_email"
    status: "validated"
    
  # Identifiers (generated from L1 entity scan)
  - id: "identifier.CustomerId"
    name: "CustomerId"
    kind: "identifier"
    scope: "shared"
    traces: []
    definition:
      underlying: "type.UUID"
      for_entity: "Customer"
      instantiates: "schema.EntityId"
    status: "validated"
    
counts:
  total: 35  # Example
  by_kind:
    base_type: 15
    type_functor: 6
    monad_symbol: 5
    refinement: 6
    identifier: 3  # Matches L1 entity count

validation:
  complete: true
  all_mappings_valid: true
```

## Relation to Higher Levels

```
Level 0 (Type Signature)
    │
    │ SYNTAX: types, constructors, monad symbols
    ▼
Level 1 (Entities)
    │
    │ uses L0 types in field definitions
    ▼
Level 2 (Morphisms)
    │
    │ uses L0 effects SYNTACTICALLY in signatures
    │ e.g., "get: Id → IO[Either[Error, Entity]]"
    ▼
Level 3 (Modules)
    │
    ▼
Level 4 (Categories + Monads)
    │
    │ SEMANTICS: monad laws, Kleisli composition
    │ This is where IO, Either become REAL monads
    ▼
Level 8 (Proofs)
    │
    │ VERIFY: monad laws proven in Lean
```

**Key insight:** L0-L3 use monad symbols syntactically. L4 gives them categorical semantics. L8 proves the laws hold.
