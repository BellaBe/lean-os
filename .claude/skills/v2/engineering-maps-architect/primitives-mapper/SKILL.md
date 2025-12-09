---
name: primitives-mapper
description: |
  Map ADT types and primitives to language-agnostic representations. Produces type
  mappings, identifier mappings, and newtype wrappers. Foundation for all other mappers.
  Input: requirements.adt, standards/categories/domain.std.yaml
  Output: maps/primitives/*.map.yaml
---

# Primitives Mapper

Map algebraic data types to implementation representations.

## Purpose

Transform ADT definitions into mappable primitives:
1. Base type mappings (Int, String, Bool, etc.)
2. Product type mappings (records/structs)
3. Coproduct type mappings (unions/enums)
4. Identifier type mappings (typed IDs)
5. Newtype wrappers (domain primitives)

## Input

- `specifications/v{X}/requirements.adt` - ADT definitions
- `standards/categories/domain.std.yaml` - Domain category

## Output

```
maps/primitives/
├── types.map.yaml        # Base and composite type mappings
└── identifiers.map.yaml  # Identifier type mappings
```

## Type Mappings

### Schema

```yaml
# maps/primitives/types.map.yaml

primitives:
  # Base types
  base_types:
    - adt: Int
      abstract:
        representation: integer
        constraints: []
      targets:
        python:
          type: int
          import: null
        typescript:
          type: number
          import: null
        go:
          type: int64
          import: null
          
    - adt: String
      abstract:
        representation: string
        constraints: []
      targets:
        python:
          type: str
          import: null
        typescript:
          type: string
          import: null
        go:
          type: string
          import: null
          
    - adt: Bool
      abstract:
        representation: boolean
        constraints: []
      targets:
        python:
          type: bool
          import: null
        typescript:
          type: boolean
          import: null
        go:
          type: bool
          import: null
          
    - adt: Float
      abstract:
        representation: floating_point
        constraints: []
      targets:
        python:
          type: float
          import: null
        typescript:
          type: number
          import: null
        go:
          type: float64
          import: null
          
    - adt: DateTime
      abstract:
        representation: timestamp
        constraints: []
      targets:
        python:
          type: datetime
          import: "from datetime import datetime"
        typescript:
          type: Date
          import: null
        go:
          type: time.Time
          import: '"time"'
          
    - adt: UUID
      abstract:
        representation: uuid
        constraints: []
      targets:
        python:
          type: UUID
          import: "from uuid import UUID"
        typescript:
          type: string
          import: null
          validation: "uuid format"
        go:
          type: uuid.UUID
          import: '"github.com/google/uuid"'

  # Product types (records)
  product_types:
    pattern: |
      For ADT: A × B × C
      Abstract: record with fields a, b, c
      
    mapping_rule: |
      Each factor becomes a field
      Field name from ADT field name
      Field type from recursive type mapping
      
    example:
      adt: |
        Merchant = MerchantId × ShopDomain × SubscriptionTier × Settings
      abstract:
        kind: record
        fields:
          - name: id
            type: MerchantId
          - name: shop_domain
            type: ShopDomain
          - name: subscription
            type: SubscriptionTier
          - name: settings
            type: Settings
      targets:
        python:
          template: |
            @dataclass
            class {Name}:
                {fields}
          field_template: "{name}: {type}"
          
        typescript:
          template: |
            interface {Name} {
              {fields}
            }
          field_template: "{name}: {type};"
          
        go:
          template: |
            type {Name} struct {
              {fields}
            }
          field_template: "{Name} {type} `json:\"{json_name}\"`"

  # Coproduct types (unions/enums)
  coproduct_types:
    pattern: |
      For ADT: A + B + C
      Abstract: tagged union with variants A, B, C
      
    mapping_rule: |
      Each variant becomes a constructor/case
      Simple coproducts → enums
      Complex coproducts → discriminated unions
      
    example:
      adt: |
        SubscriptionTier = Free + Pro + Enterprise
      abstract:
        kind: enum
        variants:
          - Free
          - Pro
          - Enterprise
      targets:
        python:
          template: |
            class {Name}(Enum):
                {variants}
          variant_template: "{NAME} = \"{name}\""
          
        typescript:
          template: |
            type {Name} = {variants};
          variant_template: "\"{name}\""
          join: " | "
          
        go:
          template: |
            type {Name} string
            const (
              {variants}
            )
          variant_template: "{Name}{Variant} {Name} = \"{name}\""

  # Complex coproduct (discriminated union)
  discriminated_unions:
    example:
      adt: |
        Result[E, A] = Error(E) + Success(A)
      abstract:
        kind: discriminated_union
        discriminator: type
        variants:
          - tag: error
            payload: E
          - tag: success
            payload: A
      targets:
        python:
          template: |
            {Name} = Union[{variants}]
          uses: "typing.Union"
          alternative: |
            from result import Result, Ok, Err
            
        typescript:
          template: |
            type {Name}<E, A> = 
              | { type: 'error'; error: E }
              | { type: 'success'; value: A };
              
        go:
          template: |
            type {Name}[E, A any] struct {
              err *E
              val *A
            }
          note: "Go lacks sum types, use pointer fields"

  # Option/Maybe type
  option_type:
    adt: "Option[A] = None + Some(A)"
    abstract:
      kind: optional
      inner: A
    targets:
      python:
        type: "Optional[{A}]"
        import: "from typing import Optional"
        alternative: "Option[{A}]"  # from option library
      typescript:
        type: "{A} | null"
        alternative: "Option<{A}>"  # from fp-ts
      go:
        type: "*{A}"
        note: "Go uses pointer nil for optional"

  # List/Array type
  list_type:
    adt: "List[A]"
    abstract:
      kind: sequence
      element: A
    targets:
      python:
        type: "list[{A}]"
        import: null
      typescript:
        type: "{A}[]"
        alternative: "Array<{A}>"
      go:
        type: "[]{A}"
        import: null

  # Map/Dict type
  map_type:
    adt: "Map[K, V]"
    abstract:
      kind: mapping
      key: K
      value: V
    targets:
      python:
        type: "dict[{K}, {V}]"
        import: null
      typescript:
        type: "Record<{K}, {V}>"
        alternative: "Map<{K}, {V}>"
      go:
        type: "map[{K}]{V}"
        import: null
```

## Identifier Mappings

### Schema

```yaml
# maps/primitives/identifiers.map.yaml

identifiers:
  # Identifier pattern
  pattern: |
    Domain identifiers are newtypes wrapping base types
    Provides type safety: MerchantId ≠ ProfileId even if both are UUIDs
    
  # Newtype template
  newtype:
    abstract:
      kind: newtype
      wraps: base_type
      purpose: type_safety
      
    targets:
      python:
        template: |
          class {Name}(NewType('{Name}', {base})):
              """Type-safe identifier for {entity}."""
              pass
        alternative: |
          {Name} = NewType('{Name}', {base})
          
      typescript:
        template: |
          type {Name} = string & { readonly __brand: '{Name}' };
        factory: |
          function create{Name}(value: string): {Name} {
            return value as {Name};
          }
          
      go:
        template: |
          type {Name} {base}
        methods: |
          func (id {Name}) String() string {
            return string(id)
          }

  # Concrete identifier mappings
  mappings:
    - adt: MerchantId
      wraps: UUID
      targets:
        python:
          type: "NewType('MerchantId', UUID)"
        typescript:
          type: "string & { readonly __brand: 'MerchantId' }"
        go:
          type: "type MerchantId uuid.UUID"
          
    - adt: ProfileId
      wraps: UUID
      targets:
        python:
          type: "NewType('ProfileId', UUID)"
        typescript:
          type: "string & { readonly __brand: 'ProfileId' }"
        go:
          type: "type ProfileId uuid.UUID"
          
    - adt: AnalysisId
      wraps: UUID
      targets:
        python:
          type: "NewType('AnalysisId', UUID)"
        typescript:
          type: "string & { readonly __brand: 'AnalysisId' }"
        go:
          type: "type AnalysisId uuid.UUID"

  # Domain primitives (validated newtypes)
  domain_primitives:
    pattern: |
      Newtypes with validation constraints
      Construction may fail if validation fails
      
    example:
      adt: "Email = String { valid_email }"
      abstract:
        kind: validated_newtype
        wraps: String
        validation: email_format
      targets:
        python:
          template: |
            class {Name}(str):
                def __new__(cls, value: str) -> '{Name}':
                    if not cls._validate(value):
                        raise ValueError(f"Invalid {name}: {value}")
                    return super().__new__(cls, value)
                    
                @staticmethod
                def _validate(value: str) -> bool:
                    {validation}
                    
        typescript:
          template: |
            class {Name} {
              private constructor(private readonly value: string) {}
              
              static create(value: string): Either<ValidationError, {Name}> {
                if (!{Name}.validate(value)) {
                  return left(new ValidationError('{name}', value));
                }
                return right(new {Name}(value));
              }
              
              private static validate(value: string): boolean {
                {validation}
              }
            }
```

## Mapping Rules

```yaml
mapping_rules:
  # ADT to type resolution
  resolution:
    - pattern: "primitive type"
      action: "lookup in base_types"
      
    - pattern: "identifier type (*Id)"
      action: "lookup in identifiers"
      
    - pattern: "product type (×)"
      action: "map to record/struct"
      
    - pattern: "coproduct type (+)"
      action: "map to enum or union"
      
    - pattern: "parameterized type (A[B])"
      action: "map container with inner type"
      
    - pattern: "recursive type"
      action: "forward reference, lazy evaluation"

  # Naming conventions
  naming:
    python:
      types: PascalCase
      fields: snake_case
      constants: SCREAMING_SNAKE_CASE
      
    typescript:
      types: PascalCase
      fields: camelCase
      constants: SCREAMING_SNAKE_CASE
      
    go:
      types: PascalCase
      fields: PascalCase  # Exported
      private_fields: camelCase
```

## Validation

### Completeness Checks

```yaml
completeness:
  - all_adt_types_mapped
  - all_identifiers_mapped
  - all_domain_primitives_validated
  - all_targets_have_implementations
```

### Consistency Checks

```yaml
consistency:
  - type_names_unique
  - no_circular_type_references
  - all_references_resolve
  - target_types_valid
```

## Next Skills

Output feeds into:
- `kleisli-mapper`
- `adjunction-mapper`
- `functor-mapper`
- `transformation-mapper`
