---
name: type-synthesizer
description: Convert domain concepts into algebraic data types. Second skill in specification pipeline. Use after domain-extractor to transform entities and value objects into products, coproducts, and recursive types. Input is domain-concepts.yaml, output is requirements.adt. Produces type algebra that downstream skills use for morphism signatures and categorical structure.
---

# Type Synthesizer

Transform domain concepts into algebraic data types (ADTs). Entities become products, variants become coproducts, hierarchies become recursive types.

## Input

Requires `artifacts/engineering/v{X}/specifications/domain-concepts.yaml` from domain-extractor.

## Output

Generate `artifacts/engineering/v{X}/specifications/requirements.adt`:

```yaml
version: "1.0"
source: "domain-concepts.yaml"

primitives:
  - name: PrimitiveName
    base: string | int | float | bool | datetime | uuid | binary
    constraints: []  # Refinement constraints

products:
  # Records, tuples - "A AND B"
  - name: ProductName
    description: "What this product represents"
    factors:
      - name: field_name
        type: TypeReference
        optional: false
    derives_from: EntityName | ValueObjectName  # Source in domain-concepts

coproducts:
  # Variants, unions - "A OR B"
  - name: CoproductName
    description: "What this variant represents"
    variants:
      - name: VariantName
        payload: TypeReference | null  # null for unit variant
    derives_from: enum | status | error  # Why this is a coproduct

recursive:
  # Self-referential types - trees, lists
  - name: RecursiveName
    description: "What this recursive structure represents"
    base_case: TypeReference  # Terminal case
    recursive_case: TypeReference  # Self-reference
    structure: list | tree | graph

identifiers:
  # Newtype wrappers for IDs
  - name: EntityNameId
    wraps: uuid | string | int
    for_entity: EntityName

type_aliases:
  # Convenience aliases
  - name: AliasName
    target: TypeReference
    purpose: "Why this alias exists"
```

## Synthesis Rules

### Entities → Products

Every entity becomes a product type with its attributes as factors:

```yaml
# From domain-concepts.yaml
entities:
  - name: Merchant
    identity: merchant_id
    attributes:
      - name: shop_domain
        type: string
      - name: subscription
        type: Subscription

# To requirements.adt
identifiers:
  - name: MerchantId
    wraps: uuid
    for_entity: Merchant

products:
  - name: Merchant
    factors:
      - name: id
        type: MerchantId
        optional: false
      - name: shop_domain
        type: ShopDomain  # Create refined primitive
        optional: false
      - name: subscription
        type: Subscription
        optional: false
    derives_from: Merchant
```

### Value Objects → Products

Value objects also become products, but without identity fields:

```yaml
# From domain-concepts.yaml
value_objects:
  - name: Demographics
    attributes:
      - name: age_range
        type: enum:18-25|26-35|36-45|46+
      - name: gender
        type: enum:female|male|non-binary

# To requirements.adt
coproducts:
  - name: AgeRange
    variants:
      - name: Age18To25
        payload: null
      - name: Age26To35
        payload: null
      - name: Age36To45
        payload: null
      - name: Age46Plus
        payload: null
    derives_from: enum

  - name: Gender
    variants:
      - name: Female
        payload: null
      - name: Male
        payload: null
      - name: NonBinary
        payload: null
    derives_from: enum

products:
  - name: Demographics
    factors:
      - name: age_range
        type: AgeRange
        optional: false
      - name: gender
        type: Gender
        optional: false
    derives_from: Demographics
```

### Enums → Coproducts

All enum types become coproducts (sum types):

```yaml
# Pattern: enum:A|B|C becomes
coproducts:
  - name: EnumName
    variants:
      - name: A
        payload: null
      - name: B
        payload: null
      - name: C
        payload: null
```

### Status/State → Coproducts

Entity lifecycle states become coproducts:

```yaml
# Entity with lifecycle: true + state attribute
# To requirements.adt
coproducts:
  - name: AnalysisStatus
    variants:
      - name: Pending
        payload: null
      - name: Processing
        payload: ProcessingInfo  # Optional context
      - name: Completed
        payload: AnalysisResult
      - name: Failed
        payload: FailureReason
    derives_from: status
```

### Relationships → Type References

```yaml
# one-to-many: Parent has list of Child
products:
  - name: Parent
    factors:
      - name: children
        type: List[ChildId]  # Reference by ID

# many-to-one: Child has ParentId
products:
  - name: Child
    factors:
      - name: parent_id
        type: ParentId
```

### Collections

Standard collection types:

```yaml
type_aliases:
  - name: List
    target: "[A]"  # Parametric
    purpose: "Ordered collection"

  - name: Set
    target: "{A}"
    purpose: "Unordered unique collection"

  - name: Map
    target: "{K: V}"
    purpose: "Key-value mapping"

  - name: Option
    target: "A | Null"
    purpose: "Optional value"
```

### Primitives with Constraints

Refine base types with constraints:

```yaml
primitives:
  - name: ShopDomain
    base: string
    constraints:
      - pattern: "^[a-z0-9-]+\\.myshopify\\.com$"

  - name: Email
    base: string
    constraints:
      - format: email

  - name: PositiveInt
    base: int
    constraints:
      - minimum: 1

  - name: Money
    base: float
    constraints:
      - minimum: 0
      - precision: 2
```

## Type Reference Syntax

Use consistent syntax for type references:

| Reference | Meaning |
|-----------|---------|
| `TypeName` | Direct reference to defined type |
| `List[T]` | List of T |
| `Set[T]` | Set of T |
| `Map[K, V]` | Map from K to V |
| `Option[T]` | T or null |
| `T1 × T2` | Product of T1 and T2 |
| `T1 + T2` | Coproduct of T1 and T2 |

## Validation Checklist

Before outputting, verify:

- [ ] Every entity has corresponding identifier type
- [ ] All enum attributes become coproducts
- [ ] No undefined type references
- [ ] Recursive types have base case
- [ ] Products have at least one factor
- [ ] Coproducts have at least two variants
- [ ] Constraints are valid for base type

## Algebraic Laws

Types must satisfy:

**Products (×)**:
- Have projections: `π₁: A × B → A`, `π₂: A × B → B`
- Support pairing: `⟨f, g⟩: C → A × B`

**Coproducts (+)**:
- Have injections: `inl: A → A + B`, `inr: B → A + B`
- Support case analysis: `[f, g]: A + B → C`

**Recursive**:
- Form initial F-algebra
- Support catamorphism (fold)

## Next Skill

Output feeds into:
- **constraint-specifier** → adds proof obligations
- **morphism-specifier** → uses types for signatures
- **categorical-structure-detector** → identifies products/coproducts
