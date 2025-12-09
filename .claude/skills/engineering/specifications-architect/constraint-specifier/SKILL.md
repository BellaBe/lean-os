---
name: constraint-specifier
description: Capture business rules as formal propositions and constraints. Use after type-synthesizer to formalize invariants, pre-conditions, post-conditions from domain-concepts.yaml and requirements.adt. Outputs constraints.yaml with propositions that become proof obligations in types.curry-howard.
---

# Constraint Specifier

Transform business rules into formal propositions. These constraints become proof obligations that the implementation must satisfy.

## Input

Requires:
- `artifacts/engineering/v{X}/specifications/domain-concepts.yaml` (business_rules section)
- `artifacts/engineering/v{X}/specifications/requirements.adt` (type definitions)

## Output

Generate `artifacts/engineering/v{X}/specifications/constraints.yaml`:

```yaml
version: "1.0"
sources:
  - domain-concepts.yaml
  - requirements.adt

propositions:
  # Things that must be provably true
  - name: PropositionName
    description: "Plain language description"
    formal: "Logical formula"
    scope: TypeName  # What type this applies to
    kind: invariant | pre | post | refinement

invariants:
  # Always true for a type
  - name: InvariantName
    type: TypeName
    property: "What must always hold"
    formal: "∀x: Type. Property(x)"

pre_conditions:
  # Must be true before operation
  - name: PreConditionName
    operation: operation_name
    requires: "What must be true before"
    formal: "P(input) → ..."

post_conditions:
  # Must be true after operation
  - name: PostConditionName
    operation: operation_name
    ensures: "What must be true after"
    formal: "... → Q(output)"

refinement_types:
  # Types with embedded proofs
  - name: RefinedTypeName
    base: BaseType
    predicate: "Condition that must hold"
    formal: "Σ(x: Base). P(x)"

relationships:
  # Constraints between types
  - name: RelationshipConstraint
    between: [TypeA, TypeB]
    constraint: "How they must relate"
    formal: "∀a: A, b: B. R(a, b)"

cardinality:
  # Collection size constraints
  - name: CardinalityConstraint
    collection: TypeName.field
    min: 0
    max: null  # null = unbounded
    formal: "min ≤ |collection| ≤ max"
```

## Formalization Patterns

### Invariants

Business rules that must always hold:

```yaml
# "Order total must be positive"
invariants:
  - name: PositiveOrderTotal
    type: Order
    property: "total > 0"
    formal: "∀o: Order. o.total > 0"

# "Merchant must have valid shop domain"
invariants:
  - name: ValidShopDomain
    type: Merchant
    property: "shop_domain matches Shopify pattern"
    formal: "∀m: Merchant. IsValidShopifyDomain(m.shop_domain)"
```

### Pre-conditions

Requirements before an operation can execute:

```yaml
# "Cannot analyze without photo"
pre_conditions:
  - name: PhotoRequired
    operation: request_analysis
    requires: "photo is not empty"
    formal: "photo ≠ ∅ → request_analysis(profile, photo)"

# "Profile must exist before analysis"
pre_conditions:
  - name: ProfileExists
    operation: request_analysis
    requires: "profile_id references existing profile"
    formal: "∃p: Profile. p.id = profile_id → request_analysis(...)"
```

### Post-conditions

Guarantees after operation completes:

```yaml
# "Analysis status is pending after creation"
post_conditions:
  - name: InitialStatusPending
    operation: request_analysis
    ensures: "returned analysis has Pending status"
    formal: "request_analysis(...) → result.status = Pending"

# "Created entity has valid ID"
post_conditions:
  - name: ValidIdAfterCreate
    operation: create_merchant
    ensures: "returned merchant has non-null ID"
    formal: "create_merchant(...) → result.id ≠ null"
```

### Refinement Types

Types that carry their proofs:

```yaml
# Non-empty string
refinement_types:
  - name: NonEmptyString
    base: String
    predicate: "length > 0"
    formal: "Σ(s: String). length(s) > 0"

# Valid email
refinement_types:
  - name: ValidEmail
    base: String
    predicate: "matches email regex"
    formal: "Σ(s: String). IsEmail(s)"

# Positive money amount
refinement_types:
  - name: PositiveMoney
    base: Money
    predicate: "amount ≥ 0"
    formal: "Σ(m: Money). m.amount ≥ 0"
```

### Relationship Constraints

Dependencies between types:

```yaml
# "Recommendation requires completed analysis"
relationships:
  - name: RecommendationAnalysisComplete
    between: [Recommendation, Analysis]
    constraint: "linked analysis must be complete"
    formal: "∀r: Recommendation. r.analysis.status = Completed"

# "Child must reference valid parent"
relationships:
  - name: ValidParentReference
    between: [Profile, Merchant]
    constraint: "merchant_id must exist"
    formal: "∀p: Profile. ∃m: Merchant. p.merchant_id = m.id"
```

### State Transition Constraints

For entities with lifecycle:

```yaml
# "Analysis can only transition Pending → Processing"
propositions:
  - name: ValidAnalysisTransition
    description: "Analysis status transitions are restricted"
    formal: |
      transition(Pending, Processing) ∧
      transition(Processing, Completed) ∧
      transition(Processing, Failed) ∧
      ¬transition(Completed, _) ∧
      ¬transition(Failed, _)
    scope: AnalysisStatus
    kind: invariant
```

## Logical Notation

Use consistent notation:

| Symbol | Meaning | Example |
|--------|---------|---------|
| `∀` | For all | `∀x: T. P(x)` |
| `∃` | Exists | `∃x: T. P(x)` |
| `→` | Implies | `P → Q` |
| `∧` | And | `P ∧ Q` |
| `∨` | Or | `P ∨ Q` |
| `¬` | Not | `¬P` |
| `Σ` | Dependent sum | `Σ(x: A). P(x)` |
| `Π` | Dependent product | `Π(x: A). B(x)` |
| `=` | Equals | `x = y` |
| `≠` | Not equals | `x ≠ y` |
| `∈` | Element of | `x ∈ S` |
| `⊆` | Subset | `A ⊆ B` |

## Extracting from Business Rules

Map domain-concepts business rules to constraints:

```yaml
# From domain-concepts.yaml
business_rules:
  - name: AnalysisRequiresPhoto
    description: "Cannot analyze without photo upload"
    scope: Analysis
    type: pre-condition
    enforcement: on-create

# To constraints.yaml
pre_conditions:
  - name: AnalysisRequiresPhoto
    operation: create_analysis
    requires: "photo must be provided"
    formal: "photo ≠ ∅ → create_analysis(profile_id, photo)"
```

## Validation Checklist

Before outputting, verify:

- [ ] All business_rules from domain-concepts are covered
- [ ] Formal notation is syntactically valid
- [ ] Type references exist in requirements.adt
- [ ] Operations exist in domain-concepts
- [ ] No contradictory constraints
- [ ] Invariants are satisfiable (type is inhabitable)

## Constraint Categories

Group by proof difficulty:

**Trivial** (type system enforces):
- Non-null fields (required: true)
- Type matching

**Decidable** (runtime check):
- Range constraints (min/max)
- Pattern matching
- Cardinality

**Requires Proof** (formal verification):
- State machine validity
- Relationship integrity
- Complex invariants

## Next Skill

Output feeds into:
- **proof-obligation-generator** → generates types.curry-howard
- **morphism-specifier** → uses pre/post conditions
