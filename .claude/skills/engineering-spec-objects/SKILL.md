---
name: spec-objects
description: |
  Extract type definitions from requirements. Identifies primitives, products (×),
  coproducts (+), and refined types as categorical objects. Use when: starting
  new system, adding types, analyzing domain model, defining data structures.
---

# Spec Objects

Extract categorical objects (types) from requirements.

## Categorical Foundation

Objects in a category are the "things" between which morphisms map. In our domain:

```
Objects = Types
        = Primitives + Products + Coproducts + Refinements
```

## Input

- Natural language requirements
- Existing domain documentation
- Database schemas (for extraction)
- API contracts (for extraction)

## Output

`artifacts/v{N}/spec/objects.yaml`

## Process

1. **Identify entities** — Nouns with identity (have an ID)
2. **Identify value objects** — Nouns without identity (immutable values)
3. **Identify primitives** — Base types needed
4. **Classify structure** — Product, coproduct, or refined
5. **Establish relationships** — Which types reference which

## Object Kinds

### Primitives

Atomic types with no internal structure in our domain.

```yaml
- id: "UserId"
  kind: primitive
  definition:
    base: "UUID"
  description: "Unique identifier for a user"
```

**Standard primitives:**
- `Bool` — true/false
- `String` — UTF-8 text
- `Int` — Integer
- `Float` — Floating point
- `Decimal` — Exact decimal (for money)
- `UUID` — Universally unique identifier
- `DateTime` — Timestamp with timezone
- `Date` — Calendar date
- `Duration` — Time interval
- `Bytes` — Raw binary
- `Json` — Arbitrary JSON
- `Unit` — Single value (void)

### Products (×)

Compound types with multiple fields. "A AND B AND C"

```yaml
- id: "User"
  kind: product
  definition:
    fields:
      - name: "id"
        type: "UserId"
      - name: "email"
        type: "Email"
      - name: "status"
        type: "UserStatus"
      - name: "created_at"
        type: "DateTime"
  description: "A registered user in the system"
```

**Pattern recognition:**
- "X has Y and Z" → Product
- "X contains A, B, C" → Product
- "X consists of..." → Product
- Database row with columns → Product

### Coproducts (+)

Sum types with variants. "A OR B OR C"

```yaml
- id: "UserStatus"
  kind: coproduct
  definition:
    variants:
      - name: "Pending"
        payload: null
      - name: "Active"
        payload: null
      - name: "Suspended"
        payload: "SuspensionReason"
      - name: "Deleted"
        payload: "DateTime"
  description: "Possible states of a user account"
```

**Pattern recognition:**
- "X is either A or B" → Coproduct
- "X can be one of..." → Coproduct
- "Status: pending | active | closed" → Coproduct
- Enum with variants → Coproduct

### Refined Types

Constrained subtypes with predicates.

```yaml
- id: "Email"
  kind: refined
  definition:
    base: "String"
    predicate: "matches(EMAIL_REGEX)"
  description: "Valid email address"
```

**Pattern recognition:**
- "X is Y that must be..." → Refined
- "Valid X" → Refined
- "X where condition" → Refined
- Business rules on values → Refined

## Common Patterns

### Entity with ID

```yaml
# Pattern: Entity X has identity
- id: "XId"
  kind: primitive
  definition:
    base: "UUID"
    
- id: "X"
  kind: product
  definition:
    fields:
      - name: "id"
        type: "XId"
      # ... other fields
```

### Optional Field

```yaml
# Pattern: X may or may not have Y
- id: "X"
  kind: product
  definition:
    fields:
      - name: "y"
        type: "Y"
        optional: true  # Generates Option[Y] or Y | null
```

### List Field

```yaml
# Pattern: X has many Y
- id: "X"
  kind: product
  definition:
    fields:
      - name: "items"
        type: "List[Y]"  # Use List[T] syntax
```

### Nested Product

```yaml
# Pattern: X contains structured data
- id: "Address"
  kind: product
  definition:
    fields:
      - name: "street"
        type: "String"
      - name: "city"
        type: "String"
        
- id: "User"
  kind: product
  definition:
    fields:
      - name: "address"
        type: "Address"  # Reference to nested product
```

### Recursive Type

```yaml
# Pattern: X contains X (tree structure)
- id: "Comment"
  kind: product
  definition:
    fields:
      - name: "id"
        type: "CommentId"
      - name: "text"
        type: "String"
      - name: "replies"
        type: "List[Comment]"  # Recursive reference
```

## Output Format

```yaml
version: "1.0"
objects:
  # Primitives (identifiers)
  - id: "UserId"
    kind: primitive
    definition:
      base: "UUID"
    description: "Unique identifier for users"
    traces_to: ["req:user-identity"]
    
  - id: "OrderId"
    kind: primitive
    definition:
      base: "UUID"
    description: "Unique identifier for orders"
    traces_to: ["req:order-tracking"]
    
  # Refined types (validated values)
  - id: "Email"
    kind: refined
    definition:
      base: "String"
      predicate: "matches('^[\\w.-]+@[\\w.-]+\\.\\w+$')"
    description: "Valid email address"
    traces_to: ["req:email-validation"]
    
  - id: "Money"
    kind: refined
    definition:
      base: "Decimal"
      predicate: ">= 0"
    description: "Non-negative monetary amount"
    traces_to: ["req:financial-constraints"]
    
  # Coproducts (enums, states)
  - id: "UserStatus"
    kind: coproduct
    definition:
      variants:
        - name: "Pending"
          payload: null
        - name: "Active"
          payload: null
        - name: "Suspended"
          payload: "SuspensionReason"
    description: "User account status"
    traces_to: ["req:user-lifecycle"]
    
  - id: "SuspensionReason"
    kind: coproduct
    definition:
      variants:
        - name: "TOS_Violation"
          payload: null
        - name: "PaymentFailed"
          payload: null
        - name: "UserRequested"
          payload: null
    description: "Reasons for account suspension"
    traces_to: ["req:suspension-policy"]
    
  # Products (entities, value objects)
  - id: "User"
    kind: product
    definition:
      fields:
        - name: "id"
          type: "UserId"
        - name: "email"
          type: "Email"
        - name: "status"
          type: "UserStatus"
        - name: "created_at"
          type: "DateTime"
    description: "A registered user"
    traces_to: ["req:user-entity"]
    
  - id: "CreateUserInput"
    kind: product
    definition:
      fields:
        - name: "email"
          type: "Email"
        - name: "password"
          type: "String"
    description: "Input for creating a new user"
    traces_to: ["req:user-registration"]
```

## Validation Rules

1. **Uniqueness**: Every `id` must be unique
2. **Completeness**: Every referenced type must exist
3. **No cycles in products**: A cannot contain B which contains A (except through List)
4. **Valid predicates**: Refined type predicates must be well-formed
5. **Traces**: Every object should trace to at least one requirement

## Validation Checklist

- [ ] All product field types exist as objects
- [ ] All coproduct payload types exist as objects
- [ ] All refined base types exist as objects
- [ ] No direct circular references
- [ ] All traces_to reference valid requirements
- [ ] IDs follow naming convention (PascalCase)

## Do NOT

- **Assume API structure** — Request/Response types come from functors, not here
- **Assume persistence** — Model types come from functors, not here
- **Create "Service" types** — Services are morphism implementations
- **Create "Repository" types** — Repositories are functor applications
- **Include implementation details** — Just the type structure

## Example Extraction

**Requirement:**
> Users can register with email and password. Each user has a status 
> (pending, active, or suspended). Suspended users must have a reason.

**Extraction:**

1. Entities: User (has identity)
2. Value objects: Email (validated string)
3. Primitives: UserId (UUID)
4. Coproducts: UserStatus (pending | active | suspended)
5. Sub-coproduct: SuspensionReason (if suspended)
6. Input types: CreateUserInput (for registration)

**Output:** As shown in Output Format section above.
