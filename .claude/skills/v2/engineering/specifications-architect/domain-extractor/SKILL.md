---
name: domain-extractor
description: Extract domain concepts from natural language requirements. First skill in the specification pipeline. Use when starting system generation from requirements, analyzing existing system descriptions, or when domain-concepts.yaml is needed. Outputs entities, value objects, aggregates, relationships, operations, external dependencies, and business rules in structured format.
---

# Domain Extractor

Extract structured domain concepts from natural language requirements. First sub-skill in the specification pipeline—all downstream skills depend on this output.

## Workflow

1. Parse input requirements (natural language, user stories, existing docs)
2. Identify domain concepts by category
3. Detect relationships between concepts
4. Extract operations and dependencies
5. Capture business rules
6. Output domain-concepts.yaml

## Output Format

Generate `artifacts/engineering/v{X}/specifications/domain-concepts.yaml`:

```yaml
version: "1.0"
domain: "{domain-name}"

entities:
  - name: EntityName
    description: "What this entity represents"
    identity: "field that uniquely identifies"
    attributes:
      - name: attribute_name
        type: primitive | entity_ref | value_object_ref
        required: true | false
        description: "Purpose of this attribute"
    lifecycle: true | false  # Has state transitions?

value_objects:
  - name: ValueObjectName
    description: "Immutable value with no identity"
    attributes:
      - name: attribute_name
        type: primitive | value_object_ref
        constraints: []  # e.g., "non-empty", "positive", "valid-email"

aggregates:
  - name: AggregateName
    root: EntityName  # Aggregate root entity
    members:
      - EntityName
      - ValueObjectName
    invariants:
      - "Business rule that must always hold within aggregate"

relationships:
  - from: EntityA
    to: EntityB
    type: one-to-one | one-to-many | many-to-many
    name: "relationship_name"
    ownership: owns | references  # owns = cascade delete, references = independent
    required: true | false

operations:
  - name: operation_name
    description: "What this operation does"
    actor: "Who/what initiates"
    input:
      - name: param_name
        type: type_reference
    output: type_reference
    category: command | query  # Commands mutate, queries read
    affects:
      - EntityName  # Which entities are affected

external_dependencies:
  - name: DependencyName
    type: api | database | queue | storage | ai-service
    purpose: "Why this dependency exists"
    operations:
      - name: external_operation
        description: "What we call on external system"
        sync: true | false  # Synchronous or async

business_rules:
  - name: RuleName
    description: "Plain language description"
    scope: EntityName | AggregateName  # What it applies to
    type: invariant | pre-condition | post-condition | constraint
    enforcement: always | on-create | on-update | on-delete
```

## Extraction Guidelines

### Entities vs Value Objects

**Entity**: Has identity, mutable, tracked over time
- "User", "Order", "Merchant", "Profile"
- Ask: "Do I need to distinguish between two instances with same data?"

**Value Object**: No identity, immutable, interchangeable
- "Money", "Address", "DateRange", "Email"
- Ask: "Are two instances with same data equivalent?"

### Detecting Relationships

Look for signals:
- "belongs to", "has", "contains" → ownership
- "references", "links to", "associated with" → reference
- "one", "many", "multiple" → cardinality

### Identifying Operations

From requirements, extract:
- CRUD operations (create, read, update, delete)
- Business operations ("approve", "cancel", "process", "analyze")
- Queries ("list", "search", "find", "get")

Mark operations that:
- Change state → command
- Only read → query
- Call external systems → note in external_dependencies

### Capturing Business Rules

Extract from:
- "must", "should", "cannot", "always", "never"
- Conditional statements ("if X then Y")
- Constraints ("at least", "at most", "between")

Classify as:
- **invariant**: Always true (e.g., "Order total must be positive")
- **pre-condition**: Must be true before operation
- **post-condition**: Must be true after operation
- **constraint**: Limits on values

### External Dependencies

Look for:
- Third-party APIs (Shopify, Stripe, Groq, etc.)
- Databases (explicitly mentioned)
- Message queues (async operations)
- Storage (files, blobs, images)
- AI/ML services

## Validation Checklist

Before outputting, verify:

- [ ] Every entity has identity field
- [ ] Every relationship has both ends defined
- [ ] Operations reference defined types
- [ ] External dependencies have clear purpose
- [ ] Business rules reference defined entities/aggregates
- [ ] No circular ownership relationships
- [ ] Aggregate roots are entities

## Next Skill

Output feeds into:
- **type-synthesizer** → converts to algebraic data types
- **morphism-specifier** → defines operation signatures
