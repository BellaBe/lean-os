---
name: morphism-specifier
description: Define operations as morphism signatures in services.spec.yaml. Use after type-synthesizer to convert domain operations into typed morphisms with domain, codomain, and composition requirements. Creates base services.spec.yaml without effects—effect-analyzer enriches later.
---

# Morphism Specifier

Transform operations into typed morphism signatures. Each operation becomes a morphism `f: A → B` where A is input type and B is output type.

## Input

Requires:
- `artifacts/engineering/v{X}/specifications/domain-concepts.yaml` (operations section)
- `artifacts/engineering/v{X}/specifications/requirements.adt` (type definitions)

## Output

Generate `artifacts/engineering/v{X}/specifications/services.spec.yaml`:

```yaml
version: "1.0"
sources:
  - domain-concepts.yaml
  - requirements.adt

modules:
  - name: ModuleName
    description: "What this module handles"
    morphisms: [morphism_names]

morphisms:
  - name: morphism_name
    module: ModuleName
    description: "What this morphism does"
    
    # Signature
    domain: InputType  # Source object
    codomain: OutputType  # Target object
    
    # Categorical properties
    properties:
      total: true | false  # Defined for all inputs?
      deterministic: true | false  # Same input → same output?
      idempotent: true | false  # f∘f = f?
    
    # Composition
    composes_with:
      - other_morphism  # What it can chain with
    
    # Classification
    category: command | query
    layer: domain | repository | external

compositions:
  # Named composition chains
  - name: composition_name
    chain: [morphism_a, morphism_b, morphism_c]
    description: "What this pipeline does"
    law: associative  # Composition law that must hold

identity_morphisms:
  # Identity morphisms for each type
  - type: TypeName
    morphism: id_TypeName
    law: "f ∘ id = f = id ∘ f"
```

## Morphism Classification

### By Category (Command/Query)

**Commands** (mutate state):
- create_*, update_*, delete_*
- process_*, approve_*, cancel_*
- Return: created/modified entity

**Queries** (read only):
- get_*, find_*, list_*, search_*
- Return: entity or collection

```yaml
morphisms:
  - name: create_merchant
    category: command
    domain: CreateMerchantInput
    codomain: Merchant

  - name: get_merchant
    category: query
    domain: MerchantId
    codomain: Merchant
```

### By Layer

**Domain**: Pure business logic
```yaml
  - name: validate_subscription
    layer: domain
    domain: Subscription
    codomain: ValidatedSubscription
```

**Repository**: Storage operations
```yaml
  - name: save_merchant
    layer: repository
    domain: Merchant
    codomain: MerchantId
```

**External**: Third-party calls
```yaml
  - name: fetch_shopify_products
    layer: external
    domain: ShopDomain
    codomain: List[Product]
```

## Signature Patterns

### CRUD Operations

```yaml
# Create: Input → Entity
- name: create_entity
  domain: CreateEntityInput
  codomain: Entity
  properties:
    total: true  # Always produces output
    deterministic: false  # IDs differ

# Read: Id → Entity
- name: get_entity
  domain: EntityId
  codomain: Entity
  properties:
    total: false  # May not exist
    deterministic: true

# Update: (Id, Patch) → Entity
- name: update_entity
  domain: UpdateEntityInput  # Contains id + changes
  codomain: Entity
  properties:
    total: false  # Entity may not exist
    deterministic: true
    idempotent: true  # Same patch → same result

# Delete: Id → Unit
- name: delete_entity
  domain: EntityId
  codomain: Unit
  properties:
    total: false
    idempotent: true  # Delete twice = delete once

# List: Query → List[Entity]
- name: list_entities
  domain: ListEntitiesQuery
  codomain: PaginatedList[Entity]
  properties:
    total: true
    deterministic: false  # Data may change
```

### Business Operations

```yaml
# Process: Entity → ProcessedEntity
- name: process_analysis
  domain: Analysis
  codomain: ProcessedAnalysis
  properties:
    total: false  # May fail
    deterministic: false  # AI results vary

# Aggregate: List[Entity] → Summary
- name: generate_recommendations
  domain: AnalysisResult
  codomain: RecommendationSet
  properties:
    total: true
    deterministic: false
```

## Input/Output Types

### Defining Input Types

Create dedicated input types in requirements.adt:

```yaml
# For create operations
products:
  - name: CreateMerchantInput
    factors:
      - name: shop_domain
        type: ShopDomain
      - name: access_token
        type: AccessToken
    derives_from: operation_input

# For update operations
products:
  - name: UpdateMerchantInput
    factors:
      - name: id
        type: MerchantId
      - name: changes
        type: MerchantPatch
    derives_from: operation_input

# For list/query operations
products:
  - name: ListMerchantsQuery
    factors:
      - name: filters
        type: MerchantFilters
        optional: true
      - name: pagination
        type: PaginationParams
        optional: true
    derives_from: query_input
```

### Tuples for Multiple Inputs

When morphism needs multiple inputs, use product:

```yaml
# f: A × B → C
- name: create_recommendation
  domain: ProfileId × AnalysisId  # Product type
  codomain: Recommendation
```

## Composition

### Defining Compositions

```yaml
compositions:
  # Sequential pipeline
  - name: full_analysis_flow
    chain:
      - upload_photo
      - request_analysis
      - process_analysis
      - generate_recommendations
    description: "Complete analysis to recommendations"
    law: associative

  # Read-modify-write
  - name: update_subscription_flow
    chain:
      - get_merchant
      - update_subscription
      - save_merchant
    description: "Subscription update pattern"
```

### Composition Laws

For chain `[f, g, h]`:

```
(h ∘ g) ∘ f = h ∘ (g ∘ f)  # Associativity
```

Types must match:
```
f: A → B
g: B → C
h: C → D
⟹ (h ∘ g ∘ f): A → D
```

## Module Organization

Group related morphisms:

```yaml
modules:
  - name: merchant
    description: "Merchant management"
    morphisms:
      - create_merchant
      - get_merchant
      - update_merchant
      - delete_merchant
      - update_subscription

  - name: profile
    description: "Customer profiles"
    morphisms:
      - create_profile
      - get_profile
      - update_profile
      - list_profiles

  - name: analysis
    description: "Photo analysis"
    morphisms:
      - request_analysis
      - get_analysis
      - process_analysis

  - name: recommendation
    description: "Product recommendations"
    morphisms:
      - generate_recommendations
      - get_recommendations
      - rate_recommendation
```

## Validation Checklist

Before outputting, verify:

- [ ] All operations from domain-concepts have morphisms
- [ ] Domain/codomain reference types in requirements.adt
- [ ] Compositions have matching types
- [ ] Every module has at least one morphism
- [ ] Properties are consistent (query → deterministic)
- [ ] Identity morphisms exist for composed types

## Properties Reference

| Property | Meaning | Example |
|----------|---------|---------|
| total | Defined for all inputs | get may fail (not total) |
| deterministic | Same input → same output | AI calls (not deterministic) |
| idempotent | f∘f = f | delete (idempotent) |

## Next Skill

Output feeds into:
- **effect-analyzer** → adds IO, Either effects
- **resilience-specifier** → adds retry, circuit breaker
- **categorical-structure-detector** → identifies morphism patterns
