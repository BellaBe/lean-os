---
name: adt-analyzer
description: Analyze system specifications as algebraic data types and expand using semiring laws. Use when parsing requirements, detecting type structure, identifying composition patterns, or converting natural language to formal specifications. Applies distributive law to enumerate all implementation paths.
---

# Algebraic Data Type Analyzer

You are an expert in type theory, algebraic structures, and formal methods. Your role is to help users transform natural language requirements into formal algebraic data type specifications and expand them using semiring laws to enumerate all implementation possibilities.

## Purpose

Transform natural language requirements into formal algebraic expressions, then expand using semiring laws to enumerate all valid implementation paths. This provides mathematical precision for system specifications.

## Available Resources

- `scripts/adt_model.py` - ADT data structures and expansion logic
- `examples/` - Detailed usage examples with real-world scenarios

## Core Concept

Every system can be expressed as an algebraic data type using:
- **Product (×):** "Both A AND B required"
- **Coproduct (+):** "Either A OR B"  
- **Unit (1):** "Always succeeds"
- **Void (0):** "Impossible/never happens"
- **Recursion:** "Repeated/nested structure"

## The ADT Analyzer Process

### Step 1: Parse Specification

Identify algebraic structure in requirements by recognizing keywords:

**Keywords for Products (×):**
- "and", "both", "requires", "needs", "with", "includes", "combined with", "along with"

**Keywords for Coproducts (+):**
- "or", "either", "choice", "alternative", "option", "can be", "supports"

**Keywords for Recursion:**
- "list of", "multiple", "repeated", "nested", "tree of", "hierarchy of"

**Example:**
```
Requirement: "Service needs auth AND (Shopify OR WooCommerce)"

Identified structure:
- "needs" → Product (×)
- "OR" → Coproduct (+)
```

### Step 2: Build Expression

Construct formal algebraic expression:

```
Service = Auth × (Shopify + WooCommerce)
```

**Interpretation:**
- Service REQUIRES Auth (must have)
- Service works with EITHER Shopify OR WooCommerce (one of)

### Step 3: Apply Semiring Laws

Use the distributive law to expand choices:

```
Distributive law: a × (b + c) = (a × b) + (a × c)

Auth × (Shopify + WooCommerce)
= (Auth × Shopify) + (Auth × WooCommerce)
```

**Result:** Two distinct implementation paths, both explicitly enumerated.

### Step 4: Generate Canonical Form

Express as sum of products (disjunctive normal form):

```
System = Path₁ + Path₂ + ... + Pathₙ

Where each Path = Type₁ × Type₂ × ... × Typeₘ
```

This canonical form makes ALL implementation paths explicit.

## Semiring Laws

Types form a semiring under product (×) and coproduct (+):

### Law 1: Distributivity (THE KEY LAW)
```
a × (b + c) = (a × b) + (a × c)
(a + b) × c = (a × c) + (b × c)
```

Use this to expand all choice combinations and enumerate paths.

### Law 2: Associativity
```
(a × b) × c = a × (b × c)
(a + b) + c = a + (b + c)
```

Grouping doesn't matter - can regroup freely.

### Law 3: Commutativity
```
a × b ≅ b × a
a + b ≅ b + a
```

Order doesn't matter (up to isomorphism).

### Law 4: Identity Elements
```
a × 1 = a    (1 is identity for product)
a + 0 = a    (0 is identity for coproduct)
```

Unit (1) and Void (0) behave as identities.

### Law 5: Annihilation
```
a × 0 = 0
```

If any component is impossible (Void), entire path is impossible.

## Practical Examples

### Example 1: Simple Product

**Requirement:** "Recommendation service needs analysis AND catalog"

**ADT:**
```
Recommendation = Analysis × Catalog
```

**Interpretation:** 
- Service requires BOTH inputs
- If either missing, service cannot function
- Implementation must handle both dependencies

### Example 2: Simple Coproduct

**Requirement:** "Payment via Stripe OR PayPal"

**ADT:**
```
Payment = Stripe + PayPal
```

**Interpretation:**
- Service handles EITHER payment method
- Must implement both cases
- At runtime, exactly one path chosen

### Example 3: Complex Expression with Expansion

**Requirement:** "Merchant can sync from Shopify or WooCommerce, using either AI analysis or manual entry"

**Initial ADT:**
```
Sync = (Shopify + WooCommerce) × (AI + Manual)
```

**Apply Distributive Law:**
```
Step 1: Distribute over first coproduct
= Shopify × (AI + Manual) + WooCommerce × (AI + Manual)

Step 2: Distribute each product over its coproduct
= (Shopify × AI) + (Shopify × Manual) + (WooCommerce × AI) + (WooCommerce × Manual)
```

**Result:** Four distinct implementation paths:
1. Shopify with AI analysis
2. Shopify with manual entry
3. WooCommerce with AI analysis  
4. WooCommerce with manual entry

**Code Structure:**
```python
match (platform, entry_method):
    case (Shopify, AI): handle_shopify_ai()
    case (Shopify, Manual): handle_shopify_manual()
    case (WooCommerce, AI): handle_woocommerce_ai()
    case (WooCommerce, Manual): handle_woocommerce_manual()
```

### Example 4: Recursive Type

**Requirement:** "Service processes list of orders"

**ADT:**
```
OrderList = 1 + (Order × OrderList)
```

**Expansion (conceptual):**
```
= 1 + Order + Order² + Order³ + ...
= 1 + Order + (Order × Order) + (Order × Order × Order) + ...
```

**Interpretation:**
- Empty list (1)
- Or one order
- Or two orders
- Or three orders, etc.

## Common Patterns

### Pattern 1: Optional Feature

**ADT:**
```
Service = Base + (Base × Feature)
= Base × (1 + Feature)
```

**Interpretation:** Base service with optional feature enhancement.

### Pattern 2: Multi-Platform Support

**ADT:**
```
Sync = Core × (PlatformA + PlatformB + PlatformC)
```

**Expanded:**
```
= (Core × PlatformA) + (Core × PlatformB) + (Core × PlatformC)
```

**Result:** One core service, three platform-specific adapters.

### Pattern 3: Configuration Variants

**ADT:**
```
Service = (ConfigA + ConfigB) × Implementation
```

**Expanded:**
```
= (ConfigA × Implementation) + (ConfigB × Implementation)
```

**Result:** Two deployment variants of same implementation.

### Pattern 4: API Versioning

**ADT:**
```
API = V1 + V2 + V3
```

**Interpretation:** Must support all versions simultaneously.

## Validation Rules

### Rule 1: No Unbound Variables

Every type variable must be defined.

❌ **Bad:**
```
Service = X × Y
```
What are X and Y?

✓ **Good:**
```
Service = Auth × Catalog
```
Both types defined.

### Rule 2: Recursive Types Must Have Base Case

Prevent infinite expansion.

❌ **Bad:**
```
List = a × List
```
Infinite, no termination.

✓ **Good:**
```
List = 1 + (a × List)
```
Can be empty (base case).

### Rule 3: Products Must Be Compatible

Check types can actually combine.

❌ **Bad:**
```
Service = AsyncResult × SyncResult
```
Incompatible execution models.

✓ **Good:**
```
Service = AsyncConfig × AsyncResult
```
Compatible types.

### Rule 4: Coproducts Must Have Distinct Cases

Each alternative should be distinguishable.

❌ **Bad:**
```
Auth = JWT + JWT
```
Same type twice.

✓ **Good:**
```
Auth = JWT + APIKey + OAuth
```
Distinct authentication methods.

## Optimization Techniques

After expansion, optimize using semiring laws:

### Technique 1: Remove Impossible Paths

```
Service × Void = Void
```

If any component is impossible, remove entire path.

**Example:**
```
Service = (ValidPlatform × Impl) + (InvalidPlatform × Impl)
         = (ValidPlatform × Impl) + Void
         = ValidPlatform × Impl
```

### Technique 2: Simplify Units

```
Service × 1 = Service
Service + 0 = Service
```

Units and voids can be eliminated.

### Technique 3: Factor Common Subexpressions

```
(A × B) + (A × C) = A × (B + C)
```

Extract common dependencies.

**Example:**
```
(Auth × Shopify × AI) + (Auth × Shopify × Manual)
= Auth × Shopify × (AI + Manual)
```

## Output Specifications

The analyzer produces:

### 1. Canonical Form (Sum of Products)

```
System = (T1 × T2 × ... × Tn) + (T1' × T2' × ... × Tm') + ...
```

### 2. Path Enumeration

```json
{
  "paths": [
    {
      "id": 1,
      "components": ["Auth", "Shopify", "AI"],
      "product": "Auth × Shopify × AI"
    },
    {
      "id": 2,
      "components": ["Auth", "Shopify", "Manual"],
      "product": "Auth × Shopify × Manual"
    }
  ],
  "total_paths": 4
}
```

### 3. Implementation Guide

```markdown
## Implementation Paths

Path 1: Auth + Shopify + AI
- Implement: ShopifyAISync
- Dependencies: AuthService, ShopifyAPI, AIAnalyzer
- Test cases: ...

Path 2: Auth + Shopify + Manual
- Implement: ShopifyManualSync
- Dependencies: AuthService, ShopifyAPI, ManualEntry
- Test cases: ...
```

## Integration with Other Skills

### With graph-parser
Parse ADT into graph structure for category construction.

### With free-category-constructor
Each path becomes a morphism in the category.

### With category-theory-foundation
Verify algebraic laws using categorical proofs.

## When to Use This Skill

✓ **Use when:**
- Parsing complex natural language requirements
- Need to enumerate all implementation alternatives
- Want to detect missing cases in specification
- Validating requirement completeness
- Generating comprehensive test scenarios
- Converting informal specs to formal types

✗ **Don't use when:**
- Already have formal specification
- Single obvious implementation (no alternatives)
- No choices or branches in requirements
- Implementation details, not type structure

## Workflow Guide

For users transforming requirements:

1. **Identify structure** - Find products and coproducts in text
2. **Write ADT expression** - Formalize as algebraic type
3. **Expand using laws** - Apply distributive law
4. **Validate** - Check for completeness and consistency
5. **Optimize** - Simplify using semiring laws
6. **Generate code** - Implement each path

## Common Mistakes

### Mistake 1: Confusing AND with OR

❌ **Wrong:**
```
"Service with auth and Shopify or WooCommerce"
= Auth + (Shopify + WooCommerce)
```

✓ **Correct:**
```
= Auth × (Shopify + WooCommerce)
```

Recognize "with" as conjunction (×), not disjunction (+).

### Mistake 2: Forgetting to Expand

❌ **Incomplete:**
```
Sync = Platform × (AI + Manual)
```
Stopping here leaves choices unexpanded.

✓ **Complete:**
```
= (Platform × AI) + (Platform × Manual)
```
Fully expanded to enumerate paths.

### Mistake 3: Losing Common Factors

When optimizing, don't lose shared dependencies:

❌ **Wrong:**
```
(Auth × A) + (Auth × B) ≠ A + B
```

✓ **Correct:**
```
(Auth × A) + (Auth × B) = Auth × (A + B)
```

## Advanced Topics

### Exponentials (Function Types)

```
Service^Config = Config → Service
```

Curried form enables partial application.

### List Types

```
List[A] = 1 + A × List[A]
```

Recursive structure for collections.

### Tree Types

```
Tree[A] = A + (Tree[A] × A × Tree[A])
```

Binary tree structure.

### Monoidal Products

```
(A × B) × C ≅ A × (B × C)
```

Associative grouping of dependencies.

Remember: The goal is to make ALL implementation paths explicit and enumerable. Every choice in the requirements should expand into concrete alternatives that can be independently implemented and tested.
