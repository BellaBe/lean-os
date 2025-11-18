# System Builder: Practical Execution Guide

## Quick Start

### Prerequisites
```bash
# Install skills
mkdir -p ~/.claude/skills
cp -r skills/* ~/.claude/skills/

# Verify installation
ls ~/.claude/skills/
# Should show: adt-analyzer, category-theory-foundation, functor-generator, etc.
```

### Basic Usage

```bash
# Start Claude with skills
claude

# Ask Claude to build a system
> Build a multi-tenant catalog service that syncs from Shopify or WooCommerce
```

Claude will automatically:
1. Detect the requirement
2. Activate relevant skills
3. Execute the workflow
4. Generate production code

## Skill Activation Patterns

Skills are **model-invoked** - Claude automatically decides when to use them based on your request.

### Trigger Phrases

| Skill | Trigger Phrases |
|-------|----------------|
| ADT Analyzer | "parse specification", "analyze requirements", "enumerate paths" |
| Category Theory | "verify composition", "validate structure", "check laws" |
| Functor Generator | "multi-tenant", "optional feature", "async", "replicated" |
| NatTrans Engine | "migrate", "transform", "upgrade version", "change strategy" |
| Curry-Howard Prover | "prove correctness", "type signature", "verify requirements" |
| System Optimizer | "optimize", "improve performance", "reduce code" |
| Architecture Validator | "validate architecture", "check correctness", "verify laws" |
| Code Generator | "generate code", "implement", "create service", "build system" |

## Real-World Examples

### Example 1: Simple Catalog Service

**Request:**
```
Build a catalog service that syncs products from Shopify
```

**Claude's Execution:**

```
[Activating: adt-analyzer]
Parsing specification...
  Expression: ShopifySync × Products
  Paths: 1 (simple service)

[Activating: category-theory-foundation]
Validating structure...
  ✓ Product well-formed
  ✓ Types defined

[Activating: curry-howard-prover]
Generating type signature...
  def sync_catalog(credentials: ShopifyCredentials) -> Products

[Activating: architecture-validator]
Validating...
  ✓ Composition valid
  ✓ Identity exists

[Activating: code-generator]
Generating implementation...
  Created: src/catalog_service.py
  Created: tests/test_catalog.py

✓ System generated successfully
```

**Output:**
```python
# src/catalog_service.py
from dataclasses import dataclass
from typing import List

@dataclass
class Product:
    id: str
    title: str
    price: float

@dataclass
class ShopifyCredentials:
    shop_url: str
    access_token: str

class CatalogService:
    """Sync products from Shopify"""
    
    def sync_catalog(self, credentials: ShopifyCredentials) -> List[Product]:
        """
        Fetch all products from Shopify store
        
        Type signature proves: Given credentials → Can produce products
        """
        import shopify
        
        shopify.Session.setup(
            api_key=credentials.access_token,
            secret=credentials.shop_url
        )
        
        products = shopify.Product.find()
        return [
            Product(
                id=p.id,
                title=p.title,
                price=float(p.variants[0].price)
            )
            for p in products
        ]
```

### Example 2: Multi-Tenant with Choice

**Request:**
```
Build a recommendation service that:
- Supports multiple merchants (multi-tenant)
- Syncs from Shopify OR WooCommerce
- Uses AI analysis OR manual categorization
```

**Claude's Execution:**

```
[Activating: adt-analyzer]
Parsing specification...
  Expression: Tenant × (Shopify + WooCommerce) × (AI + Manual)
  
  Expanding using distributivity...
  = (Tenant × Shopify × AI) +
    (Tenant × Shopify × Manual) +
    (Tenant × WooCommerce × AI) +
    (Tenant × WooCommerce × Manual)
  
  Paths: 4

[Activating: category-theory-foundation]
Validating structure...
  ✓ All products well-formed
  ✓ Coproducts well-formed
  ✓ No impossible paths

[Activating: functor-generator]
Analyzing transformation needs...
  - Multi-tenant detected → Reader[TenantConfig, -]
  - Platform choice → Either[Shopify, WooCommerce]
  - Analysis choice → Either[AI, Manual]
  
  Generated functor:
    Reader[TenantConfig, Either[Platform, Either[AnalysisMode, Products]]]

[Activating: system-optimizer]
Optimizing...
  Factoring common tenant handling...
  Result: 1 tenant handler + 2 platform adapters + 2 analyzers
  Reduction: 4 → 5 components (but reusable)

[Activating: architecture-validator]
Running validation suite...
  ✓ 47/47 tests passed

[Activating: code-generator]
Generating...
  Created: 8 files, 1,247 LOC
```

**Output Structure:**
```
src/
  types.py                  # Platform, AnalysisMode, TenantConfig
  recommendation_service.py # Main service
  tenant_handler.py         # Reader functor
  platform_adapters/
    shopify.py
    woocommerce.py
  analyzers/
    ai_analyzer.py
    manual_analyzer.py
  composition.py            # Service composition
tests/
  test_recommendation.py
  property_tests.py
```

### Example 3: Migration Between Versions

**Request:**
```
We have a v1 API. Create v2 that adds pagination.
Generate a migration path from v1 to v2.
```

**Claude's Execution:**

```
[Activating: natural-transformation-engine]
Analyzing transformation...
  From: V1Response (all products)
  To: V2Response (paginated products)
  
  Natural transformation:
    α: V1Response → V2Response
    
  Naturality check:
    ✓ Transform preserves structure
    ✓ Can convert any v1 response to v2

[Activating: curry-howard-prover]
Proving migration safety...
  Theorem: V1Response → V2Response is total
  Proof: Every v1 response can be converted to v2
  ✓ Proven by construction

[Activating: code-generator]
Generating migration...
```

**Output:**
```python
# migrations/v1_to_v2.py
from typing import List
from dataclasses import dataclass

@dataclass
class V1Response:
    products: List[Product]

@dataclass
class V2Response:
    products: List[Product]
    page: int
    total_pages: int
    has_more: bool

def migrate_v1_to_v2(
    v1_response: V1Response,
    page_size: int = 50
) -> V2Response:
    """
    Natural transformation: V1Response → V2Response
    
    Preserves all products, adds pagination metadata.
    Naturality: Transform commutes with product operations.
    """
    products = v1_response.products
    total = len(products)
    total_pages = (total + page_size - 1) // page_size
    
    return V2Response(
        products=products,
        page=1,
        total_pages=total_pages,
        has_more=total > page_size
    )

# Naturality verification
def test_naturality():
    """
    Verify: fmap f . migrate = migrate . fmap f
    
    Transforming then mapping = Mapping then transforming
    """
    v1 = V1Response(products=[...])
    
    # Path 1: Migrate then map
    v2 = migrate_v1_to_v2(v1)
    mapped1 = fmap(enrich_product, v2)
    
    # Path 2: Map then migrate
    mapped_v1 = fmap(enrich_product, v1)
    mapped2 = migrate_v1_to_v2(mapped_v1)
    
    assert mapped1 == mapped2  # Naturality holds
```

## Interactive Development

### Incremental Building

You can build systems incrementally, skill by skill:

```
> Parse this requirement: "Multi-tenant catalog with Shopify sync"

[Claude uses adt-analyzer]
Expression: Tenant × ShopifySync
Paths: 1

> Now add WooCommerce support

[Claude updates analysis]
Expression: Tenant × (Shopify + WooCommerce)
Paths: 2 (expanded via distributivity)

> Make it async

[Claude uses functor-generator]
Applied Future functor
Result: Future[Tenant × (Shopify + WooCommerce)]

> Generate the code

[Claude uses code-generator]
✓ Generated async multi-tenant service
```

### Refinement Loop

If something isn't right, Claude can refine:

```
> Build a catalog service

[Claude generates code]

> The Shopify adapter is missing error handling

[Claude uses architecture-validator to check, then code-generator to fix]

> Add retry logic with exponential backoff

[Claude uses system-optimizer to add resilience patterns, regenerates]

> Perfect, validate the complete system

[Claude uses architecture-validator]
✓ All laws satisfied
✓ Error handling complete
✓ Retry logic correct
```

## Advanced Patterns

### Pattern 1: Feature Flags

```
> Build a recommendation service with an optional AI feature

[ADT]: Service × (EnableAI + DisableAI)
[Functor]: Maybe[AIService] - optional AI
[NatTrans]: None → Some when feature enabled
[Code]: Feature flag implementation
```

### Pattern 2: A/B Testing

```
> Create two variants of the algorithm for A/B testing

[ADT]: (VariantA + VariantB) × Experiment
[Functor]: Either[VariantA, VariantB]
[Optimizer]: Share common code, specialize differences
[Code]: A/B test harness
```

### Pattern 3: Gradual Rollout

```
> Migrate from sync to async gradually

[NatTrans]: 
  α₁: Sync → Sync + Async (hybrid)
  α₂: Sync + Async → Async (complete)
[Validator]: Both stages proven safe
[Code]: Feature flag for gradual rollout
```

### Pattern 4: Multi-Region Deployment

```
> Deploy to US, EU, and APAC regions

[ADT]: (US + EU + APAC) × Service
[Functor]: Reader[Region, Service]
[Optimizer]: Factor region-specific config
[Code]: Region-aware service
```

## Debugging & Validation

### Check Specific Laws

```
> Validate that the catalog service composition is associative

[Category Theory Foundation]
Testing: (h ∘ g) ∘ f = h ∘ (g ∘ f)

Test case 1: ✓
Test case 2: ✓
Test case 3: ✓

Associativity verified for all test cases.
```

### Verify Functor Laws

```
> Check that the Reader functor satisfies functor laws

[Architecture Validator]
Testing Reader functor...

Law 1: F(id) = id
  ✓ Passed (10 test cases)

Law 2: F(g ∘ f) = F(g) ∘ F(f)
  ✓ Passed (20 test cases)

Reader functor is valid.
```

### Prove Correctness

```
> Prove that all platform types are handled

[Curry-Howard Prover]
Analyzing match statement...

match platform:
    case Shopify: handle_shopify()
    case WooCommerce: handle_woo()

✓ Exhaustive - all constructors matched
✓ Type-safe - each branch returns correct type
✓ Total function - defined for all inputs

Correctness proven by construction.
```

## Performance Optimization

### Request Optimization

```
> Optimize this service for performance

[System Optimizer]
Analyzing algebraic structure...

Found: (Service × PlatformA) + (Service × PlatformB)

Applying distributivity:
  = Service × (PlatformA + PlatformB)

Optimization:
  - Extracted common Service component
  - Parallel platform adapters
  - 2x throughput increase

Would you like me to apply this optimization? (y/n)
```

### Caching Strategy

```
> Add caching to the catalog service

[Functor Generator]
Analyzing: Service[Input, Output]

Applying Reader functor with memoization:
  Reader[Config, Cached[Output]]

Benefits:
  - Automatic cache per config
  - Cache invalidation built-in
  - Type-safe

Generating implementation...
```

## Testing Strategy

### Property-Based Tests

Claude automatically generates property-based tests:

```python
# Generated by code-generator
from hypothesis import given
from hypothesis.strategies import text, integers

@given(text(), integers())
def test_functor_identity(config, value):
    """Property: fmap id = id"""
    service = create_service(config)
    assert service.fmap(identity)(value) == identity(service(value))

@given(text())
def test_functor_composition(config):
    """Property: fmap (g ∘ f) = fmap g ∘ fmap f"""
    f = lambda x: x + 1
    g = lambda x: x * 2
    service = create_service(config)
    
    left = service.fmap(compose(g, f))
    right = compose(service.fmap(g), service.fmap(f))
    
    assert left(10) == right(10)
```

### Integration Tests

```python
# Generated integration tests
def test_end_to_end_shopify():
    """Test complete Shopify sync flow"""
    tenant = TenantConfig(merchant_id="123")
    platform = Platform.Shopify
    credentials = ShopifyCredentials(...)
    
    service = create_catalog_service(tenant, platform)
    products = service.sync(credentials)
    
    assert len(products) > 0
    assert all(isinstance(p, Product) for p in products)

def test_version_migration():
    """Test V1 → V2 migration"""
    v1_response = get_v1_response()
    v2_response = migrate_v1_to_v2(v1_response)
    
    # Verify structure preserved
    assert len(v1_response.products) == len(v2_response.products)
    # Verify pagination added
    assert hasattr(v2_response, 'page')
    assert hasattr(v2_response, 'total_pages')
```

## Common Issues & Solutions

### Issue 1: Type Mismatch

**Symptom:**
```
Error: Cannot compose Service[A, B] with Service[C, D]
Type B does not match type C
```

**Solution:**
```
> Add a transformation from B to C

[Natural Transformation Engine]
Generated: transform_b_to_c: B → C
Now services compose: Service[A, B] → Service[C, D]
```

### Issue 2: Impossible Combination

**Symptom:**
```
Error: Path contains Void type
Auth × DatabaseConnection × Void = Void
```

**Solution:**
```
> Remove the impossible dependency

[ADT Analyzer]
Identifying Void source: MissingCredentials
Recommendation: Make credentials required
Updated: Auth × DatabaseConnection × Credentials
```

### Issue 3: Broken Naturality

**Symptom:**
```
Error: Naturality condition violated
G(f) ∘ α ≠ α ∘ F(f)
```

**Solution:**
```
> Redesign the transformation to preserve structure

[Natural Transformation Engine]
Analyzing transformation...
Issue: Transformation inspects type-specific values
Fix: Make transformation parametric
✓ Naturality restored
```

## Cheat Sheet

### Common Commands

| Task | Command Pattern |
|------|----------------|
| Parse requirements | "Parse: [requirements]" |
| Generate service | "Build service for: [spec]" |
| Add feature | "Add [feature] to [service]" |
| Optimize | "Optimize [service]" |
| Validate | "Validate [service] architecture" |
| Migrate | "Migrate from [v1] to [v2]" |
| Prove correctness | "Prove [service] handles all cases" |

### Quick Reference

```bash
# Start with requirements
> Parse: Multi-tenant catalog with Shopify and WooCommerce

# Check structure
> Validate the specification

# Design transformations
> Generate functors for this design

# Prove correctness
> Prove all platform types are handled

# Optimize
> Optimize using algebraic laws

# Generate code
> Generate production code

# Validate everything
> Run complete validation suite
```

## Next Steps

1. **Install Skills:** Copy skills to `~/.claude/skills/`
2. **Start Simple:** Build a single-path service
3. **Add Complexity:** Add coproducts (choices)
4. **Add Transformations:** Use functors
5. **Validate:** Check all laws
6. **Deploy:** Generate and deploy

The skills will guide you through each step automatically.

## Summary

The 8-skill system provides:

✅ **Automatic Workflow:** Claude orchestrates skills
✅ **Mathematical Guarantees:** Category theory ensures correctness
✅ **Incremental Development:** Build piece by piece
✅ **Self-Validation:** Continuous law checking
✅ **Production Ready:** Generates deployable code
✅ **Optimized:** Algebraic laws enable automatic optimization

Start building with mathematical precision today!