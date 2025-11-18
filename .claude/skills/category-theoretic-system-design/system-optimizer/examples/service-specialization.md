# Service Specialization via Distributivity

## Problem

Monolithic service handling multiple platforms:

```python
def handle_ecommerce(auth: Auth, platform: Platform) -> Result:
    """
    Single service handling all platforms.

    Type: Auth × (Shopify + WooCommerce + Stripe)

    Problems:
    - Large deployment
    - All platforms bundled
    - Cannot scale platforms independently
    """
    if isinstance(platform, Shopify):
        return handle_shopify_logic(auth, platform)
    elif isinstance(platform, WooCommerce):
        return handle_woocommerce_logic(auth, platform)
    elif isinstance(platform, Stripe):
        return handle_stripe_logic(auth, platform)
```

## Optimization

Apply distributivity law: `a × (b + c) = (a × b) + (a × c)`

```python
from scripts.optimize import optimize, Product, Coproduct, Atom

# Original: Auth × (Shopify + WooCommerce + Stripe)
original = Product([
    Atom("Auth"),
    Coproduct([
        Atom("Shopify"),
        Atom("WooCommerce"),
        Atom("Stripe")
    ])
])

# Apply distributivity
result = optimize(original, rules=['distributivity'])

# Result: (Auth × Shopify) + (Auth × WooCommerce) + (Auth × Stripe)
print(result.optimized)
```

## Optimized Implementation

Three specialized microservices:

```python
# Service 1: Shopify handler
def handle_shopify(auth: Auth, shopify: Shopify) -> Result:
    """
    Type: Auth × Shopify

    - Only Shopify dependencies
    - Smaller deployment
    - Independent scaling
    """
    return handle_shopify_logic(auth, shopify)


# Service 2: WooCommerce handler
def handle_woocommerce(auth: Auth, woocommerce: WooCommerce) -> Result:
    """
    Type: Auth × WooCommerce

    - Only WooCommerce dependencies
    - Independent deployment
    """
    return handle_woocommerce_logic(auth, woocommerce)


# Service 3: Stripe handler
def handle_stripe(auth: Auth, stripe: Stripe) -> Result:
    """
    Type: Auth × Stripe

    - Only Stripe dependencies
    - Can deploy to different regions
    """
    return handle_stripe_logic(auth, stripe)
```

## Benefits

✓ **Smaller deployments**: Each service only includes needed dependencies
✓ **Independent scaling**: Scale Shopify service without affecting others
✓ **Parallel deployment**: Deploy services independently
✓ **Team autonomy**: Different teams can own different services
✓ **Fault isolation**: Shopify issue doesn't affect WooCommerce

## Deployment

```yaml
# Before: One large service
services:
  ecommerce:
    image: ecommerce-monolith:v1
    size: 500MB
    dependencies: [shopify-sdk, woocommerce-sdk, stripe-sdk]

# After: Three specialized services
services:
  shopify-service:
    image: shopify-handler:v1
    size: 150MB
    dependencies: [shopify-sdk]

  woocommerce-service:
    image: woocommerce-handler:v1
    size: 120MB
    dependencies: [woocommerce-sdk]

  stripe-service:
    image: stripe-handler:v1
    size: 100MB
    dependencies: [stripe-sdk]
```

## Verification

Optimization preserves semantics:

```python
# For all auth, platform:
monolithic(auth, platform) = specialized_service(auth, platform)
```

Mathematical proof: Distributivity law guarantees equivalence.
