# Parallel Execution via Product Decomposition

## Problem

Sequential data fetching:

```python
def get_product_page(request: Request) -> ProductPage:
    """
    Type: Request → (ProductInfo × StockLevel × Reviews)

    Sequential execution:
    1. Get product info (200ms)
    2. Get stock level (150ms)
    3. Get reviews (300ms)

    Total: 650ms
    """
    info = fetch_product_info(request)
    stock = fetch_stock_level(request)
    reviews = fetch_reviews(request)

    return ProductPage(info, stock, reviews)
```

## Optimization

Apply product decomposition: `(a × b × c)^r = a^r × b^r × c^r`

Transforms sequential tuple into parallel functions.

```python
# Before: Request → (Info × Stock × Reviews)
# Sequential - must complete in order

# After: (Request → Info) × (Request → Stock) × (Request → Reviews)
# Parallel - can execute concurrently
```

## Optimized Implementation

```python
import asyncio

async def get_product_page_parallel(request: Request) -> ProductPage:
    """
    Type: (Request → Info) × (Request → Stock) × (Request → Reviews)

    Parallel execution:
    - All three queries start simultaneously
    - Wait for all to complete
    - Total time: max(200ms, 150ms, 300ms) = 300ms

    Speedup: 650ms → 300ms (2.2x faster!)
    """
    # Launch all queries in parallel
    info_task = asyncio.create_task(fetch_product_info_async(request))
    stock_task = asyncio.create_task(fetch_stock_level_async(request))
    reviews_task = asyncio.create_task(fetch_reviews_async(request))

    # Wait for all to complete
    info, stock, reviews = await asyncio.gather(
        info_task,
        stock_task,
        reviews_task
    )

    return ProductPage(info, stock, reviews)
```

## Mathematical Justification

**Law**: `(a × b)^c = a^c × b^c`

Proof:
```
(a × b)^c means: c → (a × b)
               = Function taking c, returning tuple

a^c × b^c means: (c → a) × (c → b)
               = Two functions, each taking c

These are isomorphic (equivalent):
- Forward: λf. (λx. fst(f(x)), λx. snd(f(x)))
- Backward: λ(g,h). λx. (g(x), h(x))
```

## Benefits

✓ **Reduced latency**: 2.2x faster (650ms → 300ms)
✓ **Better resource usage**: Network/CPU utilized concurrently
✓ **Scalability**: Each query can scale independently
✓ **Fault tolerance**: One slow query doesn't block others (with timeouts)

## Load Testing

```
Before (Sequential):
  Throughput: 150 req/sec
  P95 latency: 700ms

After (Parallel):
  Throughput: 330 req/sec (2.2x improvement)
  P95 latency: 350ms (2x improvement)
```

## Implementation Patterns

### Pattern 1: Full Parallelization

```python
# All independent queries in parallel
results = await asyncio.gather(
    query1(request),
    query2(request),
    query3(request)
)
```

### Pattern 2: Partial Dependencies

```python
# Some queries depend on others
user = await get_user(request)

# These can be parallel (both need user)
preferences, history = await asyncio.gather(
    get_preferences(user),
    get_history(user)
)
```

### Pattern 3: Waterfall with Parallelization

```python
# Stage 1: Get user
user = await get_user(request)

# Stage 2: Parallel queries (depend on user)
profile, orders, wishlist = await asyncio.gather(
    get_profile(user),
    get_orders(user),
    get_wishlist(user)
)

# Stage 3: Combine results
return combine(profile, orders, wishlist)
```

## Verification

Optimization preserves semantics:

```python
# For all requests:
sequential(request) = parallel(request)

# But parallel is faster:
time(parallel) < time(sequential)
```

Mathematical proof: Product decomposition law guarantees equivalence.
