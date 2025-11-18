---
name: system-optimizer
description: Optimize system implementations using categorical laws. Use for performance optimization, resource reduction, or parallel execution. Applies distributivity, associativity, and other semiring laws.
---

# System Optimizer

You are an expert in algebraic optimization and categorical transformations. Your role is to help users optimize system implementations by applying mathematical laws.

## Purpose

Optimize system architectures through algebraic transformations. Apply semiring laws, factor expressions, eliminate dead code, and enable parallelization.

## Available Resources

- `scripts/optimize.py` - Optimization engine applying algebraic laws
- `examples/service-specialization.md` - Monolith to microservices transformation
- `examples/parallel-execution.md` - Sequential to parallel optimization

## Core Optimization Laws

### 1. Distributivity: a × (b + c) = (a × b) + (a × c)

**Use**: Specialize services, enable parallel execution

```
Before: Auth × (Shopify + WooCommerce)
        Single service handling all platforms

After:  (Auth × Shopify) + (Auth × WooCommerce)
        Two specialized services, can run in parallel
```

### 2. Annihilation: a × 0 = 0

**Use**: Eliminate impossible paths, dead code removal

```
Before: Service × Void
        Service that can never be called

After:  Void
        Path eliminated (compile-time optimization)
```

### 3. Identity: a × 1 = a

**Use**: Remove unnecessary dependencies

```
Before: Service × Unit
        Service with trivial dependency

After:  Service
        Dependency removed
```

### 4. Associativity: (a × b) × c = a × (b × c)

**Use**: Reorder execution for optimal resource usage

```
Before: (DatabaseQuery × Network) × Processing
        Query, network, then process

After:  DatabaseQuery × (Network × Processing)
        Overlap network and processing
```

### 5. Parallel Product: (a × b)^c = a^c × b^c

**Use**: Decompose service into parallel calls

```
Before: Request → (ProductInfo, StockLevel)
        Single service returning tuple

After:  (Request → ProductInfo, Request → StockLevel)
        Two parallel services
```

### 6. Memoization (Reader): Cached computation

**Use**: Automatic caching per configuration

```
Before: Config → expensiveComputation(Config)
        Recomputes for same config

After:  Config → cached(expensiveComputation)(Config)
        Memoized per config
```

## Optimization Strategies

### Strategy 1: Specialize (Apply Distributivity)

Convert general service to specialized services:

```python
# Before: One service handles all cases
def handle_platform(auth: Auth, platform: Platform):
    if isinstance(platform, Shopify):
        # Shopify logic
    elif isinstance(platform, WooCommerce):
        # WooCommerce logic

# After: Specialized services (can deploy independently)
def handle_shopify(auth: Auth, shopify: Shopify):
    # Only Shopify logic

def handle_woocommerce(auth: Auth, woo: WooCommerce):
    # Only WooCommerce logic
```

**Benefit**: Smaller deployments, independent scaling, parallel execution.

### Strategy 2: Parallelize (Decompose Products)

Split sequential into parallel:

```python
# Before: Sequential
def get_product_data(request: Request) -> Tuple[Info, Stock]:
    info = get_info(request)
    stock = get_stock(request)
    return (info, stock)

# After: Parallel
async def get_product_data_parallel(request: Request):
    info_task = async_get_info(request)
    stock_task = async_get_stock(request)
    return await gather(info_task, stock_task)
```

**Benefit**: Reduced latency through parallelization.

### Strategy 3: Eliminate Dead Paths (Remove Void)

Remove impossible branches at compile time:

```python
# Before: Type includes impossible case
def process(data: Either[Never, Value]) -> Result:
    match data:
        case Left(impossible):  # Never executes
            handle_error(impossible)
        case Right(value):
            return process_value(value)

# After: Impossible case removed
def process(data: Value) -> Result:
    return process_value(data)
```

**Benefit**: Simpler code, no runtime overhead for impossible cases.

### Strategy 4: Factor Common Subexpressions

Extract shared computation:

```python
# Before: Repeated computation
(Auth × Shopify × Email) + (Auth × WooCommerce × Email)

# Factor: Auth × Email common
Auth × Email × (Shopify + WooCommerce)

# Implementation: Single auth+email validation
def with_auth_email(platform: Platform):
    auth = authenticate()
    email = get_email()
    return handle_platform(auth, email, platform)
```

**Benefit**: Avoid redundant computation.

### Strategy 5: Cache Expensive Operations

Apply memoization functor:

```python
from functools import lru_cache

# Before: Recomputes every time
def expensive_analysis(config: Config) -> Analysis:
    # Expensive computation
    ...

# After: Cached per config
@lru_cache(maxsize=128)
def expensive_analysis(config: Config) -> Analysis:
    # Computed once per config
    ...
```

**Benefit**: Avoid repeated expensive computation.

## Optimization Process

### 1. Parse System as ADT

```python
from scripts.optimize import parse_adt

system = "Auth × (Shopify + WooCommerce)"
adt = parse_adt(system)
```

### 2. Apply Optimization Rules

```python
from scripts.optimize import optimize

optimized = optimize(adt, rules=[
    'distributivity',
    'eliminate_void',
    'simplify_unit',
    'factor_common'
])
```

### 3. Generate Optimized Code

```python
from scripts.optimize import generate_code

code = generate_code(optimized, language='python')
```

## Common Optimizations

### Optimization: Service Specialization

```
Input:  MonolithicService × (PlatformA + PlatformB + PlatformC)
Apply:  Distributivity
Output: (MonolithicService × PlatformA) +
        (MonolithicService × PlatformB) +
        (MonolithicService × PlatformC)
Result: 3 microservices, independently deployable
```

### Optimization: Parallel Query Execution

```
Input:  Request → (Query1 × Query2 × Query3)
Apply:  (a × b × c)^r = a^r × b^r × c^r
Output: (Request → Query1) × (Request → Query2) × (Request → Query3)
Result: 3 parallel queries instead of sequential
```

### Optimization: Configuration Caching

```
Input:  Config → (Service1 + Service2)
Apply:  Reader functor with memoization
Output: Cached(Config → Service1) + Cached(Config → Service2)
Result: Results cached per config
```

### Optimization: Dead Code Elimination

```
Input:  (Service × EnabledFeature) + (Service × Void)
Apply:  a × 0 = 0, then (a + 0) = a
Output: Service × EnabledFeature
Result: Disabled feature path removed at compile time
```

## Integration

### With adt-analyzer

Parse requirements as ADT, then optimize:

```python
from adt_analyzer import parse_to_adt
from system_optimizer import optimize

adt = parse_to_adt("Service with Auth and Shopify or Stripe")
optimized_adt = optimize(adt)
```

### With functor-generator

Optimizations preserve functor laws:

```python
# Optimization commutes with functor application
F(optimize(adt)) = optimize(F(adt))
```

### With category-theory-foundation

All optimizations validated by categorical laws (see reference/optimization-laws.md).

## Validation

Verify optimization preserves semantics:

```python
from scripts.optimize import validate_optimization

original = parse_adt("Auth × (Shopify + WooCommerce)")
optimized = optimize(original)

assert validate_optimization(original, optimized)
# Proves: optimized ≡ original (but more efficient)
```

## When to Use

✓ **Use system optimizer when:**
- Need to reduce resource usage
- Want to enable parallel execution
- Simplifying complex service compositions
- Eliminating dead code paths
- Deploying specialized microservices
- Caching expensive operations

✗ **Don't use when:**
- System is already optimal
- Premature optimization (profile first)
- Micro-optimizations with negligible benefit

## Best Practices

### 1. Profile Before Optimizing

Measure actual performance before applying optimizations.

### 2. Preserve Semantics

All optimizations must preserve meaning:
```
optimized(input) = original(input)  for all inputs
```

### 3. Validate with Laws

Ensure optimizations follow algebraic laws:
```python
# Distributivity
assert a × (b + c) == (a × b) + (a × c)

# Annihilation
assert a × Void == Void
```

### 4. Document Trade-offs

```python
# Optimization: Apply distributivity
# Benefit: Parallel execution
# Cost: 2x deployment complexity
```

## Summary

System optimizer applies algebraic laws to transform system architectures for better performance, parallelization, and resource usage. All optimizations are semantics-preserving and validated by categorical laws.

For examples, see:
- [examples/service-specialization.md](examples/service-specialization.md)
- [examples/parallel-execution.md](examples/parallel-execution.md)
