---
name: resilience-specifier
description: Add resilience patterns to effectful morphisms. Use after effect-analyzer to specify retry strategies, circuit breakers, timeouts, fallbacks, and degradation modes. Critical for external functor reliability. Enriches services.spec.yaml with resilience configuration for IO operations.
---

# Resilience Specifier

Add resilience patterns to IO morphisms. External dependencies fail—this skill ensures graceful handling.

## Input

Requires:
- `artifacts/engineering/v{X}/specifications/services.spec.yaml` (with effects from effect-analyzer)
- `artifacts/engineering/v{X}/specifications/domain-concepts.yaml` (external_dependencies)

## Output

Enrich `artifacts/engineering/v{X}/specifications/services.spec.yaml` with resilience:

```yaml
morphisms:
  - name: morphism_name
    effects:
      io: true
      fallible: true
    
    # NEW: Resilience specification
    resilience:
      timeout:
        duration_ms: 5000
        on_timeout: error | fallback
      
      retry:
        max_attempts: 3
        strategy: exponential | linear | immediate
        backoff_base_ms: 100
        max_backoff_ms: 10000
        retryable_errors:
          - ConnectionError
          - TimeoutError
          - RateLimited
      
      circuit_breaker:
        enabled: true
        failure_threshold: 5
        success_threshold: 2
        half_open_timeout_ms: 30000
        on_open: error | fallback
      
      fallback:
        enabled: true
        strategy: cached | default | degrade
        cached_ttl_ms: 300000
        default_value: null  # Type-specific default
      
      bulkhead:
        max_concurrent: 10
        queue_size: 100
        on_reject: error | fallback
```

## Resilience Patterns

### Timeout

Prevent indefinite waiting:

```yaml
timeout:
  duration_ms: 5000  # 5 seconds
  on_timeout: error  # Fail fast

# For slow operations
timeout:
  duration_ms: 30000  # 30 seconds
  on_timeout: fallback  # Try alternative
  
# Adaptive timeout (adjusts based on latency)
timeout:
  strategy: adaptive
  initial_ms: 5000
  min_ms: 1000
  max_ms: 30000
  adjustment_factor: 1.5  # Increase on success, decrease on timeout
```

**Guidelines:**
- External API: 5-10 seconds
- Database: 1-5 seconds
- AI/ML: 30-60 seconds
- File upload: Based on size

### Retry

Handle transient failures:

```yaml
# Exponential backoff (recommended for APIs)
retry:
  max_attempts: 3
  strategy: exponential
  backoff_base_ms: 100
  max_backoff_ms: 10000
  retryable_errors:
    - ConnectionError
    - TimeoutError
    - RateLimited
    - ServiceUnavailable

# Linear backoff (for rate limits with known window)
retry:
  max_attempts: 5
  strategy: linear
  backoff_base_ms: 1000
  retryable_errors:
    - RateLimited

# Immediate retry (for flaky connections)
retry:
  max_attempts: 2
  strategy: immediate
  retryable_errors:
    - ConnectionError
```

**Retryable vs Non-Retryable:**

| Retryable | Non-Retryable |
|-----------|---------------|
| ConnectionError | ValidationError |
| TimeoutError | NotFoundError |
| RateLimited | AuthenticationError |
| ServiceUnavailable | BusinessRuleViolation |
| InternalServerError (5xx) | BadRequest (4xx) |

### Circuit Breaker

Prevent cascade failures:

```yaml
circuit_breaker:
  enabled: true
  failure_threshold: 5     # Open after 5 failures
  success_threshold: 2     # Close after 2 successes
  half_open_timeout_ms: 30000  # Try again after 30s
  on_open: fallback        # What to do when open

# States:
# CLOSED: Normal operation, counting failures
# OPEN: Failing fast, not calling dependency
# HALF_OPEN: Testing if dependency recovered
```

**State Transitions:**

```
CLOSED ──(failures ≥ threshold)──► OPEN
                                     │
                                     │ (timeout)
                                     ▼
                                  HALF_OPEN
                                     │
              ┌────────────────────┬─┴─┬────────────────────┐
              │                    │   │                    │
              ▼                    │   │                    ▼
(successes ≥ threshold)            │   │          (any failure)
              │                    │   │                    │
              ▼                    │   │                    ▼
           CLOSED                  │   │                  OPEN
```

### Fallback

Provide alternatives when primary fails:

```yaml
# Cached fallback (for read operations)
fallback:
  enabled: true
  strategy: cached
  cached_ttl_ms: 300000  # 5 minute cache

# Default fallback (for optional data)
fallback:
  enabled: true
  strategy: default
  default_value:
    products: []  # Empty list is safe default

# Degraded fallback (reduced functionality)
fallback:
  enabled: true
  strategy: degrade
  degraded_operation: get_cached_recommendations
```

**Fallback Strategies:**

| Strategy | Use When | Example |
|----------|----------|---------|
| cached | Read operations | Products list from cache |
| default | Optional features | Empty recommendations |
| degrade | Core features | Simplified analysis |

### Bulkhead

Limit concurrent operations:

```yaml
bulkhead:
  max_concurrent: 10   # Max parallel calls
  queue_size: 100      # Waiting queue
  on_reject: error     # When queue full

# Per-dependency isolation
bulkheads:
  shopify:
    max_concurrent: 20
    queue_size: 200
  groq:
    max_concurrent: 5
    queue_size: 50
```

### Hedged Requests

Send parallel requests, take fastest (for latency-critical paths):

```yaml
hedging:
  enabled: true
  strategy: parallel | delayed
  
  # Parallel: send N requests immediately
  parallel:
    count: 2
    cancel_on_first: true
    
  # Delayed: send backup after threshold
  delayed:
    delay_ms: 100  # If no response in 100ms, send backup
    max_requests: 3
    
  # Only for idempotent operations
  requires_idempotent: true
```

**Use when:**
- Operation is idempotent
- Latency matters more than cost
- Backend can handle extra load

**Categorical interpretation:**
- Hedging: Coproduct of parallel requests `R₁ + R₂ → first(R₁, R₂)`

### Load Shedding

Drop low-priority requests under load:

```yaml
load_shedding:
  enabled: true
  
  # Priority levels
  priorities:
    - level: critical
      never_shed: true
    - level: high
      shed_threshold: 0.9  # Shed at 90% capacity
    - level: normal
      shed_threshold: 0.7
    - level: low
      shed_threshold: 0.5
      
  # Capacity detection
  capacity:
    metric: queue_depth | latency_p99 | cpu
    threshold: 100  # Depends on metric
    
  # Response when shed
  on_shed: 
    status: 503
    retry_after_ms: 5000
    message: "Service temporarily unavailable"
```

**Priority assignment:**
```yaml
morphisms:
  - name: process_payment
    priority: critical
    
  - name: generate_recommendations
    priority: normal
    
  - name: update_analytics
    priority: low
```

### Backpressure

Propagate overload signals upstream:

```yaml
backpressure:
  enabled: true
  strategy: signal | throttle | buffer
  
  # Signal: Return 429 with retry-after
  signal:
    status: 429
    retry_after_header: true
    
  # Throttle: Slow down acceptance rate
  throttle:
    algorithm: token_bucket | leaky_bucket
    rate: 100  # requests per second
    burst: 20  # allowed burst
    
  # Buffer: Queue with bounded size
  buffer:
    max_size: 1000
    on_full: reject | drop_oldest
    
  # Propagation to callers
  propagate_upstream: true
```

**Categorical interpretation:**
- Backpressure: Natural transformation modifying morphism semantics
- `α: F ⟹ Throttled[F]` where throttled functor adds rate limiting

## Per-Dependency Configuration

Configure based on external dependency characteristics:

```yaml
external_resilience:
  shopify:
    description: "Shopify Admin API"
    rate_limit: "40 requests/second"
    typical_latency_ms: 200
    
    default_timeout: 5000
    default_retry:
      max_attempts: 3
      strategy: exponential
      backoff_base_ms: 100
    circuit_breaker:
      failure_threshold: 10
      half_open_timeout_ms: 60000
    bulkhead:
      max_concurrent: 30

  groq:
    description: "Groq AI API"
    rate_limit: "variable"
    typical_latency_ms: 2000
    
    default_timeout: 30000
    default_retry:
      max_attempts: 2
      strategy: exponential
      backoff_base_ms: 1000
    circuit_breaker:
      failure_threshold: 5
      half_open_timeout_ms: 120000
    bulkhead:
      max_concurrent: 5
    fallback:
      strategy: degrade
      degraded_operation: use_cached_analysis

  database:
    description: "PostgreSQL"
    typical_latency_ms: 10
    
    default_timeout: 5000
    default_retry:
      max_attempts: 2
      strategy: immediate
    circuit_breaker:
      enabled: false  # DB failure is critical
    bulkhead:
      max_concurrent: 50
```

## Morphism Enrichment Examples

```yaml
morphisms:
  # External API call with full resilience
  - name: fetch_shopify_products
    layer: external
    effects:
      io: true
      fallible: true
    errors:
      - ShopifyError
      - TimeoutError
      - RateLimited
    
    resilience:
      timeout:
        duration_ms: 5000
        on_timeout: fallback
      retry:
        max_attempts: 3
        strategy: exponential
        backoff_base_ms: 100
        retryable_errors:
          - TimeoutError
          - RateLimited
          - ConnectionError
      circuit_breaker:
        enabled: true
        failure_threshold: 10
        on_open: fallback
      fallback:
        enabled: true
        strategy: cached
        cached_ttl_ms: 300000
      bulkhead:
        max_concurrent: 20

  # AI service with degradation
  - name: analyze_photo
    layer: external
    effects:
      io: true
      fallible: true
    errors:
      - GroqError
      - TimeoutError
    
    resilience:
      timeout:
        duration_ms: 30000
        on_timeout: error
      retry:
        max_attempts: 2
        strategy: exponential
        backoff_base_ms: 2000
        retryable_errors:
          - TimeoutError
          - ServiceUnavailable
      circuit_breaker:
        enabled: true
        failure_threshold: 5
        on_open: fallback
      fallback:
        enabled: true
        strategy: degrade
        degraded_operation: basic_analysis  # Simpler fallback

  # Database operation (simpler resilience)
  - name: save_merchant
    layer: repository
    effects:
      io: true
      fallible: true
    
    resilience:
      timeout:
        duration_ms: 5000
        on_timeout: error
      retry:
        max_attempts: 2
        strategy: immediate
        retryable_errors:
          - ConnectionError
      # No circuit breaker - DB failure is critical
      # No fallback - must succeed or fail
```

## Degradation Modes

Define graceful degradation:

```yaml
degradation_modes:
  - name: full_service
    description: "All features available"
    availability: 100%
    features: [analysis, recommendations, sync]

  - name: cached_recommendations
    description: "Using cached product data"
    availability: 95%
    features: [analysis, cached_recommendations]
    trigger: shopify_circuit_open

  - name: basic_analysis
    description: "Simplified analysis without AI"
    availability: 80%
    features: [basic_analysis, cached_recommendations]
    trigger: groq_circuit_open

  - name: read_only
    description: "View existing data only"
    availability: 50%
    features: [read_profiles, read_recommendations]
    trigger: database_degraded
```

## Validation Checklist

Before outputting, verify:

- [ ] All IO morphisms have timeout
- [ ] External layer morphisms have retry
- [ ] Retryable errors are correctly classified
- [ ] Circuit breakers configured for external dependencies
- [ ] Fallbacks exist for critical paths
- [ ] Bulkheads prevent resource exhaustion
- [ ] Degradation modes cover failure scenarios

## Categorical Interpretation

Resilience patterns as morphism transformations:

```
# Timeout: A → IO[Either[TimeoutError + E, B]]
timeout(f): A → IO[Either[TimeoutError + E, B]]

# Retry: Kleisli arrow with retry semantics
retry(f): A → IO[Either[E, B]]  # Same signature, different semantics

# Circuit Breaker: State machine morphism
cb(f): A → StateT[CircuitState, IO[Either[CircuitOpen + E, B]]]

# Fallback: Coproduct elimination
fallback(f, g): A → IO[Either[E, B]]
  = f <|> g  # Try f, if fails, try g
```

## Next Skill

Output feeds into:
- **state-machine-extractor** → circuit breaker is a state machine
- **categorical-structure-detector** → resilience patterns have structure
