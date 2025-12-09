---
name: observability-standard-definer
description: |
  Define observability standards as categorical structures. Produces metrics definitions,
  distributed tracing, and structured logging patterns. Observability as functors from
  Domain category to Metrics/Trace categories preserving morphism execution.
  Input: categories/*.std.yaml, services.spec.yaml
  Output: standards/observability/*.std.yaml
---

# Observability Standard Definer

Define observability patterns as categorical structures.

## Purpose

Transform operations into observable metrics and traces:
1. Metrics (counters, gauges, histograms)
2. Distributed tracing (spans, context propagation)
3. Structured logging (events, correlation)

## Input

- `standards/categories/*.std.yaml` - Category definitions
- `services.spec.yaml` - Morphisms to observe

## Output

```
standards/observability/
├── metrics.std.yaml   # Metric definitions
├── tracing.std.yaml   # Distributed tracing
└── logging.std.yaml   # Structured logging
```

## Metrics Standard

### Schema

```yaml
# standards/observability/metrics.std.yaml

standard:
  name: Metrics
  description: "Metrics as functor from Domain to Metrics category"

# Metrics functor: Domain → Metrics
functor:
  name: Observe
  source: Domain
  target: MetricsCategory
  
  # Every morphism produces metrics
  morphism_map: |
    For f: A → B in Domain,
    Observe(f) produces:
      - counter: {name}_total
      - histogram: {name}_duration_seconds
      - gauge: {name}_in_progress (optional)

# Metric types
metric_types:
  - name: counter
    description: "Monotonically increasing value"
    operations: [increment, add]
    example: "requests_total"
    
  - name: gauge
    description: "Value that can go up or down"
    operations: [set, increment, decrement]
    example: "active_connections"
    
  - name: histogram
    description: "Distribution of values"
    operations: [observe]
    buckets: [0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1, 2.5, 5, 10]
    example: "request_duration_seconds"
    
  - name: summary
    description: "Quantile observations"
    operations: [observe]
    quantiles: [0.5, 0.9, 0.99]
    example: "request_size_bytes"

# Standard metrics (auto-generated)
standard_metrics:
  # Per morphism
  morphism_metrics:
    - name: "{module}_{operation}_total"
      type: counter
      labels: [status, error_type]
      help: "Total {operation} calls"
      
    - name: "{module}_{operation}_duration_seconds"
      type: histogram
      labels: [status]
      help: "{operation} duration in seconds"
      
    - name: "{module}_{operation}_in_progress"
      type: gauge
      help: "Current in-progress {operation} calls"
      when: long_running  # Only for slow operations
      
  # Per external dependency
  external_metrics:
    - name: "{dependency}_requests_total"
      type: counter
      labels: [method, status, error_type]
      
    - name: "{dependency}_request_duration_seconds"
      type: histogram
      labels: [method]
      
    - name: "{dependency}_circuit_state"
      type: gauge
      labels: [state]  # closed=0, open=1, half_open=2
      
  # System metrics
  system_metrics:
    - name: "process_cpu_seconds_total"
      type: counter
      
    - name: "process_resident_memory_bytes"
      type: gauge
      
    - name: "python_gc_collections_total"
      type: counter
      labels: [generation]

# Metric naming conventions
naming:
  format: "{namespace}_{subsystem}_{name}_{unit}"
  namespace: app  # Application name
  rules:
    - snake_case: true
    - suffix_with_unit: true  # _seconds, _bytes, _total
    - no_type_in_name: true   # No "counter" in name

# Labels
labels:
  standard:
    - service: "Service name"
    - version: "Application version"
    - environment: "dev/staging/prod"
    
  cardinality_limits:
    max_label_values: 100  # Prevent cardinality explosion
    avoid:
      - user_id      # Too many values
      - request_id   # Unique per request
      - timestamp    # Use histogram instead

# Categorical interpretation
categorical:
  # Metrics form a commutative monoid
  monoid:
    name: MetricMonoid
    carrier: Metric
    operation: combine  # Metrics can be combined
    identity: zero_metric
    
  laws:
    - associativity: "combine(combine(a, b), c) = combine(a, combine(b, c))"
    - commutativity: "combine(a, b) = combine(b, a)"
    - identity: "combine(a, zero) = a"
    
  # Functor laws
  functor_laws:
    - "Observe(id) = id"
    - "Observe(g ∘ f) = Observe(g) ∘ Observe(f)"
```

## Tracing Standard

### Schema

```yaml
# standards/observability/tracing.std.yaml

standard:
  name: Tracing
  description: "Distributed tracing as natural transformation"

# Tracing as natural transformation: Domain ⟹ TracedDomain
transformation:
  name: Trace
  source_functor: Domain
  target_functor: TracedDomain
  
  # Every morphism is wrapped with span
  components: |
    For f: A → B,
    Trace(f): TracedA → TracedB
    where TracedX = (X, SpanContext)

# Span structure
span:
  attributes:
    # Required
    - trace_id: "128-bit unique identifier"
    - span_id: "64-bit unique identifier"
    - parent_span_id: "64-bit, optional"
    - operation_name: "Name of the operation"
    - start_time: "Timestamp"
    - end_time: "Timestamp"
    
    # Standard attributes
    - service.name: "Service identifier"
    - service.version: "Service version"
    - deployment.environment: "Environment"
    
    # Status
    - status.code: "OK | ERROR | UNSET"
    - status.message: "Error description if ERROR"
    
  events:
    - name: "Significant points in time"
    - timestamp: "When event occurred"
    - attributes: "Event-specific data"
    
  links:
    - description: "Causal relationships to other spans"
    - trace_id: "Linked trace"
    - span_id: "Linked span"

# Context propagation
propagation:
  format: W3C_TraceContext  # traceparent, tracestate headers
  
  injection: |
    1. Get current span context
    2. Encode as traceparent header
    3. Add to outgoing request
    
  extraction: |
    1. Check for traceparent header
    2. Decode trace_id, span_id, flags
    3. Create child span context

# Span generation rules
span_rules:
  # Per morphism layer
  layers:
    - name: http
      create_span: always
      operation_name: "{method} {path}"
      attributes:
        http.method: "GET, POST, etc."
        http.url: "Full URL"
        http.status_code: "Response code"
        http.request_content_length: "Request size"
        http.response_content_length: "Response size"
        
    - name: repository
      create_span: always
      operation_name: "{operation}"
      attributes:
        db.system: "postgresql"
        db.operation: "SELECT, INSERT, etc."
        db.statement: "SQL query (sanitized)"
        
    - name: external
      create_span: always
      operation_name: "{service}.{operation}"
      attributes:
        http.url: "External URL"
        peer.service: "External service name"

# Sampling
sampling:
  strategy: parent_based  # Follow parent decision
  
  rules:
    - name: always_sample
      condition: "error or slow (> 1s)"
      rate: 1.0
      
    - name: health_checks
      condition: "path matches /health"
      rate: 0.0  # Never sample
      
    - name: default
      condition: "all other"
      rate: 0.1  # 10% sampling

# Categorical interpretation
categorical:
  # Traced morphisms form a category
  traced_category:
    objects: "TracedTypes = Type × SpanContext"
    morphisms: "Traced morphisms producing spans"
    composition: "Child span with parent context"
    
  # Natural transformation
  naturality: |
    For f: A → B,
    Trace_B ∘ Domain(f) = TracedDomain(f) ∘ Trace_A
    
  laws:
    - "Trace preserves composition (parent-child spans)"
    - "Trace preserves identity (no-op span)"
```

## Logging Standard

### Schema

```yaml
# standards/observability/logging.std.yaml

standard:
  name: Logging
  description: "Structured logging as side effect in IO monad"

# Logging as IO side effect
effect:
  type: "IO[Unit]"
  position: "Within morphism execution"
  correlation: "Via trace context"

# Log structure
log_entry:
  required:
    - timestamp: "ISO 8601 format"
    - level: "DEBUG | INFO | WARN | ERROR"
    - message: "Human-readable description"
    - logger: "Logger name (module.function)"
    
  standard_fields:
    - trace_id: "From span context"
    - span_id: "From span context"
    - service: "Service name"
    - environment: "Deployment environment"
    - version: "Application version"
    
  contextual:
    - request_id: "Unique request identifier"
    - user_id: "Authenticated user (if any)"
    - tenant_id: "Tenant identifier"
    - operation: "Current operation name"

# Log levels
levels:
  - name: DEBUG
    value: 10
    use: "Detailed debugging, disabled in production"
    
  - name: INFO
    value: 20
    use: "Normal operation events"
    
  - name: WARN
    value: 30
    use: "Unexpected but handled situations"
    
  - name: ERROR
    value: 40
    use: "Errors requiring attention"

# Logging rules
rules:
  # What to log
  events:
    - morphism_start: INFO
    - morphism_success: INFO
    - morphism_failure: ERROR
    - validation_failure: WARN
    - external_call: DEBUG
    - state_transition: INFO
    
  # What NOT to log
  exclusions:
    - passwords: never
    - tokens: never
    - pii: mask  # Mask personally identifiable info
    - credit_cards: mask
    
  # Formatting
  format:
    type: json  # Structured JSON logs
    pretty: false  # No pretty printing in prod

# Log morphisms
morphisms:
  - name: log_info
    domain: "(Logger, Message, Context)"
    codomain: "IO[Unit]"
    
  - name: log_error
    domain: "(Logger, Error, Context)"
    codomain: "IO[Unit]"
    includes: [stack_trace, error_type]
    
  - name: log_morphism_execution
    domain: "(MorphismName, Duration, Status)"
    codomain: "IO[Unit]"
    auto_generated: true  # Wraps all morphisms

# Correlation
correlation:
  # All logs in a request share trace_id
  strategy: trace_context
  
  propagation: |
    1. Extract trace_id from incoming request
    2. Store in context variable
    3. Include in all log entries
    4. Pass to downstream services

# Categorical interpretation
categorical:
  # Logging as writer monad
  monad:
    name: Writer
    type_constructor: "Writer[W, A] = (A, W)"
    where: "W = List[LogEntry]"
    
    pure: "a ↦ (a, [])"
    bind: "(a, w1).flatMap(f) = let (b, w2) = f(a) in (b, w1 ++ w2)"
    
  # Or as IO effect
  io_effect:
    type: "A → IO[A]"
    semantics: "Execute with logging side effect"
    
  laws:
    - "Logging doesn't affect return value"
    - "Log order matches execution order"
```

## Validation

### Completeness Checks

```yaml
completeness:
  - all_morphisms_have_metrics
  - all_layers_have_spans
  - all_operations_have_logging
  - trace_context_propagated
```

### Consistency Checks

```yaml
consistency:
  - metric_names_follow_convention
  - span_names_match_operations
  - log_levels_appropriate
  - no_pii_in_logs
```

## Next Skills

Output feeds into:
- `configuration-standard-definer`
- `standards-validator`
