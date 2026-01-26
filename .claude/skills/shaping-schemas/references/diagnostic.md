# Diagnostic Schema Reference

Explain why a problem occurred through structured root cause analysis.

## When to Use

Use diagnostic schema when output is:
- Root cause analysis
- Failure investigation
- Bug explanation
- Why something happened

**Required:** Pair with thinking-modes.abductive for reasoning.

## Output Structure

```yaml
diagnostic:
  title: string
  date: date
  severity: critical | high | medium | low
  
  symptoms:
    - symptom: string
      observed: string
      expected: string
      first_detected: datetime
      
  scope:
    affected: [string]
    unaffected: [string]
    timeline: string
    impact: string
    
  hypotheses:
    - id: string
      cause: string
      mechanism: string
      evidence_for: [string]
      evidence_against: [string]
      confidence: float
      
  conclusion:
    primary_cause: string
    confidence: float
    mechanism: string
    contributing_factors: [string]
    
  ruled_out:
    - hypothesis: string
      reason: string
      
  data_gaps:
    - gap: string
      would_clarify: string
      how_to_obtain: string
      
  # Note: NO fixes—use prescriptive schema for that
```

## Construction Process

### Step 1: Document Symptoms

What was observed vs expected?

```yaml
symptoms:
  - symptom: "API response time"
    observed: "2500ms p95"
    expected: "200ms p95"
    first_detected: "2024-01-15T14:30:00Z"
    
  - symptom: "Error rate"
    observed: "15% of requests"
    expected: "<0.1%"
    first_detected: "2024-01-15T14:32:00Z"
```

**Rule:** Quantify symptoms. Not "slow" but "2500ms vs 200ms expected."

### Step 2: Define Scope

What's affected and what's not?

```yaml
scope:
  affected:
    - "API endpoints /users/*"
    - "All regions"
    - "All customer tiers"
    
  unaffected:
    - "Static assets"
    - "Authentication service"
    - "Background jobs"
    
  timeline: "Started 14:30, ongoing at time of analysis"
  impact: "~5000 users experiencing degraded service"
```

**Rule:** "Unaffected" is as important as "affected" for diagnosis.

### Step 3: Generate Hypotheses

Use thinking-modes.abductive. Minimum 3 hypotheses:

```yaml
hypotheses:
  - id: H1
    cause: "Database connection pool exhausted"
    mechanism: "Queries queuing, waiting for connections"
    evidence_for:
      - "DB connection count at max (100)"
      - "Query queue depth increasing"
    evidence_against:
      - "DB CPU and memory normal"
    confidence: 0.75
    
  - id: H2
    cause: "Upstream service degradation"
    mechanism: "Waiting on slow external calls"
    evidence_for:
      - "External service latency up 10x"
    evidence_against:
      - "Only 20% of requests call external service"
    confidence: 0.40
    
  - id: H3
    cause: "Memory leak in application"
    mechanism: "GC pauses causing latency spikes"
    evidence_for:
      - "Heap usage trending up"
    evidence_against:
      - "No GC pause events in logs"
      - "Started suddenly, not gradually"
    confidence: 0.20
```

### Step 4: State Conclusion

What's the primary cause?

```yaml
conclusion:
  primary_cause: "Database connection pool exhausted"
  confidence: 0.75
  mechanism: "Traffic spike exceeded pool capacity. Queries queued
             waiting for connections. Timeout cascade caused errors."
  contributing_factors:
    - "Pool size not scaled with traffic growth"
    - "No connection pool monitoring alert"
```

**Rule:** State confidence. If <0.6, flag as uncertain.

### Step 5: Document Ruled Out

What did we eliminate and why?

```yaml
ruled_out:
  - hypothesis: "Memory leak (H3)"
    reason: "No GC pauses, sudden onset not gradual"
    
  - hypothesis: "Network partition"
    reason: "All regions affected equally, no network errors"
```

### Step 6: Identify Data Gaps

What would help but we don't have?

```yaml
data_gaps:
  - gap: "Historical connection pool metrics"
    would_clarify: "Whether this has been building over time"
    how_to_obtain: "Enable pool metrics export to monitoring"
    
  - gap: "Query-level timing breakdown"
    would_clarify: "Which queries are slow"
    how_to_obtain: "Enable query tracing"
```

## Complete Example

```yaml
diagnostic:
  title: "API Latency Incident - January 15, 2024"
  date: "2024-01-15"
  severity: high
  
  symptoms:
    - symptom: "API p95 latency"
      observed: "2500ms"
      expected: "200ms"
      first_detected: "2024-01-15T14:30:00Z"
      
    - symptom: "Error rate"
      observed: "15%"
      expected: "<0.1%"
      first_detected: "2024-01-15T14:32:00Z"
      
  scope:
    affected:
      - "All /users/* endpoints"
      - "All regions"
    unaffected:
      - "Static assets"
      - "Auth service"
    timeline: "14:30 - 15:45 (75 minutes)"
    impact: "~5000 users, degraded experience"
    
  hypotheses:
    - id: H1
      cause: "Database connection pool exhausted"
      mechanism: "Traffic exceeded pool, queries queued"
      evidence_for:
        - "Pool at max (100 connections)"
        - "Query queue depth 500+"
      evidence_against:
        - "DB resources (CPU/mem) normal"
      confidence: 0.75
      
    - id: H2
      cause: "Upstream service slow"
      mechanism: "External API calls blocking"
      evidence_for:
        - "External service 10x slower"
      evidence_against:
        - "Only 20% requests use external"
        - "Timing doesn't match"
      confidence: 0.40
      
    - id: H3
      cause: "Application memory leak"
      mechanism: "GC pauses causing spikes"
      evidence_for:
        - "Heap trending up"
      evidence_against:
        - "No GC pause events"
        - "Sudden onset"
      confidence: 0.20
      
  conclusion:
    primary_cause: "Database connection pool exhaustion"
    confidence: 0.75
    mechanism: "Marketing campaign drove 3x traffic. Pool sized
               for normal load. Queries queued, timeouts cascaded."
    contributing_factors:
      - "Pool not scaled with growth"
      - "No pool utilization alerting"
      - "No traffic forecasting from marketing"
      
  ruled_out:
    - hypothesis: "Memory leak (H3)"
      reason: "No GC evidence, sudden not gradual"
    - hypothesis: "Network issues"
      reason: "All regions equal, no network errors"
      
  data_gaps:
    - gap: "Pool metrics history"
      would_clarify: "Trend over time"
      how_to_obtain: "Add monitoring export"
```

## Quality Gates

| Gate | Requirement |
|------|-------------|
| Symptoms quantified | Numbers, not adjectives |
| Scope includes unaffected | What's NOT broken matters |
| Multiple hypotheses | ≥3 considered |
| Evidence both ways | For AND against each |
| Confidence stated | Numeric with threshold |
| No fixes included | Diagnostic only explains why |

## Anti-Patterns

| Avoid | Do Instead |
|-------|------------|
| "It was slow" | "2500ms vs 200ms expected" |
| Single hypothesis | Generate ≥3 before evaluating |
| Only confirming evidence | Include contradicting evidence |
| Including fixes | Separate diagnostic from prescriptive |
| Certainty without evidence | State confidence honestly |
