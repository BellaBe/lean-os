# Abductive Mode Reference

Generate best explanation from observation through competing hypothesis voices.

## When to Use

Use abductive mode when:
- Single anomaly or unexpected outcome occurred
- Need to diagnose root cause
- Something surprising happened
- The question is "Why did this happen?"

## Required Personas

| Persona | Role | Traits |
|---------|------|--------|
| **Explorer** | Generates hypotheses | E:4, A:3, C:5, N:3, O:5 |
| **Challenger** | Attacks each hypothesis | E:3, A:2, C:5, N:4, O:3 |
| **Integrator** | Synthesizes conclusion | E:3, A:4, C:5, N:3, O:4 |

## Execution Flow

```
Stage 1: Observation
    ↓
Stage 2: Hypothesis Generation (≥5)
    ↓
Stage 3: Evidence Debate
    ↓
Stage 4: Best Explanation + Minority Report
```

## Stage Instructions

### Stage 1: Observation

**All personas confirm:**
1. Quantify the deviation (% change, sigma from mean)
2. Identify temporal boundaries (when did it start?)
3. Scope the phenomenon (which segments affected?)
4. Rate surprise level (0.0-1.0)

**Output:**
```yaml
observation:
  anomaly: "[Quantified statement of deviation]"
  deviation: "[Numeric change - absolute and relative]"
  temporal: "[When started, duration, persistence]"
  scope: "[Which segments, systems, users affected]"
  surprise: 0.0-1.0
  baseline_source: "[Where baseline comes from]"
```

**Gate:** Anomaly must be quantified, not just described.

---

### Stage 2: Hypothesis Generation

**Explorer generates ≥5 hypotheses across ≥3 categories:**

Categories:
- **Technical**: Site issues, bugs, performance
- **Product**: Features, pricing, positioning
- **Market**: Competition, trends, seasonality
- **Operational**: Team changes, process issues
- **External**: Economy, regulations, events

**For each hypothesis, Explorer states:**
```yaml
hypothesis:
  id: H1
  cause: "[Brief causal claim]"
  category: technical | product | market | operational | external
  mechanism: "[How this cause produces the effect]"
  initial_confidence: 0.0-1.0
```

**Challenger immediately probes each:**
- "Wait, H1 doesn't explain [aspect]..."
- "But if H2 were true, we'd also see [X]..."
- "H3 assumes [Y], but is that valid?"

**Output:**
```xml
<think_explorer>
  H1 (operational): AM departures caused relationship gaps.
  Mechanism: Key AMs left → rapport lost → deals stalled.
  
  H2 (external): Economic uncertainty extending cycles.
  Mechanism: CFO involvement up → longer approvals.
  
  H3 (market): Competitor launched enterprise offering.
  Mechanism: Prospects diverted to competitor evaluation.
  
  H4 (product): Missing enterprise features.
  Mechanism: SSO/audit gaps blocking purchase decisions.
  
  H5 (operational): Not a real drop—just longer cycles.
  Mechanism: Pipeline value unchanged, timing shifted.
</think_explorer>

<think_challenger>
  Wait, H1 only explains existing accounts. What about new accounts?
  H3 needs evidence—did we actually lose deals to competitor?
  H4 is testable—check win/loss for feature mentions.
</think_challenger>
```

**Gate:** Must have ≥5 hypotheses across ≥3 categories before proceeding.

---

### Stage 3: Evidence Debate

**Each hypothesis voice argues its case:**

**Explorer advocates for each hypothesis:**
- Present supporting evidence
- Cite specific data points
- Explain mechanism

**Challenger attacks each hypothesis:**
- "But that doesn't explain [X]..."
- "The data actually shows [Y]..."
- "If that were true, we'd see [Z]..."

**Required discourse markers:**
- "Wait..." (challenge)
- "Actually..." (correction)
- "Good point, but..." (partial concession)
- "Let me check..." (verification)

**Scoring during debate:**
```yaml
evidence_tracker:
  H1:
    supporting:
      - claim: "[Evidence for]"
        strength: 0.0-1.0
    contradicting:
      - claim: "[Evidence against]"
        strength: 0.0-1.0
    net_score: float
```

**Scoring Formula:**
```
Score(H) = (Explanatory × 0.30) + 
           (Simplicity × 0.20) + 
           (Coherence × 0.25) + 
           (Testability × 0.10) + 
           (Prior × 0.15)
```

**Example debate:**
```xml
<think_explorer>
  Supporting H1 (AM departures):
  - Departed AMs' accounts show 60% of total drop
  - Timeline matches: departures Q3, acceleration Q4
  - Relationship-heavy deals most affected
</think_explorer>

<think_challenger>
  But H1 doesn't explain why NEW accounts also slowed.
  AM departures only affect existing relationships.
  New account velocity dropped 15%—what explains that?
</think_challenger>

<think_explorer>
  Good point. Let me check H2 (economic)...
  Economic factors would affect both new and existing.
  Maybe H1 + H2 combined?
</think_explorer>

<think_challenger>
  Actually, that makes sense. H1 explains 85% (existing),
  H2 explains 15% (new accounts). Let me verify...
  
  For H3 (competitor): Only 3 of 47 losses mentioned competitor.
  That's 6%—noise, not signal. Ruling out H3.
</think_challenger>
```

**Gate:** Each top-3 hypothesis must survive ≥1 challenge.

---

### Stage 4: Best Explanation + Minority Report

**Integrator synthesizes:**

1. Rank hypotheses by final score
2. State primary cause with confidence
3. If #2 hypothesis has confidence ≥0.4, include minority report
4. List ruled-out hypotheses with reasons
5. Identify remaining uncertainty
6. Specify next steps

**Output:**
```yaml
conclusion:
  primary_cause: "[Most likely explanation]"
  confidence: 0.0-1.0
  mechanism: "[How cause produces effect]"
  
  minority_report:  # Include if #2 confidence ≥0.4
    cause: "[Second hypothesis]"
    confidence: 0.0-1.0
    advocate_argument: "[Why this might be right]"
    revisit_if:
      - "[Conditions to reconsider]"
      
  ruled_out:
    - hypothesis: "H3"
      reason: "[Evidence that eliminated it]"
      
  remaining_uncertainty:
    - "[What we still don't know]"
    
  next_steps:
    - "[Immediate action]"
    - "[Monitoring plan]"
```

**Gate:** Minority report required if second hypothesis confidence ≥0.4.

## Complete Conversation Example

```xml
<personas>
  <explorer traits="E:4,A:3,C:5,N:3,O:5">
    Creative, generates possibilities, sees connections
  </explorer>
  <challenger traits="E:3,A:2,C:5,N:4,O:3">
    Skeptical, finds flaws, demands evidence
  </challenger>
  <integrator traits="E:3,A:4,C:5,N:3,O:4">
    Balanced, synthesizes views, finds resolution
  </integrator>
</personas>

<observation>
  Anomaly: Enterprise conversion dropped 40% (15% → 9%)
  Temporal: Started week 5 of Q3, accelerated Q4
  Scope: Enterprise only, SMB stable
  Surprise: 0.85
</observation>

<think_explorer>
  Generating hypotheses...
  
  H1 (operational): AM departures—2 key AMs left Q3
  H2 (external): Economic uncertainty—CFO involvement up
  H3 (market): Competitor enterprise launch
  H4 (product): Missing enterprise features
  H5 (operational): Cycle elongation, not real drop
</think_explorer>

<think_challenger>
  Wait, let me stress-test each...
  
  H1: Only explains existing accounts. New accounts?
  H2: If economic, why is SMB stable?
  H3: Need win/loss data on competitor mentions
  H4: Check if features appear in loss reasons
  H5: Pipeline value data needed
</think_challenger>

<think_explorer>
  Good challenges. Let me check data...
  
  H1 evidence: 60% of drop in departed AM accounts ✓
  H5 evidence: Cycle +45 days, pipeline value stable ✓
  
  These could be related—AM loss → stalls → longer cycles
</think_explorer>

<think_challenger>
  Actually, that's a coherent combined mechanism.
  
  For H3: Checked win/loss—only 6% mention competitor.
  Ruling out H3 as primary cause.
  
  For H4: Zero mentions of SSO/audit in loss reasons.
  Ruling out H4.
</think_challenger>

<think_integrator>
  Synthesizing the debate:
  
  Primary: H1 + H5 combined (AM departures → cycle elongation)
  Confidence: 0.72
  Mechanism: AMs left → relationship gaps → deals stalled → 
             appears as longer cycles
  
  Minority report (H2):
  Economic factors explain new account slowdown (15% of effect)
  Confidence: 0.45
  Revisit if: Recovery doesn't materialize with AM backfill
  
  Ruled out: H3 (6%), H4 (0%)
  
  Next: Backfill AMs, monitor Q1 conversion
</think_integrator>
```

## Quality Gates Summary

| Stage | Gate |
|-------|------|
| Observation | Quantified deviation |
| Hypotheses | ≥5 across ≥3 categories |
| Debate | Each top-3 survives ≥1 challenge |
| Conclusion | Minority report if #2 ≥0.4 confidence |

## Anti-Patterns

| Avoid | Do Instead |
|-------|------------|
| Single hypothesis | Generate ≥5 before evaluating |
| Same category | Require ≥3 categories |
| Confirming favorite | Challenger must attack leader |
| Ignoring minority | Include if confidence ≥0.4 |
| "It's obvious" | Require evidence for conclusion |
