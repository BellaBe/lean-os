# Abductive Mode

Generate best explanation from observation through competing hypotheses.

## When to Use

- Single anomaly or unexpected outcome occurred
- Need to diagnose root cause
- Something surprising happened
- Question is "Why did this happen?"

## Flow

```
Observation → Hypotheses (≥5) → Evidence Debate → Best Explanation
```

---

## Stage 1: Observation

Quantify the anomaly before explaining it.

**Required elements:**
- **Deviation:** Numeric change (absolute and relative)
- **Timeline:** When started, duration, persistence
- **Scope:** Which segments, systems, users affected
- **Baseline:** Where the expected value comes from

**Example:**

> **Observation:** Enterprise conversion dropped from 15% to 9% (40% relative decline).
> 
> **Timeline:** Started week 5 of Q3, accelerated through Q4.
> 
> **Scope:** Enterprise segment only; SMB conversion stable at 22%.
> 
> **Baseline:** 15% was trailing 6-month average before Q3.

**Gate:** Anomaly must be quantified, not just described. "Conversion dropped" is insufficient. "Conversion dropped 40% (15% → 9%)" is sufficient.

---

## Stage 2: Hypothesis Generation

Generate ≥5 hypotheses across ≥3 categories before evaluating any.

### Standard Categories

| Category | Examples |
|----------|----------|
| **Technical** | Site issues, bugs, performance, integration failures |
| **Product** | Features, pricing, positioning, UX changes |
| **Market** | Competition, trends, seasonality, macro shifts |
| **Operational** | Team changes, process issues, capacity constraints |
| **External** | Economy, regulations, events, platform changes |

### AI System Categories

When diagnosing AI/agent failures, add these:

**By Intelligence Layer:**

| Layer | Hypothesis Type | Example |
|-------|-----------------|---------|
| Representation | Encoding problem | "Tokenization losing semantic boundaries" |
| Generalization | Learning failure | "Model overfit to training artifacts" |
| Reasoning | Recombination failure | "Thin geometry in this domain" |
| Agency | Action failure | "Tool schema mismatch" |

**By System Layer:**

| Layer | Hypothesis Type |
|-------|-----------------|
| Input Sanitation | Malformed input passed through |
| Retrieval | Wrong context retrieved |
| Model Invocation | Wrong model for task |
| Orchestration | CoT failure, tool sequencing |
| Constraint | Guardrail bypass |
| Memory | Stale state, hallucinated memory |
| Evaluation | Metric gaming |
| Monitoring | Distribution shift undetected |

**By Agent Failure Mode:**

| Mode | Hypothesis |
|------|------------|
| Hallucinated Actions | "Agent inventing APIs that don't exist" |
| Infinite Loops | "Missing termination condition" |
| Goal Drift | "Task mutating during execution" |
| Over-Confidence | "Acting without appropriate uncertainty" |

**Example:**

> **H1 (Operational):** AM departures caused relationship gaps.  
> Mechanism: Key AMs left → rapport lost → deals stalled.
> 
> **H2 (External):** Economic uncertainty extending cycles.  
> Mechanism: CFO involvement up → longer approval chains.
> 
> **H3 (Market):** Competitor launched enterprise offering.  
> Mechanism: Prospects evaluating alternatives before committing.
> 
> **H4 (Product):** Missing enterprise features blocking purchases.  
> Mechanism: SSO/audit gaps appearing in requirements.
> 
> **H5 (Operational):** Not a real drop—just elongated cycles.  
> Mechanism: Pipeline value unchanged, timing shifted.

**Gate:** Must have ≥5 hypotheses across ≥3 categories before proceeding.

---

## Stage 3: Evidence Debate

Test each hypothesis against available evidence.

### For each hypothesis, ask:

1. **What would we expect to see if this is true?**
2. **What would contradict this?**
3. **What evidence do we actually have?**

### Scoring dimensions:

| Dimension | Weight | Question |
|-----------|--------|----------|
| Explanatory Power | 30% | Does it explain the full anomaly? |
| Coherence | 25% | Is it consistent with other facts? |
| Simplicity | 20% | Does it avoid unnecessary assumptions? |
| Prior Probability | 15% | How likely was this before the evidence? |
| Testability | 10% | Can we verify or falsify it? |

### Challenge techniques:

- "This doesn't explain [aspect of the anomaly]..."
- "If this were true, we'd also see [X], but we don't..."
- "This assumes [Y], but is that valid?"

**Example:**

> **Testing H1 (AM departures):**
> - Supporting: 60% of drop concentrated in departed AMs' accounts ✓
> - Supporting: Timeline matches—departures Q3, acceleration Q4 ✓
> - Challenge: Doesn't explain why NEW accounts also slowed (15% of drop)
> - Verdict: Explains 85% of effect, not 100%
> 
> **Testing H3 (Competitor):**
> - Check: Win/loss data shows only 3 of 47 losses mentioned competitor
> - That's 6%—noise, not signal
> - Verdict: Ruled out as primary cause
> 
> **Testing H4 (Features):**
> - Check: Zero mentions of SSO/audit in loss reasons
> - Verdict: Ruled out

**Gate:** Each top-3 hypothesis must survive at least one serious challenge.

---

## Stage 4: Best Explanation

Synthesize findings into conclusion.

### Required elements:

1. **Primary cause** with confidence (0-100%)
2. **Mechanism** explaining how cause produces effect
3. **Minority report** if second hypothesis ≥40% confidence
4. **Ruled out** hypotheses with reasons
5. **Remaining uncertainty**
6. **Next steps**

### Output format:

```markdown
## Diagnosis: [Anomaly Name]

**Primary cause ([X]% confidence):** [Explanation in 1-2 sentences]

**Mechanism:** [How cause produces effect]

**Minority view ([Y]% confidence):** [Second hypothesis if ≥40%]
- Revisit if: [Conditions that would change conclusion]

**Ruled out:**
- [H3]: [Evidence that eliminated it]
- [H4]: [Evidence that eliminated it]

**Remaining uncertainty:** [What we still don't know]

**Next steps:**
1. [Immediate action]
2. [Monitoring plan]
```

**Example:**

> ## Diagnosis: Enterprise Conversion Drop
> 
> **Primary cause (72% confidence):** AM departures created relationship gaps, stalling deals in existing accounts.
> 
> **Mechanism:** Key AMs left Q3 → relationship continuity lost → deals in progress stalled → appears as conversion drop in Q4.
> 
> **Minority view (45% confidence):** Economic uncertainty explains slowdown in new accounts (15% of total effect).
> - Revisit if: Recovery doesn't materialize after AM backfill
> 
> **Ruled out:**
> - Competitor: Only 6% of losses mentioned them
> - Missing features: Zero mentions in loss reasons
> 
> **Remaining uncertainty:** Whether elongated cycles will eventually convert or are truly lost.
> 
> **Next steps:**
> 1. Backfill AM positions with enterprise experience
> 2. Re-engage stalled deals with new relationship owners
> 3. Monitor Q1 conversion with weekly tracking

---

## AI System Diagnosis Example

```markdown
## Observation

Agent task completion dropped from 85% to 52% after model upgrade.
- Timeline: Immediate, started with deployment
- Scope: Multi-step tasks only; single-step tasks unaffected
- Baseline: 85% was 30-day average before upgrade

## Hypotheses

**H1 (Reasoning layer):** New model has thinner geometry for tool sequencing.

**H2 (Agency layer):** Tool schemas incompatible with new model's output format.

**H3 (Memory layer):** Context window handling changed, losing mid-task state.

**H4 (Orchestration layer):** CoT prompts were tuned for old model.

**H5 (Representation layer):** Token boundaries different, breaking structured output parsing.

## Evidence Debate

**H1 test:** If geometry is thinner, single-step tasks with same tools should also degrade.
- Finding: Single-step tasks unaffected.
- Verdict: H1 less likely.

**H2 test:** Check tool call logs for format errors.
- Finding: 67% of failures show malformed tool parameters.
- Verdict: H2 supported.

**H4 test:** Review CoT prompts for model-specific assumptions.
- Finding: Prompts reference old model's output structure.
- Verdict: H4 supported, may combine with H2.

## Diagnosis

**Primary cause (68% confidence):** Tool schemas and CoT prompts assume old model's output format (H2 + H4 combined).

**Mechanism:** New model produces valid JSON but with different field ordering and optional field handling → parsing fails → tool calls malformed → multi-step chains break.

**Next steps:**
1. Update tool schemas for new model's output format
2. Revise CoT prompts to be model-agnostic
3. Add output validation layer between model and tool execution
```

---

## Output Format

```markdown
## Diagnosis: [Anomaly Name]

### Observation
**Anomaly:** [Quantified deviation]
**Timeline:** [When started, duration]
**Scope:** [What's affected, what's not]
**Baseline:** [Expected value and source]

### Hypotheses Considered

| # | Hypothesis | Category | Confidence |
|---|------------|----------|------------|
| H1 | [Cause] | [Category] | [%] |
| H2 | [Cause] | [Category] | [%] |
| H3 | [Cause] | [Category] | [%] |

### Evidence Analysis

**H1: [Hypothesis]**
- Supporting: [Evidence for]
- Contradicting: [Evidence against]
- Verdict: [Supported/Weakened/Ruled out]

**H2: [Hypothesis]**
- Supporting: [Evidence for]
- Contradicting: [Evidence against]
- Verdict: [Supported/Weakened/Ruled out]

### Conclusion

**Primary cause ([X]% confidence):** [Explanation in 1-2 sentences]

**Mechanism:** [How cause produces effect]

**Minority view ([Y]% confidence):** [Second hypothesis if ≥40%]
- Revisit if: [Conditions that would change conclusion]

### Ruled Out
- **[H3]:** [Evidence that eliminated it]

### Remaining Uncertainty
- [What we still don't know]

### Next Steps
1. [Immediate action]
2. [Monitoring plan]
```

---

## Quality Gates

| Stage | Gate |
|-------|------|
| Observation | Quantified deviation with timeline and scope |
| Hypotheses | ≥5 across ≥3 categories |
| Evidence | Each top-3 survives ≥1 challenge |
| Conclusion | Minority report if #2 ≥40% confidence |

## Anti-Patterns

| Avoid | Do Instead |
|-------|------------|
| Single hypothesis | Generate ≥5 before evaluating |
| Same category | Require ≥3 categories |
| Confirming favorite | Challenge the leading hypothesis hardest |
| Ignoring minority | Include if confidence ≥40% |
| "It's obvious" | Require evidence for conclusion |
| Blaming wrong layer | Check representation before reasoning |
