# Synthesizing Mode

Integrate multiple signals into coherent picture.

## When to Use

- Have disparate inputs needing unification
- Multiple signals, unclear how they relate
- Need holistic understanding
- Preparing inputs for thinking modes
- Building mental model of situation

## Mental Model

**Jigsaw puzzle:** Assemble individual pieces into a coherent whole. The whole reveals what pieces alone cannot.

## Synthesis Methods

### Weighted Average
Combine quantitative signals by importance.

**Use when:** Signals are quantitative, can assign meaningful weights, need single metric.

**Example:** Customer satisfaction = (Survey score × 0.4) + (NPS × 0.3) + (Support tickets inverse × 0.3)

### Bayesian Update
Update beliefs based on new evidence.

**Use when:** Have prior belief, new evidence arrives, need revised probability.

**Example:** P(competitor launches Q1) updated from 30% to 55% based on hiring signal.

### Narrative
Construct explanatory story from signals.

**Use when:** Signals are qualitative, need to explain "what's happening", audience needs story.

**Example:** "Competitor pivoting to enterprise" explains hiring + funding + office signals.

### Framework
Map signals to structured template.

**Use when:** Have established framework (SWOT, Porter's, etc.), need structured analysis.

**Example:** Map signals to Strengths/Weaknesses/Opportunities/Threats.

## Execution

### Input Collection

For each signal:
- **Signal:** What was observed
- **Source:** Where it came from
- **Quality:** High/Medium/Low reliability
- **Recency:** How current
- **Weight:** Importance (0.0-1.0)

### Finding Connections

Map relationships between signals:

| Signal A | Signal B | Relationship |
|----------|----------|--------------|
| [Signal] | [Signal] | Supports / Contradicts / Independent / Enables |

### Conflict Resolution

For each conflict:
- **Conflict:** [What disagrees]
- **Possible resolutions:** [List explanations]
- **Chosen resolution:** [Most likely explanation]
- **Rationale:** [Why this explanation]

### Coherence Check

**Does synthesis explain all signals?**

| Signal | Explained by synthesis? | How? |
|--------|------------------------|------|
| [Signal] | Yes/No | [Explanation] |

**Unexplained signals:** [Any signals that don't fit]

**Alternative syntheses considered:** [Other interpretations]

## Output Format

```markdown
## Synthesis: [Topic]

**Method:** [Weighted Average / Bayesian / Narrative / Framework]
**Inputs:** [N] signals from [sources]

### Input Signals

| Signal | Source | Quality | Weight |
|--------|--------|---------|--------|
| [Signal 1] | [Source] | [H/M/L] | [0.0-1.0] |
| [Signal 2] | [Source] | [H/M/L] | [0.0-1.0] |

### Connections

**Supporting relationships:**
- [Signal A] supports [Signal B]: [How]

**Contradictions:**
- [Signal A] vs [Signal B]: [Resolution]

### Integrated Picture

**Summary:** [2-3 sentence synthesis]

**Confidence:** [X%] — [Why this confidence level]

**Key components:**
- [Component 1]: [How it contributes to synthesis]
- [Component 2]: [How it contributes]

**Coherence:** [High/Medium/Low] — [Do all signals fit?]

### Gaps and Uncertainty

**Missing information:**
- [Gap]: [Impact on synthesis]

**Unexplained signals:**
- [Signal that doesn't fit]

### Predictions

If this synthesis is correct:
- [Prediction 1] (Confidence: [X%])
- [Prediction 2] (Confidence: [X%])

### Ready for Thinking

**Suggested mode:** [Which rsn-reasoning-problems mode]
**Key input:** [What to feed to thinking]
```

## Quality Gates

| Gate | Requirement |
|------|-------------|
| Input weights justified | Not arbitrary |
| Conflicts resolved or flagged | No hidden contradictions |
| Coherence verified | Synthesis explains signals |
| Predictions made | Testable implications |
| Alternatives considered | Not locked into one view |

## Anti-Patterns

| Avoid | Problem | Do Instead |
|-------|---------|------------|
| Cherry-picking | Ignoring contrary signals | Include all signals |
| Over-weighting recent | Recency bias | Weight by reliability |
| Forcing coherence | False confidence | Acknowledge gaps |
| Single method | May miss patterns | Consider multiple methods |
| No predictions | Untestable synthesis | Make testable predictions |

## Synthesizing → Thinking Handoff

| Synthesis Type | Thinking Mode |
|----------------|---------------|
| Landscape integrated | Inductive (find patterns) |
| Anomaly confirmed | Abductive (diagnose cause) |
| Conflicting views integrated | Dialectical (if still unresolved) |
| Options understood | Counterfactual (evaluate) |
| Situation understood | Causal (plan actions) |
