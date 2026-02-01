# Experimentation

Test belief through deliberate action before commitment.

## When to Use

- Belief needs validation before major commitment
- Multiple options, unclear which is best
- Cost of being wrong is high
- Learning value justifies experiment cost
- Conditions allow controlled test

## Mental Model

**Scientific method applied to operational decisions.**

Hypothesis → Design → Execute → Analyze → Conclude → Act

## Experiment Types

### A/B Test
Compare two treatments with random assignment.

**Use when:** Clear options, can randomize, need statistical rigor

**Example:** Social proof vs no social proof on pricing page

### Pilot
Test new approach with subset, compare to historical baseline.

**Use when:** Can't randomize, have good baseline data

**Example:** New onboarding flow for 10% of users

### Probe
Exploratory investigation, less controlled.

**Use when:** Exploratory, qualitative insights needed

**Example:** Customer interviews about willingness to pay

### Rollback Test
Deploy change, then revert, compare metrics.

**Use when:** Testing reversibility, measuring impact of existing feature

**Example:** Remove feature, measure impact, re-enable

## Process

### 1. Formulate Hypothesis

Create a testable statement.

**Good hypothesis:**
- Specific (what exactly are we testing?)
- Measurable (how will we know?)
- Falsifiable (can it be proven wrong?)
- Actionable (what changes if true/false?)

**Template:** "If we [do X], then [Y will happen], because [Z]"

**Define:**
- If true: What action do we take?
- If false: What action do we take?

### 2. Design Experiment

Plan how to test fairly.

**Identify variables:**
- Independent: What we're changing
- Dependent: What we're measuring
- Controlled: What we're holding constant

**Determine:**
- Sample size (use power analysis)
- Duration (long enough for effect)
- Success threshold (minimum detectable effect)
- Stopping rules (when to stop early)

### 3. Execute Experiment

Run the test without interference.

**Rules:**
- Don't peek at results early
- Don't change the experiment mid-stream
- Document any anomalies
- Collect all specified data

### 4. Analyze Results

Interpret what happened.

**Quantitative:**
- Calculate metrics for each group
- Compute statistical significance
- Check for confounds

**Qualitative:**
- Note observations
- Document unexpected findings

### 5. Conclude

Determine hypothesis status.

**Status:**
- **Validated:** Evidence supports hypothesis
- **Invalidated:** Evidence contradicts hypothesis
- **Inconclusive:** Not enough evidence either way

**Include:**
- Confidence level
- Caveats and limitations
- Alternative explanations

### 6. Act on Results

Make decisions based on findings.

**If validated:** Roll out, scale up
**If invalidated:** Abandon, try different approach
**If inconclusive:** Extend experiment, redesign, or accept uncertainty

## Output Format

```markdown
## Experiment: [Name]

### Hypothesis

**Statement:** [Testable claim]

**If true:** [Action we'll take]
**If false:** [Action we'll take]

### Design

**Type:** [A/B Test / Pilot / Probe / Rollback]

**Variables:**
- Independent: [What we're changing]
- Dependent: [What we're measuring]
- Controlled: [What we're holding constant]

**Sample:** [Size and selection method]
**Duration:** [Timeframe]
**Success threshold:** [Minimum effect to declare success]

**Stopping rules:**
- Stop for harm: [Conditions]
- Stop for success: [Conditions]

### Execution

**Timeline:**
- Start: [Date]
- End: [Date]
- Checkpoints: [Interim checks]

**Data collected:**
- [Metric 1]
- [Metric 2]

### Results

**Quantitative:**

| Metric | Control | Treatment | Difference | Significant? |
|--------|---------|-----------|------------|--------------|
| [Metric] | [Value] | [Value] | [%] | [Yes/No] |

**Statistical:** p-value = [X], confidence interval = [Y]

**Qualitative:**
- [Observation 1]
- [Observation 2]

### Conclusion

**Status:** [Validated / Invalidated / Inconclusive]

**Interpretation:** [What we learned]

**Confidence:** [X%]

**Caveats:**
- [Limitation 1]
- [Limitation 2]

### Next Steps

**Action:** [What we're doing based on results]

**Follow-up:** [Additional experiments or monitoring]
```

## Hypothesis Quality Checklist

Before running experiment:

- [ ] Hypothesis is specific (clear what we're testing)
- [ ] Hypothesis is measurable (know how to evaluate)
- [ ] Hypothesis is falsifiable (can be proven wrong)
- [ ] If-true action is defined
- [ ] If-false action is defined
- [ ] Learning value justifies cost

## Experiment Design Checklist

Before executing:

- [ ] Variables identified (independent, dependent, controlled)
- [ ] Sample size calculated (adequate power)
- [ ] Duration set (long enough for effect)
- [ ] Success threshold defined (minimum detectable effect)
- [ ] Stopping rules specified
- [ ] Metrics instrumented
- [ ] Baseline data available

## Anti-Patterns

| Avoid | Problem | Do Instead |
|-------|---------|------------|
| Peeking at results | Inflates false positives | Wait for full duration |
| Changing mid-experiment | Invalidates results | Restart if must change |
| Underpowered test | Can't detect real effects | Calculate sample size |
| Post-hoc hypotheses | Fishing for significance | Pre-register hypothesis |
| Ignoring practical significance | Statistically but not practically significant | Set minimum effect |
| No stopping rules | Run too long or too short | Define upfront |
| Confirming not testing | Seeking validation not truth | Design for falsification |
