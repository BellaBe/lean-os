# Monitoring Mode

Continuous watch for threshold or condition.

## When to Use

- Need ongoing awareness of specific conditions
- Important to detect when something changes
- Early warning required
- Continuous rather than one-time perception
- Threshold crossing requires action

## Mental Model

**Smoke detector:** Constant background vigilance. Silent when normal. Alert when threshold crossed.

## Monitoring Types

### Threshold
Alert when value crosses a line.

**Example:** "Error rate > 5%"

**Use when:** Clear acceptable range exists, crossing threshold requires action.

### Trend
Alert when direction changes or persists.

**Example:** "3 consecutive weeks of decline"

**Use when:** Trajectory matters more than absolute value.

### Anomaly
Alert on deviation from normal pattern.

**Example:** "3 standard deviations from mean"

**Use when:** Normal pattern is established, unusual = noteworthy.

### Absence
Alert when expected event doesn't occur.

**Example:** "No deployment in 7 days"

**Use when:** Regular events should happen, absence indicates problem.

### Combination
Alert when multiple conditions align.

**Example:** "High CPU AND high errors"

**Use when:** Single signal not sufficient, correlation indicates problem.

## Execution

### Configuration

**Target:** What are we monitoring? Why does it matter?

**Thresholds:**

| Metric | Info | Warning | Critical |
|--------|------|---------|----------|
| [Metric 1] | [Value] | [Value] | [Value] |
| [Metric 2] | [Value] | [Value] | [Value] |

**Frequency:** How often to check? (Real-time / Hourly / Daily / Weekly)

**Duration:** How long to monitor? (Ongoing / Until condition / Time-limited)

### Response Definition

For each threshold level, define:

**On info:** [Action, if any]

**On warning:** [Action + who to notify]

**On critical:** [Immediate action + escalation path]

### Alert Fatigue Prevention

- Tune thresholds based on false positive rate
- Use severity levels appropriately
- Batch low-severity alerts
- Target: <10 alerts/day, <20% false positive rate

## Output Format

### Status Report

```markdown
## Monitoring Status: [Target]

**As of:** [Timestamp]
**Monitoring since:** [Start date]
**Check frequency:** [How often]

### Current Status

**Overall:** [Normal / Warning / Critical]

| Metric | Current | Threshold | Status | Trend |
|--------|---------|-----------|--------|-------|
| [Metric 1] | [Value] | [Threshold] | [Status] | [↑/↓/→] |
| [Metric 2] | [Value] | [Threshold] | [Status] | [↑/↓/→] |

### Recent Alerts

| Time | Metric | Condition | Severity | Resolved |
|------|--------|-----------|----------|----------|
| [Time] | [Metric] | [What triggered] | [Level] | [Yes/No] |

### Trends

**Improving:** [Metrics getting better]

**Stable:** [Metrics holding steady]

**Degrading:** [Metrics getting worse — watch these]

### Actions Taken

- [Action taken in response to alert]

### Next

**Continue monitoring:** [Yes/No]
**Adjust thresholds:** [Any needed changes]
**Escalate:** [If critical, who to notify]
```

### Alert Report

```markdown
## Alert: [Metric] [Condition]

**Triggered:** [Timestamp]
**Severity:** [Info / Warning / Critical]

**Condition:** [What threshold was crossed]
**Current value:** [Value]
**Threshold:** [Threshold value]

**Context:**
- Duration: [How long has this been happening]
- Trend: [Getting better/worse/stable]
- Related metrics: [Any correlated changes]

**Suggested action:** [What to do]

**Escalate to:** [If applicable, who to notify]
```

## Quality Gates

| Gate | Requirement |
|------|-------------|
| Thresholds quantified | Specific numbers, not vague |
| Severity levels defined | Info/Warning/Critical |
| Response actions specified | Know what to do when triggered |
| Escalation path clear | Who to notify for critical |
| Tuning scheduled | Regular threshold review |

## Anti-Patterns

| Avoid | Problem | Do Instead |
|-------|---------|------------|
| Alert fatigue | Alerts ignored | Tune thresholds, reduce noise |
| Missing escalation | Problems persist | Clear escalation paths |
| No response plan | Alert without action | Define responses |
| Static thresholds | Don't reflect reality | Regular tuning |
| Too many critical | Cry wolf | Reserve critical for emergencies |
