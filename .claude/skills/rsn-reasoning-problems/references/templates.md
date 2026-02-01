# Templates

Lightweight formats for simple cases. Use when full reasoning mode isn't needed.

## When to Use Templates vs Modes

| Situation | Use |
|-----------|-----|
| Documenting known process | Template: SOP |
| Quick verification list | Template: Checklist |
| Defining "done" for existing plan | Template: Success Criteria |
| Actionable guidance (simple) | Template: Recommendation |
| Need to analyze/reason through | Use reasoning mode |

---

## SOP / Runbook

For documenting repeatable processes.

```markdown
## [Procedure Name]

**Purpose:** [What this accomplishes]
**Last updated:** [Date]

### When to Use
- [Trigger condition 1]
- [Trigger condition 2]

### Prerequisites
- [ ] [What must be true before starting]
- [ ] [Required access/tools]

### Steps

**1. [Action]**
- Expected outcome: [What success looks like]
- If fails: [What to do]

**2. [Action]**
- Expected outcome: [What success looks like]

**3. [Action]**
- Expected outcome: [What success looks like]
- ⚠️ Warning: [Risk or irreversibility note]

### Decision Points

**At step [N], if [condition]:**
- Yes → [Do this]
- No → [Do that]

### Rollback

**If [failure condition]:**
1. [Undo step]
2. [Undo step]
3. [Notify who]

### Escalation

| Condition | Escalate To | Urgency |
|-----------|-------------|---------|
| [Problem] | [Person/team] | [H/M/L] |

### Quick Checklist
- [ ] [Step 1 summary]
- [ ] [Step 2 summary]
- [ ] [Step 3 summary]
- [ ] [Completion verification]
```

---

## Checklist

For quick verification without detailed steps.

```markdown
## [Checklist Name]

**Use for:** [When to use this checklist]

### Before Starting
- [ ] [Prerequisite 1]
- [ ] [Prerequisite 2]

### [Section 1]
- [ ] [Item]
- [ ] [Item]
- [ ] [Item]

### [Section 2]
- [ ] [Item]
- [ ] [Item]

### Final Verification
- [ ] [Completion check]
- [ ] [Quality check]

**If any item fails:** [What to do]
```

---

## Success Criteria

For defining "done" and verification methods.

```markdown
## Success Criteria: [Initiative/Feature]

### Must Have (Launch Blockers)

| Criterion | Metric | Threshold | How to Verify |
|-----------|--------|-----------|---------------|
| [What] | [Measure] | [Pass value] | [Test method] |

### Should Have (Quality Bar)

| Criterion | Metric | Threshold | How to Verify |
|-----------|--------|-----------|---------------|
| [What] | [Measure] | [Pass value] | [Test method] |

### Failure Conditions

| Condition | Threshold | Response |
|-----------|-----------|----------|
| [What would fail] | [Number] | [Action to take] |

### Rollback Triggers

| Trigger | Action |
|---------|--------|
| [Condition] | [What to do] |

### Verification Schedule
- **Before launch:** [What to check]
- **24h post-launch:** [What to check]
- **7 days post-launch:** [What to check]
```

---

## Recommendation

For actionable guidance without deep analysis.

```markdown
## Recommendation: [Topic]

### Context
[Brief situation description — 2-3 sentences]

### Recommendation

**[Do this specific thing]**

[Rationale in 2-3 sentences]

### Alternatives

| Alternative | When to Consider |
|-------------|------------------|
| [Option B] | [Condition where B is better] |
| [Option C] | [Condition where C is better] |

### Trade-offs
- [What you're giving up by following this recommendation]

### Immediate Actions
1. [First thing to do] — Owner: [Who]
2. [Next thing to do] — Owner: [Who]

### Watch For
- [Signal that recommendation isn't working]
- [Condition to revisit this guidance]
```

---

## Summary / Description

For neutral information without recommendations.

```markdown
## Summary: [Topic]

### Scope
**Covers:** [What's included]
**Excludes:** [What's not included]
**As of:** [Date]

### Overview
[2-3 sentence neutral summary]

### Key Points

**[Section 1]**
- [Fact with source]
- [Fact with source]

**[Section 2]**
- [Fact with source]
- [Fact with source]

### Data

| [Dimension] | [Metric 1] | [Metric 2] |
|-------------|------------|------------|
| [Row 1] | [Value] | [Value] |
| [Row 2] | [Value] | [Value] |

### Open Questions
- [What's unknown]
- [What needs clarification]

*Note: This summary describes current state. For recommendations, see [link] or request recommendation output.*
```

---

## Template Selection

| Need | Template |
|------|----------|
| "How do we do X?" (known process) | SOP |
| "What should we check?" | Checklist |
| "How do we know it's done?" | Success Criteria |
| "What should we do?" (simple) | Recommendation |
| "What's the situation?" | Summary |

For complex questions requiring analysis, use reasoning modes instead:
- "Why did X happen?" → Abductive mode
- "Should we do A or B?" → Dialectical mode
- "What's the pattern?" → Inductive mode
