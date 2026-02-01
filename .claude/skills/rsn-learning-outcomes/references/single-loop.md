# Single-Loop Learning

Correct action within existing frame.

## When to Use

- Action produced unexpected result
- Fix needed without questioning goals
- First occurrence (or second) of problem
- Frame/goals have been validated

## Mental Model

**Thermostat:** Detect deviation from set point → adjust action → return to target.

The set point (goal) is not questioned. Only the action is adjusted.

```
Goal (fixed) → Action → Result → Gap detected → Adjust action → Repeat
```

## Single-Loop vs Double-Loop

| Aspect | Single-Loop | Double-Loop |
|--------|-------------|-------------|
| Question | "Did we do it right?" | "Are we doing the right thing?" |
| Adjusts | Actions, tactics | Goals, assumptions, frame |
| Trigger | Gap from expected | Pattern of failures (3+) |
| Speed | Fast | Slow |
| Risk | Low | High |

## Process

### 1. Detect Gap

Identify the deviation between expected and actual.

**Questions:**
- What did we expect to happen?
- What actually happened?
- How large is the gap?
- How urgent is the fix?

### 2. Diagnose Cause

Find the immediate cause (not root cause — that's double-loop territory).

**Techniques:**
- **5 Whys (shallow):** Stop at proximate cause, not systemic
- **Fault tree:** Map possible causes, identify which occurred
- **Timeline:** What changed right before the problem?

**Key distinction:**
- Proximate cause: "Query filter was wrong"
- Root cause: "No validation in process" (save for prevention step)

### 3. Identify Correction

Determine what action to change.

**Correction types:**
- **Parameter adjustment:** Change a value (threshold, limit, timeout)
- **Process addition:** Add a step (validation, check, review)
- **Input validation:** Verify inputs before processing
- **Error handling:** Add fallback when failure occurs
- **Monitoring:** Detect problem faster next time

### 4. Verify Fix

Confirm the correction works.

**Questions:**
- Does the corrected action produce expected result?
- Any side effects?
- Is the fix complete?

### 5. Implement Prevention

Reduce likelihood of recurrence.

**Prevention types:**
- Add check/validation step
- Add monitoring/alerting
- Update documentation
- Add to checklist

## Frame Validity Check

Before completing single-loop, verify the frame is still valid:

**Check:**
- Is this the first time this type of failure occurred? (1-2 = single-loop OK)
- Did the corrected action achieve the goal? (Yes = frame OK)
- Are underlying assumptions still valid? (Yes = frame OK)

**Escalate to double-loop if:**
- Third failure of same type
- Correction doesn't achieve goal
- Assumptions seem wrong

## Output Format

```markdown
## Single-Loop: [Problem]

**Gap detected:**
- Expected: [What should have happened]
- Actual: [What happened]
- Severity: [Critical/High/Medium/Low]

**Diagnosis:**
- Immediate cause: [What went wrong]
- Contributing factors: [What enabled it]
- Investigation: [How we found it]

**Correction:**
- From: [Old action/value]
- To: [New action/value]
- Rationale: [Why this fixes it]

**Verification:**
- Test: [How we verified]
- Result: [Pass/Fail]

**Prevention:**
- Immediate: [What we added to prevent recurrence]
- Process change: [Any process updates]
- Monitoring: [Any new monitoring]

**Frame check:**
- Pattern? [Yes/No — if Yes, escalate to double-loop]
- Frame valid? [Yes/No]
```

## Common Patterns

### Parameter Was Wrong
```
Diagnosis: Threshold too low/high
Correction: Adjust parameter
Prevention: Document correct range
```

### Step Was Missing
```
Diagnosis: No validation before action
Correction: Add validation step
Prevention: Add to checklist
```

### Input Was Bad
```
Diagnosis: Garbage in, garbage out
Correction: Add input validation
Prevention: Validate at boundary
```

### Error Not Handled
```
Diagnosis: Failure case not covered
Correction: Add error handling
Prevention: Review error paths
```

## Anti-Patterns

| Avoid | Problem | Do Instead |
|-------|---------|------------|
| Blame assignment | Doesn't prevent recurrence | Focus on system/process |
| Surface fix only | Will recur | Address immediate cause |
| No verification | Don't know if fixed | Test the correction |
| No prevention | Will happen again | Add safeguards |
| Over-correction | New problems | Proportional response |
| Skipping frame check | Miss pattern | Always check for pattern |
