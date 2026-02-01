# Filtering Mode

Separate signal from noise.

## When to Use

- Information overload threatens quality
- Relevance varies widely across inputs
- Limited attention budget
- Need to prioritize
- Quality of inputs varies

## Mental Model

**Coffee filter:** Let through what matters, block the rest. Accept some good will be lost with the bad.

## Filter Types

### Threshold Filter
Pass items above/below a value.

**Example:** "Relevance score >= 0.7"

**Risk:** Miss near-threshold items that matter.

**Mitigation:** Review items in buffer zone periodically.

### Categorical Filter
Include/exclude based on type.

**Example:** "Include product announcements, exclude HR news"

**Risk:** Important item miscategorized.

**Mitigation:** Clear category definitions, spot-check excluded.

### Recency Filter
Include based on time.

**Example:** "Published in last 30 days"

**Risk:** Miss slow-moving important signals.

**Mitigation:** Periodic archive reviews for significant items.

### Source Filter
Include from trusted sources only.

**Example:** "Primary sources and major publications only"

**Risk:** Echo chamber, miss emerging sources.

**Mitigation:** Quarterly trusted source review.

### Relevance Filter
Score and rank by relevance.

**Example:** "Weighted score >= 0.6, max 20 items"

**Risk:** Scoring model may be miscalibrated.

**Mitigation:** Validate scoring against outcomes.

## Execution

### Criteria Definition (Before Filtering)

**Include if:**
- [Criterion]: [Rationale]
- [Criterion]: [Rationale]

**Exclude if:**
- [Criterion]: [Rationale]
- [Criterion]: [Rationale]

**Priority by:**
- [Dimension]: Weight [X]
- [Dimension]: Weight [Y]

### Process

1. **Define criteria** — Set include/exclude criteria and priority dimensions before filtering
2. **First pass (exclusion)** — Apply exclude criteria, remove clear non-matches, quick and low-effort
3. **Second pass (scoring)** — Score remaining items, apply include criteria, rank by priority
4. **Threshold application** — Apply cutoff threshold, enforce max items if needed, capture borderline items
5. **Validation** — Spot-check filtered-out items, verify no critical items excluded, adjust if needed

### Validation

**Spot check:** Sample [N] filtered-out items to check for false negatives.

**False negative rate:** [X]% — acceptable if <10%, concerning if >20%.

**Adjustment:** If false negative rate high, loosen criteria.

## Output Format

```markdown
## Filtering: [Input Set]

**Input:** [What was filtered, volume]
**Problem:** [Why filtering needed]
**Filter type:** [Threshold/Categorical/Recency/Source/Relevance]

### Criteria Applied

**Include if:**
- [Criterion]

**Exclude if:**
- [Criterion]

**Priority by:**
- [Dimension] (weight: [X])

### Results

**Passed ([N] items):**

| Item | Score | Rationale |
|------|-------|-----------|
| [Item 1] | [Score] | [Why included] |
| [Item 2] | [Score] | [Why included] |

**Filtered out:** [N] items

| Category | Count | Example |
|----------|-------|---------|
| [Category] | [N] | [Sample item] |
| [Category] | [N] | [Sample item] |

### Validation

**Spot check:** Reviewed [N] filtered-out items
**False negatives found:** [N]
**False negative risk:** [Low/Medium/High]

**Adjustments made:**
- [Any criteria changes]

### Warnings

- [Any concerns about what was filtered]

### Next

**Ready for:** [Thinking mode or next perceiving mode]
```

## Quality Gates

| Gate | Requirement |
|------|-------------|
| Criteria defined first | Before filtering starts |
| Filtered-out sampled | Check for false negatives |
| False negative risk assessed | Know what we might miss |
| Warnings documented | Flag concerns |

## Anti-Patterns

| Avoid | Problem | Do Instead |
|-------|---------|------------|
| Post-hoc criteria | Bias toward expected | Define criteria before filtering |
| No spot-check | Unknown false negatives | Sample filtered-out items |
| Over-filtering | Miss important signals | Monitor recall metrics |
| Under-filtering | Still overwhelmed | Tighten criteria iteratively |
| Static filters | Context changes | Review criteria periodically |
