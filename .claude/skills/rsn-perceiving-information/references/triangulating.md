# Triangulating Mode

Cross-reference multiple sources for verification.

## When to Use

- Claim needs validation
- Single source insufficient
- Stakes are high
- Information seems surprising
- Source reliability uncertain

## Mental Model

**Navigation by triangulation:** Fix position from multiple bearings. Where they converge = likely truth.

## When Triangulation is Required

### Stakes-Based Threshold

| Stakes | Requirement |
|--------|-------------|
| Critical | 3+ independent sources |
| High | 2+ independent sources |
| Medium | 1 source + verification check |
| Low | Single source acceptable |

### Mandatory Triggers

- Claims that would drive major decisions
- Information that seems too good/bad to be true
- Surprising or counterintuitive claims
- Claims contradicting prior beliefs
- Claims from unknown/unreliable sources

## Triangulation Patterns

### 3-Independent
Three unrelated sources agreeing.

**Confidence boost:** High

**Use when:** Critical decisions, surprising claims.

### Primary-Secondary
Original source plus analyst interpretation.

**Confidence boost:** Medium

**Use when:** Need both data and context.

### Multi-Method
Same question, different methodologies.

**Confidence boost:** High

**Use when:** Methodology could bias results.

### Temporal
Same source over time.

**Confidence boost:** Medium

**Use when:** Checking for consistency over time.

## Execution

### Source Independence

**Independent sources:**
- Different organizations
- Different methodologies
- No shared data source
- No common author/analyst

**NOT independent (common mistakes):**
- Same original source, different publishers
- Derived from same data
- Same author in different venues
- Press release repackaged by multiple outlets

### Process

1. **Identify claim** — State the claim clearly, note original source, assess initial confidence
2. **Gather sources** — Find 3+ sources, verify independence, note source type and reliability
3. **Assess agreement** — Do sources agree? Where do they differ?
4. **Analyze conflicts** — For disagreements, list possible explanations, assess which is most likely
5. **Form conclusion** — State verdict with confidence, acknowledge caveats

### Confidence Adjustment

| Agreement Level | Confidence Adjustment |
|-----------------|----------------------|
| Full (all sources agree) | +20-30% |
| Majority (most agree) | +10-20% |
| Mixed (no clear pattern) | No change |
| Contradictory (sources disagree) | -10-20% |

## Output Format

```markdown
## Triangulating: [Claim]

**Original claim:** [Statement]
**Original source:** [Where it came from]
**Initial confidence:** [X%]
**Stakes:** [Critical/High/Medium/Low]

### Sources Examined

**Source 1: [Name]**
- Type: [Primary/Secondary/Tertiary]
- Reliability: [High/Medium/Low]
- Finding: [What this source says]
- Supports claim: [Yes/No/Partial]
- Independent from others: [Yes/No — why]

**Source 2: [Name]**
- Type: [Primary/Secondary/Tertiary]
- Reliability: [High/Medium/Low]
- Finding: [What this source says]
- Supports claim: [Yes/No/Partial]
- Independent from others: [Yes/No — why]

**Source 3: [Name]**
- Type: [Primary/Secondary/Tertiary]
- Reliability: [High/Medium/Low]
- Finding: [What this source says]
- Supports claim: [Yes/No/Partial]

### Agreement Analysis

**Agreement level:** [Full/Majority/Mixed/Contradictory]

**Where sources agree:**
- [Agreement point]

**Where sources differ:**
- [Disagreement]: [Source A says X, Source B says Y]
  - Possible explanations: [List]
  - Most likely: [Explanation]

### Conclusion

**Verdict:** [Validated / Partially validated / Uncertain / Invalidated]

**Refined claim:** [If claim needs modification based on findings]

**Confidence:** [X%] — [Why this confidence level]

**Evidence strength:** [Strong/Moderate/Weak]

**Caveats:**
- [Important caveat or limitation]

### Next

**If validated:** [What to do]
**If uncertain:** [What additional verification needed]
**If invalidated:** [What to do]
```

## Quality Gates

| Gate | Requirement |
|------|-------------|
| ≥3 sources attempted | For high-stakes claims |
| Independence verified | Not echoes of same source |
| Conflicts analyzed | Disagreements investigated |
| Confidence adjusted | Based on agreement level |
| Caveats documented | What might still be wrong |

## Anti-Patterns

| Avoid | Problem | Do Instead |
|-------|---------|------------|
| Non-independent sources | False corroboration | Verify true independence |
| Counting echoes | Same info, multiple outlets | Trace to original source |
| Dismissing disagreement | Miss truth | Investigate conflicts |
| Confirmation bias | Favor agreeing sources | Weight by reliability |
| Premature conclusion | Insufficient verification | Require threshold sources |
