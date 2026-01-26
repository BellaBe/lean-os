# Evaluative Mode

Assess quality against defined criteria.

## Trigger Phrases

"review", "assess", "score", "audit", "grade", "rate", "evaluate quality"

## When to Use

- Reviewing work product quality
- Assessing readiness for launch
- Auditing compliance
- Grading against standards

## Execution Instructions

### Step 1: Define Criteria First

Before evaluating, explicitly state:
- What criteria will be used
- Weight of each criterion (sum to 1.0)
- What constitutes pass/partial/fail for each

**Do this:**
```yaml
criteria:
  - criterion: "Code coverage"
    weight: 0.25
    pass: ">= 80%"
    partial: "60-79%"
    fail: "< 60%"
```

**Not this:**
```
I'll review the code quality.
```

### Step 2: Assess Each Criterion

For each criterion:
1. Gather evidence
2. Apply the defined threshold
3. State result: pass | partial | fail
4. Cite specific evidence

**Format:**
```yaml
assessment:
  - criterion: "Code coverage"
    result: pass
    score: 0.85
    evidence: "Jest reports 85% line coverage, 78% branch coverage"
    notes: "Branch coverage could be improved in error handlers"
```

**Rules:**
- Every assessment MUST cite evidence
- Evidence must be specific and verifiable
- Do not assess without evidence

### Step 3: Calculate Overall Verdict

Apply this formula:
```
weighted_score = Σ(criterion_score × weight)

If any blocking criterion fails → verdict: fail
Else if weighted_score >= 0.8 → verdict: pass
Else if weighted_score >= 0.6 → verdict: conditional
Else → verdict: fail
```

**Output:**
```yaml
overall:
  verdict: pass | conditional | fail
  weighted_score: 0.82
  confidence: 0.85
  summary: "Meets requirements with minor gaps in documentation"
```

### Step 4: Identify Gaps

For any criterion scoring below pass:
1. State the gap clearly
2. Assign severity: blocking | significant | minor
3. Do NOT prescribe fixes (that's prescriptive schema)

**Severity definitions:**
- **blocking**: Cannot proceed until resolved
- **significant**: Should be addressed, doesn't block
- **minor**: Nice to have, can proceed

**Format:**
```yaml
gaps:
  - gap: "API documentation incomplete for 3 endpoints"
    criterion: "Documentation completeness"
    severity: significant
    current: "12/15 endpoints documented"
    required: "15/15 endpoints documented"
```

## Output Schema

```yaml
evaluation:
  target: string
  date: date
  evaluator: string
  
  criteria:
    - criterion: string
      weight: float
      pass_threshold: string
      
  assessment:
    - criterion: string
      result: pass | partial | fail
      score: float
      evidence: string
      notes: optional<string>
      
  overall:
    verdict: pass | conditional | fail
    weighted_score: float
    confidence: float
    summary: string
    
  gaps:
    - gap: string
      severity: blocking | significant | minor
      current: string
      required: string
```

## Quality Gates

| Gate | Requirement |
|------|-------------|
| Criteria defined | Before evaluation starts |
| Evidence cited | Every assessment backed by data |
| Thresholds explicit | Clear pass/fail line |
| No recommendations | Evaluative ≠ prescriptive |

## Anti-Patterns

| Avoid | Do Instead |
|-------|------------|
| "Looks good" | Cite specific evidence |
| Evaluating without criteria | Define criteria first |
| Including fixes | Separate evaluation from recommendations |
| Vague severity | Use blocking/significant/minor |

## Boundary

Evaluative schema **describes quality**. It does not:
- Recommend actions (use prescriptive)
- Make decisions (use decision)
- Explain causes (use diagnostic)

If user asks "is this good AND what should I do", chain: evaluative → prescriptive
