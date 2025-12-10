---
name: reasoning-causal
description: Execute evidence-based decision-making through 6-stage causal flow. Use for known processes, operational execution, and decisions with clear cause-effect chains.
---

# Causal Reasoning

Execute systematic cause-effect reasoning. The logic of process and action.

## Type Signature

```
Causal : Input → Hypothesis → Implication → Decision → Action → Learning

Where:
  Input       : Observation × Context → FactualStatement
  Hypothesis  : FactualStatement × CanvasAssumption → TestableHypothesis
  Implication : TestableHypothesis → (Impact × Probability × Timeline)
  Decision    : Implication × Alternatives → Commitment
  Action      : Commitment → [ExecutableTask]
  Learning    : [ExecutedTask] × Outcomes → CanvasUpdate
```

## When to Use

- Process execution with known steps
- Decision with clear cause-effect chain
- Operational workflows (sales, marketing, engineering)
- Canvas hypothesis testing
- Action planning and execution

## Thread Types

| Type | Location | Use For |
|------|----------|---------|
| Business | `threads/business/{name}/` | Strategic decisions, product changes |
| Sales | `threads/sales/{name}/` | Deal pipelines, prospects |
| Marketing | `threads/marketing/{name}/` | Campaigns, content launches |
| Engineering | `threads/engineering/{name}/` | Requirements → specifications |

**Thread-specific details:** See `references/threads/{type}.md`

---

## 6-Stage Flow

Execute stages **sequentially**. Each stage produces a markdown file in the thread directory.

### Stage 1: Input

**File:** `1-input.md`
**Purpose:** Capture factual observation that triggers the flow.

**Content:**
- What happened? (fact, not opinion)
- When? Where? Who observed?
- Raw data/evidence links
- Context (what we believed before)

**Rules:**
- Facts only, no interpretation
- No solutions or recommendations
- Link to evidence

**Detail:** `references/stages/input.md`

---

### Stage 2: Hypothesis

**File:** `2-hypothesis.md`
**Purpose:** Link observation to Canvas assumption being tested.

**Content:**
- Which assumption does this challenge/validate?
- What do we believe will happen?
- What would prove us wrong?
- Testable prediction

**Rules:**
- Must reference `strategy/canvas/10-assumptions.md`
- State falsifiable hypothesis
- Define success/failure criteria

**Detail:** `references/stages/hypothesis.md`

---

### Stage 3: Implication

**File:** `3-implication.md`
**Purpose:** Analyze business impact with numbers.

**Content:**
- Revenue impact (quantified)
- Timeline (short/medium/long)
- Resource requirements
- Risk assessment
- Opportunity cost

**Rules:**
- Include specific numbers
- Compare scenarios
- Identify dependencies

**Detail:** `references/stages/implication.md`

---

### Stage 4: Decision

**File:** `4-decision.md`
**Purpose:** Make official commitment with impact score.

**Content:**
- Decision statement (PROCEED/DEFER/DECLINE)
- Alternatives considered
- Impact score calculation
- Approval status

**Impact Scoring:**

| Score | Action |
|-------|--------|
| < 0.8 | Auto-execute |
| ≥ 0.8 | Flag for human approval |

**Mode-Aware Formulas:**

**VENTURE:** `Impact = (Strategic Value × Market Size × Defensibility) / 3`
**BOOTSTRAP:** `Impact = (Revenue Impact × Time to Cash × Margin) / 3`

Check `strategy/canvas/00-business-model-mode.md` for mode.

**Detail:** `references/stages/decision.md`

---

### Stage 5: Actions

**File:** `5-actions.md` or `5-actions/` directory
**Purpose:** Generate executable tasks.

**Content:**
- Typed actions (sales:*, marketing:*, engineering:*)
- Assigned owners
- Deadlines
- Success criteria
- Dependencies

**Action Types by Thread:**

| Thread | Action Types | Skills |
|--------|--------------|--------|
| Sales | lead-intake, qualify, demo, pilot, close | `sales-*` |
| Marketing | research, create, publish, promote, measure | `marketing-*` |
| Engineering | requirements, specification, implementation | `engineering-*` |
| Business | varies by decision | - |

**Detail:** `references/stages/actions.md`

---

### Stage 6: Learning

**File:** `6-learning.md`
**Purpose:** Document outcomes and update Canvas.

**Content:**
- Actual vs expected outcome
- Hypothesis validated/invalidated?
- Canvas sections to update
- New threads generated
- Metrics captured

**Rules:**
- Update `strategy/canvas/10-assumptions.md`
- Link learning to original hypothesis
- Generate follow-up threads if needed

**Detail:** `references/stages/learning.md`

---

## Workflow

```
1. Determine thread type (business/sales/marketing/engineering)
2. Create thread directory: threads/{type}/{name}/
3. Execute stages 1-6 sequentially
4. At Stage 4: Calculate impact, flag if ≥0.8
5. At Stage 6: Update Canvas assumptions
6. Update ops/today.md with results
```

## Thread Structure

```
threads/{type}/{name}/
├── meta.json           # Thread metadata
├── 1-input.md          # Factual observation
├── 2-hypothesis.md     # Canvas assumption link
├── 3-implication.md    # Impact analysis
├── 4-decision.md       # Commitment + impact score
├── 5-actions.md        # Executable tasks
└── 6-learning.md       # Outcomes + Canvas update
```

## Decision Authority

**AI Autonomous (Impact <0.8):**
- Within strategic direction
- ROI > 3x, risk low-medium
- Cost <$100K, timeline <3 months

**Human Review (Impact ≥0.8):**
- Strategic pivot
- ROI <2x, high risk
- Cost ≥$100K, timeline ≥3 months
- Canvas-altering decisions

## References

```
references/
├── stages/           # Stage execution details
│   ├── input.md
│   ├── hypothesis.md
│   ├── implication.md
│   ├── decision.md
│   ├── actions.md
│   └── learning.md
└── threads/          # Thread type specifics
    ├── business.md
    ├── sales.md
    ├── marketing.md
    └── engineering.md
```

**Note:** Action execution uses flat skills (`sales-*`, `marketing-*`, `engineering-*`) not templates.

## Success Criteria

- **Evidence-based:** Starts with factual observation
- **Hypothesis-driven:** Links to Canvas assumptions
- **Impact-analyzed:** Quantified cost/benefit
- **Traceable:** Complete 6-stage audit trail
- **Self-correcting:** Canvas updates from learning
- **Autonomous:** AI executes >95% (impact <0.8)

## Remember

Every decision flows through **6 stages**. No shortcuts.

This skill:
- Executes the 6-stage causal flow
- Reads reference docs for detail
- Calculates impact scores
- Updates Canvas from learning
- Flags high-impact items for human review
