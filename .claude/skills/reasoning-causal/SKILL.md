---
name: reasoning-causal
description: Execute evidence-based decision-making through 6-stage causal flow. Use for known processes, operational execution, and decisions with clear cause-effect chains.
version: 2.0.0
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

Load thread-specific architecture as needed:

### Business Threads
**Reference:** `reference/business-threads.md`
**Use for:** Strategic decisions, product changes, market positioning
**Action types:** Engineering, legal, marketing, sales, operations

### Sales Threads
**Reference:** `reference/sales-threads.md`
**Use for:** Deal pipelines, individual prospects, enterprise opportunities
**Action types:** lead-intake, qualification, demo, pilot, close

### Marketing Threads
**Reference:** `reference/marketing-threads.md`
**Use for:** Campaign execution, content launches, market research
**Action types:** research, create, publish, promote, measure

### Engineering Threads
**Reference:** `reference/engineering-threads.md`
**Use for:** Translating business requirements into engineering specifications
**Stages:** 1-5 only (no Stage 6 - closes after specifications defined)
**Output:** Requirements list for specialized engineering skills to build

## Orchestration Workflow

### Step 1: Determine Thread Type

Ask user if unclear:
- Business decision? → `threads/business/{name}/`
- Sales opportunity? → `threads/sales/{name}/`
- Marketing campaign? → `threads/marketing/{name}/`
- Engineering requirement? → `threads/engineering/{name}/`

### Step 2: Load Thread-Specific Architecture

```
Read reference/{type}-threads.md
```

This provides:
- Thread structure conventions
- Action type catalogs
- Metadata schemas
- Workflow patterns

### Step 3: Execute 6-Stage Flow

Invoke stage skills **sequentially**:

1. **Stage 1: Input** → `stages/causal-flow-input/SKILL.md`
2. **Stage 2: Hypothesis** → `stages/causal-flow-hypothesis/SKILL.md`
3. **Stage 3: Implication** → `stages/causal-flow-implication/SKILL.md`
4. **Stage 4: Decision** → `stages/causal-flow-decision/SKILL.md`
5. **Stage 5: Actions** → `stages/causal-flow-actions/SKILL.md`
6. **Stage 6: Learning** → `stages/causal-flow-learning/SKILL.md`

**CRITICAL:** Do NOT execute stage logic in this orchestrator. Delegate to stage skills.

### Step 4: Track Progress

Monitor thread state:
- `draft` → `active` → `in_review` → `completed` → `archived`

Update `ops/today.md` with high-impact items (≥0.8).

## Six Stages

### Stage 1: Input
Capture factual observation that triggers the flow.
- What happened? (not opinion, fact)
- When? Where? Who observed?
- What's the context?

### Stage 2: Hypothesis
Link to Canvas assumption being tested.
- Which assumption does this challenge or validate?
- What do we believe will happen?
- What would prove us wrong?

### Stage 3: Implication
Analyze business impact with numbers.
- Revenue impact (high/medium/low)?
- Timeline (short/medium/long)?
- Resource requirements?
- Risk level?

### Stage 4: Decision
Make official commitment with alternatives.
- What are we committing to?
- What alternatives were considered?
- Impact score (for routing)?
- Who needs to approve?

### Stage 5: Actions
Generate executable tasks.
- Typed actions (sales:*, marketing:*, engineering:*)
- Assigned owners
- Deadlines
- Success criteria

### Stage 6: Learning
Document outcomes and update Canvas.
- What happened vs expected?
- Hypothesis validated/invalidated?
- Canvas sections to update?
- New threads generated?

## Impact Scoring

Calculate in Stage 4 to determine routing:

**Score < 0.8:** Auto-execute autonomously
**Score ≥ 0.8:** Flag for human approval

### Mode-Aware Formulas

**VENTURE Mode:**
```
Impact = (Strategic Value × Market Size × Defensibility) / 3
```

**BOOTSTRAP Mode:**
```
Impact = (Revenue Impact × Time to Cash × Margin) / 3
```

Check `strategy/canvas/00-business-model-mode.md` for current mode.

## Canvas Integration

**Location:** `strategy/canvas/` (15 markdown files)
**Primary for causal flow:** `strategy/canvas/10-assumptions.md`

Stage skills handle Canvas reading/updating automatically:
- Stage 2 reads assumptions
- Stage 6 updates assumptions

## Output Storage

**Strategy:** `strategy/canvas/`, `strategy/financials/`
**Artifacts:** `artifacts/sales/`, `artifacts/marketing/`, `artifacts/engineering/`
**Threads:** `threads/{type}/{name}/` (working documents)

## Decision Authority

**AI Autonomous (Impact <0.8):**
- Within strategic direction
- ROI > 3x, risk low-medium
- Cost <$100K, timeline <3 months

**Human Review (Impact ≥0.8):**
- Strategic pivot
- ROI <2x, high risk
- Cost ≥$100K, timeline ≥3 months

Stage 4 skill calculates impact and flags appropriately.

## Available Resources

### Stage Skills
- `stages/causal-flow-input/SKILL.md`
- `stages/causal-flow-hypothesis/SKILL.md`
- `stages/causal-flow-implication/SKILL.md`
- `stages/causal-flow-decision/SKILL.md`
- `stages/causal-flow-actions/SKILL.md`
- `stages/causal-flow-learning/SKILL.md`

### Reference Documentation
- `reference/business-threads.md`
- `reference/sales-threads.md`
- `reference/marketing-threads.md`
- `reference/engineering-threads.md`

### Action Templates
- `actions/templates/sales-*.md`
- `actions/templates/marketing-*.md`

## Success Criteria

- **Evidence-based:** Starts with factual observation (Stage 1)
- **Hypothesis-driven:** Challenges assumptions (Stage 2)
- **Impact-analyzed:** Full cost/benefit (Stage 3)
- **Traceable:** Complete audit trail (Stages 1-6)
- **Self-correcting:** Canvas updates (Stage 6)
- **Autonomous:** AI executes >95%
- **Strategic:** Human review only when flagged

## Remember

Every decision—business, sales, or marketing—flows through **6 stages**. No shortcuts.

This skill:
- Routes to appropriate thread type
- Loads thread-specific architecture
- Invokes stage skills sequentially
- Monitors progress

This skill does NOT:
- Execute stage logic (delegate to stage skills)
- Know stage execution details (stage skills handle)
- Contain reference material (load on-demand)
