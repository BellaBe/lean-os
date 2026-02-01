# Foundations Workflow

How to set up and validate your business canvas using the Foundations agents and skills.

---

## Workflow Selection

```
START
  |
  +--> "I have a new idea"
  |       +--> Quick Validation workflow
  |
  +--> "I want to build a canvas"
  |       +--> Step by step: fnd-architect --> fnd-researcher
  |
  +--> "I need to work on a specific section"
          +--> See Single Block Reference below
```

---

## Phase Execution

Two phases available in Core. Each has a dedicated agent.

```
fnd-architect          fnd-researcher
Phase 0: Setup         Phase 1: Discovery
00, 01, 02             03, 04, 05, 06
     |                      |
     G0                     G1
                             |
                             v
                     Goal Initialization
                     (sys-defining-goals)
```

### Phase 0: Setup (fnd-architect)

**Process:**
1. Check existing state in `strategy/canvas/`
2. Interview for mode: growth priority, funding intent, risk tolerance
3. Interview for KBOS: Known facts, Beliefs, Observations, Strategic intent
4. Interview for constraints: budget, timeline, resources, technical, regulatory
5. Validate G0

**Mode determines downstream thresholds:**

| Mode | TAM Requirement | LTV:CAC Min | Payback Max |
|------|-----------------|-------------|-------------|
| VENTURE | > $1B | 2:1 (early OK) | 24 mo |
| BOOTSTRAP | Any (SOM focus) | 3:1 (now) | 12 mo |

### Phase 1: Discovery (fnd-researcher)

| Step | Skill | Output | Quality Check |
|------|-------|--------|---------------|
| 1 | fnd.r-sizing-markets | 03.opportunity.md | TAM has cited source, SOM realistic |
| 2 | fnd.r-segmenting-customers | 04.segments.md | Filters are searchable, pain scores have evidence |
| 3 | fnd.r-scoring-problems | 05.problem.md | Top 3 with F*I*WTP, evidence cited |
| 4 | fnd.r-analyzing-competition | 06.competitive.md | 3+ competitors, positioning matrix, gaps |

**Gate validation:** `fnd-validating-gates` checks phase transition requirements.

### After G1: What's Next

After Discovery, you have a validated market understanding. From here:

- **Define goals** from what you've learned: `sys-defining-goals`
- **Upgrade to Pro** for business modeling (pricing, unit economics), GTM planning, and full 16-section canvas

---

## Quick Validation

**When:** New idea, considering a pivot, before writing code, testing multiple ideas.

**Outputs:** Minimal canvas (04, 05) + validation direction.

**Process:**
1. Define segment — specific, findable customer with 1-2 observable filters
2. Validate problem — evidence from forums, job postings, competitor reviews
3. Design validation approach — test riskiest assumption first

**Decision after validation:**

```
Evidence supports the problem?
  +--> YES: Proceed to full Discovery (fnd-researcher)
  +--> MIXED: Refine segment or problem, gather more evidence
  +--> NO: Pivot segment, pivot problem, or kill idea
```

---

## Single Block Reference

| Block | File | Skill/Agent | Prompt |
|-------|------|-------------|--------|
| Mode | 00.mode | fnd-architect | "Help me define my business mode" |
| Context | 01.context | fnd-architect | "Document my strategic context" |
| Constraints | 02.constraints | fnd-architect | "Define my constraints" |
| Opportunity | 03.opportunity | fnd.r-sizing-markets | "Size my market" |
| Segments | 04.segments | fnd.r-segmenting-customers | "Define customer segments" |
| Problems | 05.problem | fnd.r-scoring-problems | "Validate problems" |
| Competitive | 06.competitive | fnd.r-analyzing-competition | "Analyze competition" |

Sections 07-15 (value proposition, pricing, unit economics, GTM) require [LeanOS Pro](https://bellabe.github.io/leanos).

---

## Post-Discovery: Goal Initialization

After Discovery (G1 passed), initialize goals from what you've learned.

```
Discovery Complete (G1)
        |
        v
  READ canvas sections
  - 00.mode.md --> metric framework
  - 04.segments.md --> target customer
  - 05.problem.md --> validated problems
        |
        v
  INVOKE sys-defining-goals
  - Define your first measurable goal
        |
        v
  INVOKE sys-decomposing-goals (optional)
  - Break into subgoals
        |
        v
  INVOKE sys-activating-goals
  - Create execution thread
  - Begin causal flow
```

---

## Thread Structure

All Foundations workflows use causal flow threads:

```
threads/foundations/{workflow}/{context}/
+-- 1-input.md          # Canvas state, user request, constraints
+-- 2-hypothesis.md     # Approach, assumptions about market/customer
+-- 3-implication.md    # If hypothesis true, what canvas sections follow
+-- 4-decision.md       # Chosen direction, rationale
+-- 5-actions.md        # Phase execution, skill invocations
+-- 6-learning.md       # Validation results, pivots, insights
```
