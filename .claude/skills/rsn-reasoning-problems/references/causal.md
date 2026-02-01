# Causal Mode

Execute systematic cause-effect reasoning through 6 stages.

## When to Use

- Executing a known process or workflow
- Making operational decisions with clear steps
- Following goal-linked execution
- Question is "How do we execute this?"

## Flow

```
Input → Hypothesis → Implication → Decision → Actions → Learning
```

---

## Stage 1: Input

State the factual observation that triggers reasoning.

**Required elements:**
- **Observation:** What was observed (fact, not interpretation)
- **Evidence:** Data points with sources and confidence
- **Context:** When, where, who observed
- **Prior belief:** What we believed before this observation

**Challenge:** "Is this fact or interpretation? What was actually observed vs inferred?"

**Example:**

> **Observation:** Q4 pipeline decreased 23% vs Q3.
> 
> **Evidence:** 
> - CRM dashboard shows $4.2M → $3.2M (confidence: high, source: Salesforce)
> - Deal count: 47 → 38 (confidence: high)
> 
> **Context:** Observed Dec 1, covers Oct-Nov activity.
> 
> **Prior belief:** Pipeline would grow 10% based on Q3 trajectory.

**Gate:** All claims must be evidence-backed facts before proceeding.

---

## Stage 2: Hypothesis

Form testable hypothesis connecting observation to cause.

**Required elements:**
- **Statement:** "If [condition], then [prediction], because [mechanism]"
- **Assumption tested:** Which belief this challenges
- **Falsification:** What would prove this wrong
- **Test method:** How to verify

**Challenge:** "Is this falsifiable? What would prove it wrong?"

**Example:**

> **Hypothesis:** If outbound activity dropped, then pipeline decreased, because fewer conversations → fewer opportunities.
> 
> **Assumption tested:** That pipeline correlates with outbound volume.
> 
> **Falsification:** Pipeline stable despite activity drop would disprove this.
> 
> **Test:** Compare outbound metrics (emails, calls, meetings) Q3 vs Q4.

**Gate:** Hypothesis must be falsifiable before proceeding.

---

## Stage 3: Implication

Model scenarios with quantified impacts.

**Required elements:**
- **Scenarios:** At least 3 with probabilities
- **Impact:** Specific numbers for each scenario
- **Resources:** Effort, cost, dependencies
- **Risks:** What could go wrong + mitigation
- **Opportunity cost:** What we can't do if we pursue this

**Challenge:** "Are these numbers justified? What scenario am I missing?"

**Example:**

> **Scenario 1: Hypothesis true (65%)**
> - Impact: Fix outbound process → recover $800K pipeline in Q1
> - Timeline: 6 weeks to implement, 4 weeks to see results
> 
> **Scenario 2: Hypothesis false (25%)**
> - Impact: Outbound not the cause; need to investigate further
> - Timeline: Lose 6 weeks on wrong fix
> 
> **Scenario 3: Partial truth (10%)**
> - Impact: Outbound is one factor; multiple causes
> - Timeline: Partial recovery
> 
> **Resources:** 2 SDRs full-time for 6 weeks, sales ops support
> 
> **Risks:** 
> - Team burnout from process change (medium probability, high impact)
> - Mitigation: Phase rollout, get buy-in first
> 
> **Opportunity cost:** Can't pursue inbound optimization simultaneously

**Gate:** All impacts must have specific numbers.

---

## Stage 4: Decision

State explicit commitment.

**Options:** PROCEED / DEFER / DECLINE

**Required elements:**
- **Commitment:** One of the three options (not "probably" or "maybe")
- **Alternatives:** What else was considered and why rejected
- **Criteria:** Factors weighed with importance
- **Conditions:** When this decision would change

**Challenge:** "Did we consider [alternative]? What if [condition] changes?"

**Example:**

> **Decision:** PROCEED with outbound process fix
> 
> **Alternatives considered:**
> - Hire more SDRs → Rejected: 3-month ramp time, doesn't address root cause
> - Wait for more data → Rejected: Q1 pipeline at risk
> 
> **Criteria:**
> - Speed to impact (high weight): This option fastest
> - Resource cost (medium weight): Acceptable
> - Reversibility (medium weight): Can roll back if wrong
> 
> **Conditions for change:**
> - If Q1 week 2 shows no improvement, revisit hypothesis

**Gate:** Decision must be explicit—PROCEED, DEFER, or DECLINE.

---

## Stage 5: Actions

Define specific tasks with accountability.

**Required for each task:**
- **Description:** What to do
- **Owner:** Who is responsible
- **Deadline:** When it's due
- **Dependencies:** What must happen first
- **Success criteria:** How we know it's done

**Challenge:** "Who owns this? How do we know it's done?"

**Example:**

> **Action 1:** Audit current outbound sequences
> - Owner: Sarah (Sales Ops)
> - Deadline: Dec 15
> - Dependencies: None
> - Success criteria: Report showing sequence performance by stage
> 
> **Action 2:** Design new outbound playbook
> - Owner: Mike (Sales Manager)
> - Deadline: Dec 22
> - Dependencies: Action 1 complete
> - Success criteria: Documented playbook reviewed by 2 SDRs
> 
> **Action 3:** Train team on new process
> - Owner: Mike
> - Deadline: Jan 5
> - Dependencies: Action 2 complete
> - Success criteria: All SDRs complete training, pass quiz

**Gate:** Every task must have owner, deadline, and success criteria.

---

## Stage 6: Learning

Compare expected vs actual. Update beliefs.

**Required elements:**
- **Outcome:** Expected vs actual results
- **Hypothesis status:** Validated / Invalidated / Inconclusive
- **Belief updates:** What assumptions changed
- **Follow-on:** New questions and next actions

**Challenge:** "Are we learning the right lesson? What else could explain this outcome?"

**Example:**

> **Outcome:**
> - Expected: $800K pipeline recovery
> - Actual: $650K recovery (81% of target)
> - Delta: -$150K
> 
> **Hypothesis status:** VALIDATED (partially)
> - Outbound was a factor, but not the only one
> - Evidence: Activity up 40%, pipeline up 20%
> 
> **Belief updates:**
> - Previous: Outbound is primary pipeline driver
> - Updated: Outbound is ~60% of pipeline; other factors matter
> 
> **Follow-on:**
> - Question: What drives the other 40%?
> - Action: Analyze inbound and referral sources

**Gate:** Must compare expected vs actual even when successful.

---

## Output Format

```markdown
## Causal Analysis: [Topic]

### Input
[Observation with evidence]

### Hypothesis
If [condition], then [prediction], because [mechanism].
Falsification: [What would prove wrong]

### Implication
| Scenario | Probability | Impact |
|----------|-------------|--------|
| [Name] | [%] | [Quantified] |

### Decision
**[PROCEED / DEFER / DECLINE]:** [Rationale]

### Actions
1. [Task] — Owner: [Name], Due: [Date]
2. [Task] — Owner: [Name], Due: [Date]

### Learning (post-execution)
- Expected: [X]
- Actual: [Y]
- Hypothesis: [Validated/Invalidated/Inconclusive]
- Updated belief: [What changed]
```

---

## Output Format

### Execution Analysis

```markdown
## Causal Analysis: [Topic]

### Input
**Observation:** [What was observed]
**Evidence:** [Data points with sources]
**Prior belief:** [What we expected]

### Hypothesis
If [condition], then [prediction], because [mechanism].

**Falsification:** [What would prove this wrong]

### Implications

| Scenario | Probability | Impact | Timeline |
|----------|-------------|--------|----------|
| [Name] | [%] | [Quantified] | [Duration] |

**Resources required:** [Effort, cost, dependencies]

**Risks:**
- [Risk]: [Likelihood/Impact] — Mitigation: [How to reduce]

### Decision
**[PROCEED / DEFER / DECLINE]**

[Rationale in 2-3 sentences]

### Actions
1. **[Task]** — Owner: [Name], Due: [Date], Done when: [Criteria]
2. **[Task]** — Owner: [Name], Due: [Date], Done when: [Criteria]

### Constraints
**Hard:** [Cannot violate]
**Soft:** [Preferred but negotiable]

---
*Learning (post-execution):*
- Expected: [X]
- Actual: [Y]
- Belief update: [What changed]
```

### Plan Output (for larger initiatives)

When causal analysis leads to multi-phase work:

```markdown
## Plan: [Initiative Name]

**Goal:** [Measurable objective]
**Owner:** [Person]
**Timeline:** [Duration]

### Constraints
- **Hard:** [Must respect]
- **Soft:** [Prefer but can trade]

### Scope
- **In:** [What's included]
- **Out:** [Explicitly excluded]

### Phases

**Phase 1: [Name]** ([Duration])
- Objective: [What this phase achieves]
- Milestones:
  - [ ] [Milestone]: [Success criteria]
- Deliverables: [What's produced]

**Phase 2: [Name]** ([Duration])
- Objective: [What this phase achieves]
- Start condition: [What must be true to begin]
- Milestones:
  - [ ] [Milestone]: [Success criteria]

### Dependencies
| Dependency | Owner | Risk if Delayed |
|------------|-------|-----------------|
| [What we need] | [Who provides] | [Impact] |

### Risks
| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| [What could go wrong] | H/M/L | H/M/L | [How to reduce] |

### Success Criteria
- [Criterion]: [How measured]
```

---

## Quality Gates

| Stage | Gate |
|-------|------|
| Input | All claims evidence-backed |
| Hypothesis | Falsifiable with test method |
| Implication | ≥3 scenarios with numbers |
| Decision | Explicit PROCEED/DEFER/DECLINE |
| Actions | Owner + deadline + criteria for each |
| Learning | Expected vs actual compared |

## Anti-Patterns

| Avoid | Do Instead |
|-------|------------|
| Jumping to actions | Complete all stages in order |
| Vague hypothesis | Require falsification criteria |
| "Significant impact" | Require specific numbers |
| "We should probably..." | Force explicit commitment |
| Tasks without owners | Require ownership assignment |
| Skipping learning | Always extract insight from outcome |
