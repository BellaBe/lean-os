# Dialectical Mode

Synthesize opposing positions into integrated resolution.

## When to Use

- Stakeholders disagree on direction
- Trade-offs between valid positions exist
- Need to resolve conflicting requirements
- Question is "How do we resolve this?"

## Flow

```
Thesis (steel-man) → Antithesis (steel-man) → Synthesis (integrate)
```

---

## Core Principles

### Steel-Man, Don't Straw-Man

Represent each position at its strongest:
- Assume good faith
- Find the kernel of truth
- Present the best possible articulation

If you can't state the opposing view in a way its advocates would accept, you don't understand it yet.

### Synthesis ≠ Compromise

| Invalid Synthesis | Valid Synthesis |
|-------------------|-----------------|
| Split the difference | Integrate at higher level |
| Take turns | Find frame that accommodates both |
| Declare winner | Address underlying concerns |
| Average positions | Transcend original framing |

Compromise leaves both sides unsatisfied. Synthesis addresses what both sides actually need.

---

## Stage 1: Thesis

State first position at its strongest.

**Required elements:**
- **Position:** Clear statement of the claim
- **Underlying concern:** What this is really about (often different from stated position)
- **Evidence:** Supporting data and arguments
- **Implications:** What happens if adopted

**Key move:** Identify the underlying concern. People argue about positions, but care about concerns.

**Example:**

> **Position:** Engineering says: "Rebuild platform before shipping new features."
> 
> **Underlying concern:** Sustainable development velocity. Technical debt is slowing everything down.
> 
> **Evidence:**
> - Deploy time increased 300% year-over-year
> - 40% of sprint capacity goes to workarounds
> - 3 critical incidents traced to architecture issues
> 
> **Implications if adopted:**
> - 6-month rebuild period
> - No new features during rebuild
> - Then: estimated 3x velocity improvement

**Gate:** Must state underlying concern, not just position.

---

## Stage 2: Antithesis

State counter-position with equal strength.

**Required elements:**
- **Position:** Clear statement of the counter-claim
- **Underlying concern:** What this side is protecting
- **Challenge to thesis:** Direct attack on thesis assumptions
- **Evidence:** Supporting data and arguments

**Challenge to thesis must:**
- Identify a specific assumption in the thesis
- Provide counter-evidence or counter-argument
- Be substantive (not just "but what about...")

**Example:**

> **Position:** Sales says: "Deliver Q2 features first, defer rebuild."
> 
> **Underlying concern:** Revenue target attainment. Missing Q2 means missing the year.
> 
> **Challenge to thesis:**
> - Thesis assumes rebuild must happen all at once (but incremental is possible)
> - Thesis assumes 6 months is acceptable (but market won't wait)
> - Thesis discounts revenue risk (but $2M pipeline depends on Q2 features)
> 
> **Evidence:**
> - $2M pipeline tied to Q2 feature commitments
> - Competitor launching similar features in March
> - Board expects feature delivery, not infrastructure investment

**Gate:** Must include direct challenge to a thesis assumption.

---

## Stage 3: Synthesis

Integrate positions at higher level.

### Resolution Types

| Type | When | How |
|------|------|-----|
| **Integration** | Both can coexist | "Do A AND B by [method]" |
| **Sequencing** | Temporal resolution | "First A, then B" |
| **Segmentation** | Context-dependent | "A for X context, B for Y context" |
| **Reframing** | False dichotomy | "Real question is C, not A vs B" |
| **Transcendence** | Higher goal | "Both serve Z; optimize for Z" |

### Required elements:
- **Resolution type:** Which approach
- **How thesis concern is addressed**
- **How antithesis concern is addressed**
- **Trade-offs:** What each side gives up
- **Commitments:** What each side agrees to

**Challenge:** "Am I actually addressing both concerns, or just picking a side? Does this synthesis actually resolve the tension?"

**Example:**

> **Resolution type:** Integration (strangler fig pattern)
> 
> **Integrated position:** Rebuild incrementally while delivering priority features. New features built on new architecture modules.
> 
> **Thesis (engineering) addressed:**
> - Concern: Sustainable velocity
> - How met: Rebuild happens, modularly. Each new feature advances the architecture.
> - Partial satisfaction: Takes 9 months instead of 6, but continuous delivery throughout.
> 
> **Antithesis (sales) addressed:**
> - Concern: Revenue targets
> - How met: Top 3 features delivered in Q2. No 6-month freeze.
> - Partial satisfaction: 3 features instead of 5, but the critical ones.
> 
> **Trade-offs:**
> - Engineering accepts: 9 months instead of 6; ongoing feature work during rebuild
> - Sales accepts: 3 features instead of 5; joint prioritization of which 3
> 
> **Commitments:**
> - Engineering: Deliver features 1, 2, 4 on new modules by Q2 end
> - Sales: Accept reduced scope; participate in prioritization
> - Both: Weekly sync on progress and blockers

**Gate:** Both underlying concerns must be addressed. Both sides must explicitly commit.

---

## Worked Example

> **Conflict:** Product wants to ship fast; Legal wants thorough review.
> 
> **Thesis (Product):**
> - Position: Ship MVP this month
> - Underlying concern: Market timing—competitor launching soon
> - Evidence: 60-day window before competitor; customer commitments
> 
> **Antithesis (Legal):**
> - Position: Full compliance review first (8 weeks)
> - Underlying concern: Liability exposure—GDPR, data handling
> - Challenge: MVP assumes low risk, but customer data is involved
> - Evidence: Recent enforcement actions in space; contract requirements
> 
> **Synthesis:**
> - Resolution type: Segmentation + Sequencing
> - Frame: Not all features have equal risk
> 
> **Integrated approach:**
> - Segment features by data sensitivity
> - Low-risk features (no PII): Ship now
> - High-risk features (PII handling): Full review, ship in 6 weeks
> 
> **Concerns addressed:**
> - Product: Ships in market window with core value prop
> - Legal: High-risk features get proper review
> 
> **Trade-offs:**
> - Product: Reduced initial scope
> - Legal: Expedited process for low-risk items
> 
> **Commitments:**
> - Product: Clear scope definition by EOD
> - Legal: 48-hour turnaround on low-risk review
> - Joint: Daily standup during sprint

---

## Output Format

```markdown
## Dialectical Analysis: [Conflict]

### Thesis: [Position A]
**Position:** [Statement]
**Underlying concern:** [What they really care about]
**Evidence:** [Supporting points]

### Antithesis: [Position B]  
**Position:** [Statement]
**Underlying concern:** [What they really care about]
**Challenge to thesis:** [Specific assumption attacked]
**Evidence:** [Supporting points]

### Synthesis
**Resolution type:** [Integration/Sequencing/Segmentation/Reframing/Transcendence]

**Integrated position:** [What we will do]

**Thesis concern addressed:** [How]
**Antithesis concern addressed:** [How]

**Trade-offs:**
- [Side A] accepts: [What they give up]
- [Side B] accepts: [What they give up]

**Commitments:**
- [Side A]: [Specific commitment]
- [Side B]: [Specific commitment]
```

---

## Output Format

### Synthesis Output (for resolving conflicts)

```markdown
## Synthesis: [Conflict]

### Positions

**Thesis ([Stakeholder]):**
- Position: [What they advocate]
- Underlying concern: [What they actually care about]
- Evidence: [Supporting points]

**Antithesis ([Stakeholder]):**
- Position: [What they advocate]
- Underlying concern: [What they actually care about]
- Challenge to thesis: [Where thesis fails]
- Evidence: [Supporting points]

### Resolution

**Type:** [Integration / Sequencing / Segmentation / Reframing / Transcendence]

**Integrated position:** [What we will do]

**How thesis concern is met:** [Explanation]

**How antithesis concern is met:** [Explanation]

### Trade-offs

| Trade-off | Accepted by | Rationale |
|-----------|-------------|-----------|
| [What's given up] | [Who bears cost] | [Why acceptable] |

### Commitments
- **[Party A]:** [Specific commitment]
- **[Party B]:** [Specific commitment]
```

### Decision Output (for choosing between options)

When the task is selecting one option:

```markdown
## Decision: [Statement]

### Context
[Why this decision now, what triggered it]

### Options

**Option A: [Name]**
- Pros: [Benefits]
- Cons: [Drawbacks]

**Option B: [Name]**
- Pros: [Benefits]
- Cons: [Drawbacks]

**Option C: Do Nothing**
- Pros: [Benefits]
- Cons: [Drawbacks]

### Criteria

| Criterion | Weight | Definition |
|-----------|--------|------------|
| [Factor] | [0.0-1.0] | [What this means] |

### Recommendation

**[Option A]**

[Rationale in 2-3 sentences explaining why this option best satisfies the weighted criteria]

### Trade-offs Accepted
- [What we're giving up]: Accepted because [reason]

### Risks
| Risk | Likelihood | Mitigation |
|------|------------|------------|
| [What could go wrong] | H/M/L | [How to reduce] |

### Revisit If
- [Condition that would change this decision]
```

---

## Quality Gates

| Stage | Gate |
|-------|------|
| Thesis | Underlying concern stated (not just position) |
| Antithesis | Direct challenge to thesis assumption |
| Synthesis | Both concerns addressed; both sides commit |

## Anti-Patterns

| Avoid | Do Instead |
|-------|------------|
| Straw-man positions | Steel-man each side |
| Position = concern | Dig for underlying concern |
| Mushy middle | Force specific resolution type |
| Unacknowledged trade-offs | Explicit cost + who accepts |
| Implicit agreement | Both sides state commitment |
| Declaring winner | Address both concerns |
