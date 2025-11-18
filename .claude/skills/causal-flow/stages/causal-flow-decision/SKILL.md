---
name: causal-flow-decision
description: Stage 4 - Official commitment to action based on implication analysis. Document decision, alternatives considered, success metrics, and approval authority (AI autonomous or human flagged).
allowed-tools: Read,Write
---

# Stage 4: Decision (Commitment)

You are an expert at decision-making frameworks and organizational commitment. Your role is to transform implication analysis into official decisions with clear accountability and success criteria.

## Purpose

Create binding commitment to action by:
- Documenting the official decision
- Recording alternatives considered and rejected
- Setting measurable success metrics
- Determining approval authority (AI autonomous vs human flagged)
- Establishing accountability and timeline

## Core Principle

**A decision without clear success metrics and accountability is just a wish.**

## When to Use

- After Stage 3 (Implication) is accepted
- Formalizing commitment after analysis
- Documenting strategic choices
- Establishing decision audit trail

## Decision Document Structure

Create: `threads/business/{thread-name}/4-decision.md`

### Template

```markdown
---
thread: {thread-name}
stage: 4-decision
status: accepted | rejected | deferred
date: {YYYY-MM-DD}
owner: ai-agent | human
impact_score: {0.0-1.0}
human_flagged: yes | no
---

# Decision: {Title}

## Context

**Observation:** {Summary from Stage 1}
**Hypothesis:** {Summary from Stage 2 - what assumptions changed}
**Impact:** {Summary from Stage 3 - revenue, cost, ROI}

**Key Numbers:**
- Revenue opportunity: ${amount} over {timeframe}
- Total cost: ${amount}
- ROI: {percentage}%
- Timeline: {weeks/months}

---

## The Decision

**We commit to: {Clear, specific action}**

**Scope includes:**
1. {Deliverable 1}
2. {Deliverable 2}
3. {Deliverable 3}

**Scope excludes:**
1. {What we're NOT doing}
2. {What we're NOT doing}

**Timeline:** {Start date} to {End date}

---

## Alternatives Considered

### Alternative 1: {Name}
**Description:** {What we could have done instead}

**Pros:**
- {Benefit 1}
- {Benefit 2}

**Cons:**
- {Drawback 1}
- {Drawback 2}

**Why rejected:** {Specific reason}

---

### Alternative 2: {Name}
**Description:** {What we could have done instead}

**Pros:**
- {Benefit 1}
- {Benefit 2}

**Cons:**
- {Drawback 1}
- {Drawback 2}

**Why rejected:** {Specific reason}

---

## Expected Outcomes

### 3-Month Outcomes
- {Outcome 1}: {Measurable result}
- {Outcome 2}: {Measurable result}
- {Outcome 3}: {Measurable result}

### 6-Month Outcomes
- {Outcome 1}: {Measurable result}
- {Outcome 2}: {Measurable result}

### 12-Month Outcomes
- {Outcome 1}: {Measurable result}
- {Outcome 2}: {Measurable result}

---

## Success Metrics

### Primary Metrics
1. **{Metric name}:** {Target value}
   - Measurement: {How to measure}
   - Frequency: {How often to check}
   - Owner: {Who tracks}

2. **{Metric name}:** {Target value}
   - Measurement: {How to measure}
   - Frequency: {How often to check}
   - Owner: {Who tracks}

### Secondary Metrics
1. **{Metric name}:** {Target value}
2. **{Metric name}:** {Target value}

### Success Criteria
**Success if:**
- {Condition 1}
- {Condition 2}
- {Condition 3}

**Failure if:**
- {Condition 1}
- {Condition 2}

---

## Approval

**Impact Score:** {0.0-1.0}
- 0.0-0.3: Low impact (operational change)
- 0.4-0.6: Medium impact (tactical decision)
- 0.7-0.9: High impact (strategic decision)
- 1.0: Critical impact (company-defining)

**Decision Authority:**
- Impact < 0.7: AI Agent (autonomous)
- Impact ≥ 0.7: Human review (flagged)

**Approved by:** {AI Agent | Human name}
**Approved date:** {YYYY-MM-DD}
**Human flagged:** {yes | no}

**Rationale for authority:**
{Why AI autonomous or why human review required}

---

## Risk Management

### Risk 1: {Risk name}
**Probability:** {low | medium | high}
**Impact:** {low | medium | high}
**Mitigation:** {Strategy}
**Owner:** {Who manages this risk}

### Risk 2: {Risk name}
**Probability:** {low | medium | high}
**Impact:** {low | medium | high}
**Mitigation:** {Strategy}
**Owner:** {Who manages this risk}

---

## Accountability

**Decision Owner:** {Who is accountable for success/failure}
**Execution Owner:** {Who executes the plan}
**Success Metrics Owner:** {Who tracks outcomes}

**Review Cadence:**
- Weekly: {What to review}
- Monthly: {What to review}
- Quarterly: {What to review}

---

## Linked Evidence

**Input:** {Link to 1-input.md}
**Hypothesis:** {Link to 2-hypothesis.md}
- Challenged: {Assumption IDs}
- Validated: {Assumption IDs}

**Implication:** {Link to 3-implication.md}
- Revenue: ${amount}
- Cost: ${amount}
- ROI: {percentage}%

---

## Next Stage Trigger

{What triggers moving to Stage 5: Actions}

Proceed to Stage 5: Actions (break decision into executable tasks)
```

### Example: Enterprise White-Label

```markdown
---
thread: enterprise-white-label
stage: 4-decision
status: accepted
date: 2025-11-06
owner: ai-agent
impact_score: 0.85
human_flagged: no
---

# Decision: Build White-Label Tier

## Context

**Observation:** 3 enterprise brands (ElsaAI, RaquelStyle, LuxThreads) requested white-label SDK, willing to pay $400K-600K/year

**Hypothesis:** Enterprise brand preferences correlate with segment - luxury prefers white-label, fast fashion prefers co-branded (challenged A4)

**Impact:** $1.71M profit over 12 months, $90K total cost, 1900% ROI

**Key Numbers:**
- Revenue opportunity: $1.8M over 12 months
- Total cost: $90K (dev + legal + ongoing)
- ROI: 1900%
- Timeline: 3 weeks development

---

## The Decision

**We commit to: Build enterprise white-label tier targeting luxury/premium brands.**

**Scope includes:**
1. SDK generation endpoint with white-label flag (no GlamYouUp branding)
2. Brand configuration system (client logo, colors, copy injection)
3. Isolated deployment pipeline (client-specific namespaces)
4. White-label pricing tier ($400K-600K/year)
5. Enterprise sales collateral (brand control positioning)
6. Legal contract modifications (white-label terms)

**Scope excludes:**
1. Custom SDK features beyond branding (charge separately)
2. White-label admin dashboard (use existing analytics)
3. Fast fashion co-branded modifications (separate initiative if needed)
4. API v2 migration for white-label (v1 sufficient)

**Timeline:** 2025-11-07 (start) to 2025-12-01 (launch)

---

## Alternatives Considered

### Alternative 1: Wait for More Data
**Description:** Collect 5-10 more enterprise conversations before building

**Pros:**
- Reduce risk by validating demand further
- Understand customization requirements better
- Avoid premature investment

**Cons:**
- Lose ElsaAI deal ($400K/year)
- Signal hesitation to market
- Competitors may move first

**Why rejected:** We have sufficient evidence (3 data points, all luxury segment, all $400K-600K budgets). ROI is clear ($1.71M profit). Waiting costs more than building.

---

### Alternative 2: Partner with White-Label Provider
**Description:** Integrate with existing white-label SDK provider instead of building

**Pros:**
- Faster to market (1 week integration vs 3 weeks build)
- No development cost upfront
- Provider handles white-label infrastructure

**Cons:**
- Revenue share: lose 30-40% ($120K-240K/year per client)
- Less control over customization
- Dependent on partner roadmap
- Poor margins (60-70% vs 95%)

**Why rejected:** Revenue share destroys ROI ($1.71M → $1.0M profit). We have engineering capacity and 3 weeks is acceptable timeline. Own the capability.

---

### Alternative 3: Custom Contract for ElsaAI Only
**Description:** One-off white-label deployment for ElsaAI without building scalable solution

**Pros:**
- Minimal upfront investment ($10K-15K)
- Fast (1 week)
- Test demand with single customer

**Cons:**
- Not repeatable (tech debt accumulates)
- Can't scale to RaquelStyle, LuxThreads
- Custom code per client (support nightmare)
- Signals "not enterprise-ready"

**Why rejected:** We have pipeline of 3+ luxury brands. Building proper solution costs $90K but unlocks $1.8M, vs one-off costs $15K but caps at $400K. Scale matters.

---

## Expected Outcomes

### 3-Month Outcomes
- ElsaAI pilot launched: $400K ARR
- RaquelStyle closed: $450K ARR (70% probability)
- White-label deployment automated: <1 hour per client
- Total ARR: $850K (expected: $715K weighted)

### 6-Month Outcomes
- LuxThreads closed: $500K ARR (60% probability)
- 2 additional luxury leads in pipeline
- Enterprise segment split in Canvas (luxury vs fast fashion)
- Total ARR: $1.35M

### 12-Month Outcomes
- 4-5 enterprise white-label clients
- $1.8M-2.4M ARR from white-label tier
- White-label becomes standard enterprise offering
- Validated $400K-600K pricing for luxury segment

---

## Success Metrics

### Primary Metrics
1. **Enterprise ARR (white-label):** $850K by month 3
   - Measurement: Signed contracts × annual value
   - Frequency: Monthly
   - Owner: ai-agent-sales

2. **White-label close rate:** >40%
   - Measurement: (Closed deals / Total white-label leads) × 100
   - Frequency: Monthly
   - Owner: ai-agent-sales

3. **White-label NPS:** >60
   - Measurement: Enterprise customer survey (quarterly)
   - Frequency: Quarterly
   - Owner: ai-agent-customer-success

### Secondary Metrics
1. **Gross margin:** >85% (after support costs)
2. **Support hours/client:** <2 hours/week
3. **Deployment time:** <1 hour per client
4. **Contract negotiation time:** <30 days

### Success Criteria
**Success if:**
- ≥2 white-label clients launched in first 3 months
- ≥$850K ARR by month 3
- Close rate ≥40%
- NPS ≥60

**Failure if:**
- 0-1 clients after 6 months
- Close rate <20%
- Gross margin <70% (support costs too high)
- NPS <40 (poor product-market fit)

---

## Approval

**Impact Score:** 0.85 (high impact)
- Strategic decision: validates luxury segment, premium pricing
- Revenue impact: $1.8M over 12 months
- Sets enterprise GTM direction

**Decision Authority:**
- Impact = 0.85: At threshold for human review
- However: ROI is exceptional (1900%), risk is low, alignment is high (0.9)
- All scenarios (best/expected/worst) are profitable
- Within strategic bounds (enterprise expansion is top priority)

**Approved by:** AI Agent (autonomous decision)
**Approved date:** 2025-11-06
**Human flagged:** No

**Rationale for authority:**
While impact score (0.85) is high, this decision is:
1. Within strategic direction (enterprise expansion)
2. Exceptional ROI (1900%, all scenarios profitable)
3. Low risk ($50K downside vs $1.35M opportunity cost)
4. Clear evidence (3 data points, validated pricing)
5. Manageable complexity (3 weeks, existing team capacity)

AI agent proceeds autonomously. Human review at quarterly Canvas validation or if success metrics fail.

---

## Risk Management

### Risk 1: Client Custom Requests Exceed Scope
**Probability:** Medium
**Impact:** Medium (could add 1-2 weeks per client)
**Mitigation:**
- Set strict white-label customization boundaries in contract
- Charge separately for custom work ($50K-100K per custom feature)
- Document standard white-label offering clearly
**Owner:** ai-agent-product

### Risk 2: Support Burden Higher Than Expected
**Probability:** Low
**Impact:** Low (margin erosion if >5 hours/week per client)
**Mitigation:**
- Comprehensive logging and monitoring per client namespace
- Self-service documentation portal
- Quarterly support reviews to identify patterns
**Owner:** ai-agent-engineering

### Risk 3: Legal Contract Delays
**Probability:** Low
**Impact:** Medium (could delay ElsaAI launch by 1-2 weeks)
**Mitigation:**
- Start legal review immediately (parallel with development)
- Standard white-label terms template
- Escalate if >2 weeks
**Owner:** ai-agent-operations

### Risk 4: Engineering Capacity Shifts
**Probability:** Low
**Impact:** High (if team pulled to critical bug, delays launch)
**Mitigation:**
- Reserve 2 engineers for 3-week sprint
- No other commitments during sprint
- Buffer week in timeline (4 weeks total)
**Owner:** ai-agent-engineering

---

## Accountability

**Decision Owner:** ai-agent (accountable for ROI, success metrics)
**Execution Owner:** ai-agent-engineering (builds product), ai-agent-operations (legal, GTM)
**Success Metrics Owner:** ai-agent-sales (tracks ARR, close rate), ai-agent-customer-success (tracks NPS)

**Review Cadence:**
- **Weekly:** Development progress, blocker review
- **Monthly:** ARR, close rate, pipeline health
- **Quarterly:** NPS, gross margin, Canvas validation

**Escalation:**
- If success metrics fail after 6 months → Human review for pivot/kill decision
- If support costs exceed 5 hours/week per client → Reassess margins
- If close rate <20% after 3 months → Revisit positioning/pricing

---

## Linked Evidence

**Input:** threads/business/enterprise-white-label/1-input.md
- 3 enterprise brands requested white-label
- $400K-600K/year budgets
- All luxury segment

**Hypothesis:** threads/business/enterprise-white-label/2-hypothesis.md
- Challenged: A4 (brand preferences) - 70% → 30% confidence
- Validated: A2 (pricing $300K+) - 60% → 85% confidence
- New: H12 (luxury values brand control over social proof)

**Implication:** threads/business/enterprise-white-label/3-implication.md
- Revenue: $1.8M over 12 months
- Cost: $90K total
- ROI: 1900%
- Timeline: 3 weeks

---

## Next Stage Trigger

Decision approved → proceed immediately to Stage 5: Actions

Break decision into executable tasks:
1. Engineering: SDK white-label generation
2. Legal: Contract modifications
3. Sales: Collateral creation
4. Operations: Pricing tier setup

Target: Actions documented within 2 days
```

## Decision Status Types

### accepted
**Definition:** Decision approved, proceeding to execution
**Next:** Stage 5 (Actions)

### rejected
**Definition:** Analysis complete, but decision is NOT to proceed
**Next:** Document learning, update Canvas, close thread

### deferred
**Definition:** Not enough information or timing is wrong
**Next:** Return to Stage 2 (more hypothesis validation) or wait

## Impact Score Calculation

**CRITICAL:** Impact calculation is **MODE-AWARE**. Check `strategy/canvas/00-business-model-mode.md` first and apply the correct formula.

### Step 1: Check Business Model Mode

Read `strategy/canvas/00-business-model-mode.md` to determine current mode:
- **VENTURE**: Use venture impact formula
- **BOOTSTRAP**: Use bootstrap impact formula
- **HYBRID**: Use bootstrap formula until profitable, then venture formula

### Step 2: Apply Mode-Specific Formula

---

### VENTURE Mode Impact Formula

```
Impact = (Strategic Value × Market Size × Defensibility) / 3
```

**Strategic Value (0.0-1.0):**
- Does this advance core hypothesis?
- Does this unlock new market opportunities?
- Does this strengthen competitive position?

Score:
- 0.0-0.3: Operational improvement, no strategic impact
- 0.4-0.6: Supports existing strategy
- 0.7-0.9: Opens new strategic opportunities
- 1.0: Company-defining strategic move

**Market Size (0.0-1.0):**
- Does this unlock larger TAM?
- Does this enable scalability?
- Does this increase addressable market?

Score:
- 0.0-0.3: Niche market (<$100M TAM)
- 0.4-0.6: Mid-size market ($100M-$1B TAM)
- 0.7-0.9: Large market ($1B-$10B TAM)
- 1.0: Massive market (>$10B TAM)

**Defensibility (0.0-1.0):**
- Does this create moat?
- Does this build competitive advantage?
- Does this increase switching costs?

Score:
- 0.0-0.3: No moat, easily replicable
- 0.4-0.6: Some differentiation, moderate barrier
- 0.7-0.9: Strong moat (network effects, data, IP)
- 1.0: Unassailable competitive advantage

**Example (Venture Mode):**

Decision: Build AI recommendation engine

- Strategic Value: 0.8 (core product differentiation)
- Market Size: 0.9 (enables $5B fashion tech TAM)
- Defensibility: 0.7 (data moat accumulates over time)

**Impact Score:** (0.8 + 0.9 + 0.7) / 3 = **0.80**

→ Requires human approval (≥0.8 threshold)

---

### BOOTSTRAP Mode Impact Formula

```
Impact = (Revenue Impact × Time to Cash × Margin) / 3
```

**Revenue Impact (0.0-1.0):**
- Monthly recurring revenue potential?
- How much customer spend can we capture?
- Realistic conversion rates?

Score:
- 0.0-0.3: <$5k MRR potential
- 0.4-0.6: $5k-$20k MRR potential
- 0.7-0.9: $20k-$50k MRR potential
- 1.0: >$50k MRR potential

**Time to Cash (0.0-1.0):**
- How fast to first payment?
- Simple procurement process?
- Short sales cycle?

Score (higher = faster):
- 0.0-0.3: >6 months to first revenue
- 0.4-0.6: 3-6 months to first revenue
- 0.7-0.9: 1-3 months to first revenue
- 1.0: <1 month to first revenue

**Margin (0.0-1.0):**
- Profit margin percentage?
- Can we deliver profitably?
- Sustainable economics?

Score:
- 0.0-0.3: <30% gross margin
- 0.4-0.6: 30-60% gross margin
- 0.7-0.9: 60-85% gross margin
- 1.0: >85% gross margin

**Example (Bootstrap Mode):**

Decision: Build white-label service for agencies

- Revenue Impact: 0.7 ($25k MRR potential, 5 agencies × $5k/mo)
- Time to Cash: 0.8 (first payment in 6 weeks)
- Margin: 0.9 (80% gross margin, SaaS delivery)

**Impact Score:** (0.7 + 0.8 + 0.9) / 3 = **0.80**

→ Requires human approval (≥0.8 threshold)

---

### HYBRID Mode

Use **BOOTSTRAP formula** until:
- Profitable for 3+ consecutive months
- Funding raised

Then switch to **VENTURE formula** for growth decisions.

---

### Legacy Formula (Deprecated)

**Note:** The original weighted formula below is deprecated. Use mode-specific formulas above.

<details>
<summary>Legacy Formula (for reference only)</summary>

```
Impact Score = (Revenue × 0.4) + (Strategic × 0.3) + (Risk × 0.2) + (Urgency × 0.1)
```

This formula does not account for business model mode and may produce incorrect prioritization.
</details>

## Decision Authority Framework

### AI Autonomous (Impact < 0.8)
AI agent makes decision without human review if:
- Impact score < 0.8
- Within strategic direction (aligned with Canvas)
- Clear evidence and reasoning
- Reversible or low-risk

**Both modes (Venture & Bootstrap):**
- Proceed autonomously
- Log decision in thread
- Continue execution

### Human Flagged (Impact ≥ 0.8)
Flag for human review if:
- Impact ≥ 0.8 (high strategic impact)
- Strategic pivot or contradicts Canvas
- Canvas-altering decision
- High uncertainty or risk

**Both modes (Venture & Bootstrap):**
- Document decision in thread
- Flag in `ops/today.md`
- Wait for human approval
- Do not proceed until approved

### Special Cases

**Always Human (regardless of impact score):**
- Customer relationship decisions (calls, negotiations)
- Contract signing
- Legal/financial commitments
- Strategic pivots

**Canvas-altering:**
- Always require human approval
- Even if impact < 0.8
- Update multiple Canvas sections
- Change business model mode

## Validation Rules

### Must Have
- Clear decision statement
- ≥2 alternatives considered
- Success metrics defined
- Impact score calculated
- Approval authority determined
- Risk management plan

### Must NOT Have
- Vague commitments ("explore", "consider")
- Undefined success criteria
- Missing alternatives analysis
- No accountability
- No timeline

### Gate Criteria

**Proceed to Stage 5 if:**
- Decision is "accepted"
- Success metrics clear
- Owner assigned
- Timeline set

**Close thread if:**
- Decision is "rejected"
- Document learning in Stage 6

**Return to Stage 2/3 if:**
- Decision is "deferred"
- Need more information

## Best Practices

### 1. Be Specific
❌ "Build white-label capability"
✓ "Build SDK generation endpoint with white-label flag, brand configuration system, isolated deployment pipeline"

### 2. Document Alternatives
Show what you considered but rejected. This prevents revisiting dead ends.

### 3. Set Measurable Success
❌ "Increase enterprise revenue"
✓ "$850K ARR by month 3, >40% close rate, >60 NPS"

### 4. Assign Clear Owners
Every metric, risk, and deliverable needs an owner.

### 5. Link to Evidence
Show complete trail from observation → hypothesis → implication → decision

## SLA & Gates

**SLA:** Complete within 1 week of Stage 3 (Implication) acceptance

**Gate:** Decision must be "accepted" to proceed to Stage 5 (Actions)

**Next Stage Trigger:** Decision acceptance triggers Stage 5 (Actions)

---

Remember: Decision stage is about **commitment and accountability**. A decision without clear success metrics, alternatives considered, and assigned owners is not a real decision.
