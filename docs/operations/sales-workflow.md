# Sales Workflow

Sales in LeanOS operates in two phases: Strategy (once per segment) and Execution (per deal).

## Phase 1: Strategy (Once Per Segment)

### Step 1: Generate ICP

```
Skill: icp-generator
Input: strategy/canvas/04-segments.md
Output: research/customer/icp/{segment}-icp.yaml
```

**ICP includes:**
- Observable filters (firmographics, technographics, behavioral)
- Qualification criteria and scoring
- Sample companies (5-10 examples)

**Example:**
```yaml
segment: dtc-fashion-smb
filters:
  industry: [fashion, apparel, accessories]
  business_model: direct-to-consumer
  revenue_range: $1M-$10M
  tech_stack: Shopify
  problem_indicators:
    - return_rate: ">20%"
    - fit_complaints: mentioned in reviews
qualification_score: 0.85
```

---

### Step 2: Create Sales Narrative

```
Skill: sales-narrative
Input: Canvas + ICP
Output: threads/sales/narrative/{segment}/
  ├── problem-narrative.md
  ├── solution-narrative.md
  └── specifics-narrative.md
```

**Narratives include:**
- **Problem:** Specific pain points for this segment
- **Solution:** How product addresses root cause
- **Specifics:** Proof points, metrics, case studies

---

### Step 3: Generate Sales Materials

```
Skill: sales-execution/materials-generation
Input: Canvas + Narrative + ICP
Output: artifacts/sales/{segment}/materials/
  ├── pitch-deck.md
  ├── one-pager.md
  ├── call-scripts.md
  ├── email-templates.md
  ├── pilot-agreement.md
  └── contract-template.md
```

Materials are segment-specific, not generic. Each references Canvas positioning and ICP characteristics.

---

## Phase 2: Execution (Per Deal)

Every deal flows through a 6-stage thread:

### Deal Thread Structure

```
threads/sales/{company-name}/
├── metadata.yaml
├── 1-input.md
├── 2-hypothesis.md
├── 3-implication.md
├── 4-decision.md
├── 5-actions.md
└── 6-learning.md
```

---

### Stage 1: INPUT

Capture lead information:
- **Source:** Inbound (website, referral) or outbound (prospecting)
- **Contact info:** Name, title, email, company
- **Initial signal:** What triggered the lead (demo request, reply to email, etc.)

---

### Stage 2: HYPOTHESIS

Link to Canvas assumptions being tested:
- Which segment does this prospect belong to?
- What assumption does this deal validate/invalidate?
- Initial confidence level

**Example:**
```
Tests: A4 - Luxury brands prefer white-label SDK
Company: ElsaAI (luxury fashion brand)
Initial confidence: 60%
```

---

### Stage 3: IMPLICATION

Quantify deal potential:
- **ARR potential:** Expected contract value
- **Strategic value:** Does this validate key hypothesis?
- **Resource cost:** Time investment required
- **Priority score:** Calculated based on fit + value

**Example:**
```
ARR potential: $1M-$1.5M
Strategic value: High (tests luxury white-label preference)
Resource cost: 40 hours (qualification, demo, pilot, close)
Priority: 0.85
```

---

### Stage 4: DECISION

Commit to pursuit strategy:
- **QUALIFY:** Worth pursuing
- **DEFER:** Not ready, nurture
- **REJECT:** Not a fit

Document alternatives considered and reasoning.

---

### Stage 5: ACTIONS

Break into executable tasks using action templates:

**Action types:**
- `sales:lead-intake` → Capture contact info, ICP score
- `sales:qualify` → Discovery call, qualification assessment
- `sales:demo` → Custom pitch deck, demo delivery
- `sales:pilot` → Pilot agreement, execution, results tracking
- `sales:close` → Contract negotiation, signature

**Example progression:**
```
Day 1-5: sales:lead-intake + sales:qualify
Day 6-15: sales:demo
Day 16-40: sales:pilot (30-day agreement)
Day 41-46: sales:close (contract signed)
```

---

### Stage 6: LEARNING

Capture outcomes and update Canvas:

**Metrics tracked:**
- Deal outcome (closed, lost, stalled)
- ARR (if closed)
- Cycle time (days from lead to close)
- Margins and costs
- Customer satisfaction

**Hypothesis validation:**
- Original assumption tested
- Result (validated, invalidated, partial)
- New confidence level
- Evidence summary

**Canvas auto-updates:**
- `10-assumptions.md` → Confidence scores
- `13-metrics.md` → ARR, cycle time, margins

**Content opportunities:**
- If deal validates hypothesis → Flag for marketing thread

**Example:**
```
Deal outcome: Closed
ARR: $1.1M
Cycle time: 46 days
Pilot results: 38% return reduction

Hypothesis validation:
A4: Luxury brands prefer white-label → VALIDATED
Confidence: 60% → 95% (N=5, 100% pattern)

Canvas updates:
- 10-assumptions.md: A4 confidence 95%
- 13-metrics.md: Average deal size $1.05M

Content opportunity:
Topic: ElsaAI white-label case study
Priority: 0.85 (high)
```

---

## Sales Execution Subskills

### materials-generation
- Generates segment-specific sales materials
- Input: Canvas + Narrative + ICP
- Output: 6 material types per segment

### prospect-research
- Finds companies matching ICP filters
- Uses web_search for list building
- Output: CSV with company name, website, LinkedIn

### contact-finding
- Identifies decision-makers at target companies
- Uses LinkedIn, company websites, email patterns
- Output: CSV with contact name, title, email

### outreach-sequencing
- Creates email/phone cadences
- Tailored to segment and campaign
- Output: Sequence templates with timing

### qualification-support
- Prepares for discovery calls
- Company research, question lists, objection handling
- Output: Call prep doc per prospect

---

## Sales Campaigns

For outbound prospecting, create campaign threads:

```
threads/sales/campaigns/YYYY-MM-DD-{name}/
├── 1-input.md (campaign goal, target list)
├── 2-hypothesis.md (what we're testing)
├── 3-implication.md (expected outcomes)
├── 4-decision.md (campaign plan)
├── 5-actions.md (prospect list, sequence, tracking)
└── 6-learning.md (results, Canvas updates)
```

**Campaign flow:**
1. Define target segment and campaign goal
2. Generate prospect list (50-100 companies)
3. Find contacts (decision-makers)
4. Execute outreach sequence (emails, calls, LinkedIn)
5. Track responses and conversions
6. Measure results, update Canvas

---

## Sales Performance Metrics

### Pipeline Velocity
- Lead response time: Target <24h
- Qualification time: Target <7 days
- Demo booking rate: Target ≥40%
- Pilot conversion: Target ≥60%
- Close rate (qualified): Target ≥50%

### Materials Quality
- Pitch deck approval: Target >90%
- Email response rate: Target >10%
- Proposal acceptance: Target >80%

### Deal Metrics (Tracked in Canvas)
- Average deal size (ARR)
- Sales cycle length (days)
- Win rate (qualified opportunities)
- Customer acquisition cost (CAC)

---

## Integration with Marketing

**Sales learning triggers marketing:**

When deals close (Stage 6):
- Canvas assumptions updated with confidence scores
- marketing-execution/content-strategy scans threads
- Content opportunities detected if pattern emerges
- High-priority opportunities flagged in ops/today.md

**Example:**
```
5 luxury brands closed → All chose white-label SDK
Pattern detected: Luxury prefers white-label
Content opportunity: Case study + implementation guide
Priority: 0.85
```

**Marketing content drives sales:**

When content drives demos:
- Sales thread created with attribution metadata
- Source tracked (blog article, LinkedIn post, etc.)
- Stage 6 measures pipeline influenced
- Marketing performance updated with attribution

---

## Next Steps

- Learn marketing workflow: [Marketing Workflow](marketing-workflow.md)
- Understand 6-stage flow: [Causal Flow](causal-flow.md)
- See daily routine: [Daily Routine](daily-routine.md)