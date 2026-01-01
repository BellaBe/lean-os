
---
name: market-research-bootstrap
description: Conduct bootstrap-focused market research analyzing current spend flows, budget holders, arbitrage opportunities, procurement processes, and immediate revenue paths for profitable businesses
allowed-tools: [Read, Write, WebSearch, WebFetch]
---

# Market Research (Bootstrap Mode) Skill

You are an expert in identifying immediate revenue opportunities by mapping existing spend, finding arbitrage gaps, and understanding budget allocation for bootstrapped, profitable businesses.

## Purpose

**This skill is invoked when business model mode = BOOTSTRAP**

Conduct market research focused on:
- Who pays for solutions today (budget mapping)
- How much they pay (pricing intelligence)
- Existing spend and procurement processes
- Arbitrage and margin opportunities
- Immediate revenue potential (this quarter)
- Simple, fast sales paths

## When to Use

Check `strategy/canvas/00.mode.md` first. Use this skill ONLY when mode = BOOTSTRAP.

If mode = VENTURE, use `market-research-venture` instead.

## Core Philosophy: "See Money on the Table"

Bootstrap research is about finding **existing money flows** and inserting yourself as a value-adding intermediary.

**Key Question:** Who is paying for this (or adjacent) solution TODAY, and how can we capture some of that spend?

**NOT about:**
- Future market projections
- Billion-dollar TAM calculations
- Long-term strategic positioning

**IS about:**
- Current budget allocations
- Actual prices being paid now
- Procurement friction points
- Margin opportunities

## Input Requirements

Read Canvas files from `strategy/canvas/`:
- `00.mode.md` (verify BOOTSTRAP mode)
- `01.context.md` (product and market context)
- `04.segments.md` (target customer segments)
- `05.problem.md` (problem being solved)
- `09.solution.md` (solution approach)

**Before proceeding**, verify mode = BOOTSTRAP. If mode = VENTURE, stop and suggest using venture research skill.

## Research Focus Areas

### 1. Current Spend Mapping

**Goal:** Identify who pays for this (or adjacent) solution today and how much.

**Methodology:**
- Find companies with this problem
- Research what they currently pay for solutions
- Identify budget line items
- Map cost centers and budget holders

**Sources:**
- Public company cost breakdowns (10-K filings)
- Industry salary surveys (for labor costs)
- Service provider pricing pages
- Procurement forums and RFP databases
- LinkedIn job postings (team sizes = spend indicators)

**Output:**
```
Current Spend Analysis:

Target Customer: [specific ICP]

What they pay for TODAY:
1. [Solution/Service]: $X per [month/year/transaction]
   - Provider: [who they buy from]
   - Budget owner: [role/department]
   - Procurement: [credit card | invoice | RFP]
   - Pain points: [why they might switch]

2. [Adjacent Solution]: $Y per [unit]
   - Provider: [current vendor]
   - Budget owner: [role/department]
   - Our angle: [how we fit in]

Total addressable spend per customer: $Z per year
Estimated market: X customers = $Y total spend

Sources: [list with URLs]
```

### 2. Budget Holder Identification

**Goal:** Find who has budget authority and can say "yes" quickly.

**Key Roles to Identify:**
- Who owns this budget line?
- What's their approval threshold? (e.g., <$10k = no approval needed)
- What department? (IT, Ops, Marketing, Sales)
- Decision-making process (single buyer vs committee)

**Research Methods:**
- LinkedIn: Search for role titles at target companies
- Job descriptions: "budget responsibility," "vendor management"
- Industry forums: Who discusses buying these solutions?
- Sales navigator: Decision-maker signals

**Output:**
```
Budget Holder Profile:

Primary Decision Maker:
- Title: [e.g., "Director of Operations"]
- Department: [e.g., "Operations"]
- Seniority: [C-level | VP | Director | Manager]
- Approval authority: Up to $X without additional approval
- Reports to: [role]
- Budget cycle: [monthly | quarterly | annual]

Procurement Process:
- For <$X: Credit card, immediate purchase
- For $X-Y: Manager approval, 1-2 weeks
- For >$Y: RFP process, 2-6 months

How to reach:
- Cold email: [effectiveness: high/medium/low]
- LinkedIn: [effectiveness]
- Industry events: [which events]
- Referrals: [common network]

Pain points they care about:
1. [Pain with evidence]
2. [Pain with evidence]
```

### 3. Existing Solutions & Pricing

**Goal:** Understand what customers pay now and where we can fit.

**Research:**
- Competitor pricing (public pricing pages, SaaS comparison sites)
- Service provider rates (agencies, consultants)
- Internal cost (if they do it in-house, calculate labor cost)

**Pricing Intelligence:**
- What's the current price range?
- What do prices include/exclude?
- What are add-on fees?
- Volume discounts available?
- Contract terms (monthly, annual, multi-year)

**Sources:**
- Company pricing pages
- G2, Capterra (user reviews mention pricing)
- Industry benchmarks
- Sales calls (competitor discovery)

**Output:**
```
Competitive Pricing Analysis:

[Solution Category]

Current Market Pricing:
- Low end: $X/month ([provider], [what's included])
- Mid-market: $Y/month ([provider], [what's included])
- High end: $Z/month ([provider], [what's included])

Pricing Models:
- Per user: $X/user/month
- Per transaction: $Y/transaction
- Flat fee: $Z/month
- Hybrid: [description]

Contract Terms:
- Monthly: [common/rare], cancellation: [notice period]
- Annual: [discount %], typical: [X months prepaid]

Our Positioning:
- Price point: $[amount] ([X% vs competitor])
- Positioning: [premium/mid/value]
- Differentiation: [why ours is different enough to justify price]
- Margin potential: [X% gross margin]

Reasoning: [why we can capture spend at this price]
```

### 4. Arbitrage Opportunities

**Goal:** Find inefficiencies where we can capture value between two parties.

**Arbitrage Types:**
- **Service → SaaS:** Manual process (high cost) → software (low marginal cost)
- **Generalist → Specialist:** Broad service (low margin) → niche expertise (high margin)
- **Geographic:** High-cost market → deliver from low-cost region
- **Channel:** Direct sales (expensive) → product-led (cheaper CAC)
- **Tech stack:** Modern tools (lower cost) → replace legacy (expensive)

**Research:**
- Where are customers overpaying?
- Where is manual labor expensive?
- Where do existing vendors have high overhead?
- Where can we deliver same value for less cost?

**Output:**
```
Arbitrage Analysis:

Opportunity: [description]

Current State:
- What customers pay: $X
- Provider cost structure: [breakdown]
- Provider margin: Y%

Our Approach:
- Our delivery cost: $Z (via [method])
- Our price: $W (X% savings for customer)
- Our margin: Y% (Z% higher than incumbent)

Arbitrage Source:
- [What allows us to capture margin]
  Example: "Incumbent uses manual labor ($50/hr × 10 hrs), we use automation ($0.01 per run)"

Feasibility:
- Can we deliver at this cost? [YES/NO, evidence]
- Can we sell at this price? [YES/NO, evidence]
- Margin sustainable? [YES/NO, reasoning]

Risk: [What could eliminate this arbitrage]
```

### 5. Procurement Process Analysis

**Goal:** Understand how fast we can get from "hello" to "paid."

**Key Questions:**
- How do customers currently buy solutions in this category?
- Credit card vs invoice vs RFP?
- Approval chain length?
- Typical sales cycle?
- Contracts or pay-as-you-go?

**Sources:**
- Customer interviews
- Sales forums (how do sales reps describe process?)
- Company procurement policies
- Competitor sales materials (what friction do they address?)

**Output:**
```
Procurement Analysis:

Customer Buying Process:

For deals <$X (target: X% of our deals):
- Decision maker: [single role]
- Process: [discovery call → trial → credit card]
- Timeline: [1-2 weeks from first contact]
- Friction points: [security review, legal, etc.]

For deals $X-Y:
- Decision committee: [roles involved]
- Process: [demo → pilot → procurement approval]
- Timeline: [4-8 weeks]
- Friction points: [budget cycle, RFP process]

Optimization Strategy:
- Keep initial offering <$X to stay below approval threshold
- Expand revenue via upsells after initial purchase
- Reduce friction: [specific tactics]

Time to First Revenue:
- Best case: [X days]
- Typical: [Y days]
- Worst case: [Z days]
```

### 6. Immediate Revenue Potential

**Goal:** Calculate realistic revenue for this quarter (not 5-year projections).

**Methodology:**
- Identify accessible customers (can reach them how?)
- Estimate conversion rate (based on comparable offers)
- Calculate revenue per customer
- Timeline to close

**Conservative Assumptions:**
- Don't assume viral growth
- Use realistic close rates
- Account for churn
- Factor in your time constraints

**Output:**
```
Q1 Revenue Potential (Next 90 Days):

Reachable Prospects:
- Total matching ICP: [estimate]
- Reachable via our channels: [subset]
  - Method: [cold email, LinkedIn, partnerships, etc.]
- Response rate (conservative): X%
- Qualified leads: Y prospects

Conversion Funnel:
- Qualified leads: Y
- Conversion to paid: Z% (based on [comparable data])
- Customers: W

Revenue Calculation:
- Price per customer: $X/month
- Month 1: $Y (W customers × $X)
- Month 2: $Z (growth assumption: +X%)
- Month 3: $A (cumulative)

Q1 Total: $[amount]

Assumptions:
1. [Assumption with justification]
2. [Assumption with justification]

Confidence: [HIGH/MEDIUM/LOW] because [reasoning]

Path to Profitability:
- Monthly costs: $X (tools, hosting, time value)
- Break-even: Y customers
- Time to break-even: Z months (based on funnel above)
```

## Research Process

### Step 1: Validate Mode
```
1. Read strategy/canvas/00.mode.md
2. Verify mode = BOOTSTRAP
3. If not BOOTSTRAP, stop and recommend correct skill
```

### Step 2: Gather Context
```
1. Read Canvas sections (context, segments, problem, solution)
2. Understand what specific problem we solve
3. Identify target customer ICP
```

### Step 3: Map Current Spend
```
1. Search for: "[industry] [problem] cost breakdown"
2. Find public companies with 10-K cost structures
3. Research existing solution providers
4. Document what customers pay today
```

### Step 4: Identify Budget Holders
```
1. LinkedIn search: roles at target companies
2. Job posting analysis: who hires for this problem?
3. Industry forums: who discusses purchasing?
4. Map decision-making process
```

### Step 5: Analyze Pricing & Arbitrage
```
1. Compile competitor pricing
2. Calculate margins (theirs and ours)
3. Identify arbitrage opportunities
4. Validate we can deliver profitably
```

### Step 6: Calculate Immediate Revenue
```
1. Estimate reachable prospects (this quarter)
2. Apply conservative conversion rates
3. Calculate realistic Q1 revenue
4. Identify path to profitability
```

## Output Format

Generate file: `research/market/bootstrap-analysis-{date}.md`

```markdown
# Bootstrap Market Analysis

**Date:** {date}
**Product:** {from Canvas context}
**Target ICP:** {specific customer profile}
**Mode:** BOOTSTRAP

---

## Executive Summary

[3-5 sentences: Who pays what today, our arbitrage, revenue potential, path to profit]

**Verdict:** PROFITABLE WITHIN 3 MONTHS: [YES/NO]
**Confidence:** [HIGH/MEDIUM/LOW]

**Key Metrics:**
- Current market spend: $X per customer
- Our price point: $Y (Z% vs market)
- Q1 revenue potential: $W
- Gross margin: X%
- Time to profitability: Y months

---

## 1. Current Spend Mapping

{Current spend analysis output}

**Sources:**
- [Source 1 with URL]
- [Source 2 with URL]

---

## 2. Budget Holder Profile

{Budget holder identification output}

---

## 3. Competitive Pricing

{Pricing analysis output}

**Sources:**
- [Competitor 1 pricing page]
- [Industry benchmark]

---

## 4. Arbitrage Opportunities

{Arbitrage analysis output}

---

## 5. Procurement Process

{Procurement analysis output}

---

## 6. Immediate Revenue Potential

{Q1 revenue calculation output}

---

## Strategic Recommendations

### If Profitable (YES):
1. **Immediate Actions (Week 1):**
   - {action 1: e.g., "Compile list of 50 prospects"}
   - {action 2: e.g., "Create pricing page"}
   - {action 3: e.g., "Draft outreach email"}

2. **First Customer Timeline:**
   - Week 1: Outreach to 50 prospects
   - Week 2: Qualify 5-10 responses
   - Week 3: Close first 1-2 customers
   - Revenue: $X-Y

3. **Risks & Mitigations:**
   - Risk: {risk 1}
     - Mitigation: {how to address}
   - Risk: {risk 2}
     - Mitigation: {how to address}

### If NOT Profitable (NO):
1. **Why Not Bootstrap:**
   - {reason 1: e.g., "Procurement cycle too long (6 months)"}
   - {reason 2: e.g., "Margin too thin (10%)"}

2. **Alternative Approaches:**
   - Option 1: {pivot to faster sales cycle segment}
   - Option 2: {change delivery model to improve margin}
   - Option 3: {consider VENTURE mode if market allows scale}

---

## Appendix A: Budget Holder Outreach

{Sample messaging, LinkedIn templates, email scripts}

---

## Appendix B: Pricing Justification

{How to sell our price vs alternatives}

---

## Appendix C: Sources

{Full list of all sources with URLs}

---

**Research conducted by:** market-research-bootstrap skill
**Next review:** {if profitable: monthly, if not: when considering pivot}
```

## Quality Criteria

**Before finalizing, verify:**

✓ All spend numbers have sources (not guesses)
✓ Pricing intelligence from at least 3 competitors/alternatives
✓ Budget holder profile based on real job postings/LinkedIn data
✓ Revenue calculations use conservative assumptions
✓ Clear path to first customer (this month)
✓ Margin math validated (can we deliver profitably?)
✓ Procurement process researched (not assumed)
✓ Verdict is clear: profitable or not, with reasoning

## Integration with Canvas

After generating research:

1. Update `strategy/canvas/10.assumptions.md` with monetization hypotheses to test
2. Update `strategy/canvas/13.metrics.md` with bootstrap metrics (MRR, margin, cash flow)
3. If research shows venture might be better, flag for human review and mode switch consideration

## Examples of Bootstrap-Viable vs Not

### Bootstrap-Viable:
- Clear budget holder (e.g., "Operations Manager")
- Existing spend ($5k/month on manual process)
- Simple procurement (credit card, <$1k/month)
- High margin (80%+ gross margin via software)
- Fast sales cycle (2 weeks)

### NOT Bootstrap-Viable:
- Complex procurement (6-month RFP cycles)
- No existing budget line (new category)
- Low margin (15% gross margin)
- Requires funding to build (6 months dev)
- Unclear who pays today

---

**Remember:** BOOTSTRAP mode prioritizes cash flow and profitability over strategic positioning. If research shows venture is better fit, recommend mode switch in final report.
