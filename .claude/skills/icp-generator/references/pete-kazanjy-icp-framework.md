# Pete Kazanjy ICP Framework

## Core Principle: Observable Over Psychographic

Pete Kazanjy's fundamental insight: **An ICP is only valuable if it enables you to FIND prospects.**

From "Founding Sales" and "The Sales Acceleration Formula":

> "Your ICP should consist entirely of characteristics you can search for in a database. If you can't filter by it in LinkedIn Sales Navigator, BuiltWith, or Crunchbase, it doesn't belong in your ICP."

## The Two Types of Characteristics

### Observable (Good)
**Definition**: Characteristics that can be searched, filtered, or verified through public data.

**Examples**:
- Company size: "50-200 employees"
- Platform: "Built on Shopify"
- Geography: "Headquartered in California"
- Revenue: "$2M-$10M annual revenue" (via Crunchbase estimates)
- Tech stack: "Uses Stripe for payments" (via BuiltWith)
- Industry: "NAICS 448 - Clothing stores"
- Funding: "Series A funded in last 18 months"
- Growth: "Hiring for 5+ roles currently"

**Why they work**: A sales rep can build a list of 100 companies matching these criteria in 30 minutes.

### Psychographic (Bad)
**Definition**: Characteristics based on attitudes, values, or mindsets.

**Examples**:
- "Innovation-focused companies"
- "Customer-centric organizations"
- "Growth-minded founders"
- "Data-driven decision makers"
- "Companies that value design"
- "Forward-thinking leadership teams"

**Why they fail**: How do you search for "innovation-focused" in a database? You can't. This forces reps to guess or waste time qualifying companies that don't match.

## The Observable Proxy Technique

When Canvas or customer research surfaces psychographic traits, translate them to observable proxies:

| Psychographic Trait | Observable Proxies |
|---------------------|-------------------|
| "Innovative companies" | • Filed patents in last 2 years<br>• Engineering blog updated monthly<br>• Speakers at industry conferences<br>• Early adopter of new platforms |
| "Customer-centric" | • NPS program mentioned on careers page<br>• Customer success team >5% of headcount<br>• Customer reviews responded to <24hrs |
| "Growth-minded" | • YoY headcount growth >20%<br>• 10+ open roles currently<br>• Raised funding in last 12 months |
| "Data-driven" | • Data engineer/analyst roles open<br>• Uses analytics platforms (Segment, Amplitude)<br>• Blog posts about data/metrics |
| "Design-focused" | • Design team listed on About page<br>• Dribbble/Behance presence<br>• Award-winning website (Awwwards, etc.) |

**Key pattern**: Find the EVIDENCE of the trait, not the trait itself.

## ICP Template Structure

### Firmographics
```yaml
company_size:
  employees: "50-200"
  reasoning: "Need dedicated ops team to implement (rules out <50), but not so large that we can't reach decision makers (rules out >200)"

revenue: "$2M-$15M ARR"
  reasoning: "Can afford our ACV ($50K), but not yet using enterprise solutions"

geography:
  primary: ["US", "CA", "UK"]
  reasoning: "English-speaking markets with strong e-commerce infrastructure"

industry:
  naics: ["448", "454"]  # Clothing stores, Nonstore retailers
  reasoning: "Fashion/apparel verticals where our solution applies"
```

### Technographics
```yaml
required_platforms:
  - platform: "Shopify"
    reasoning: "Our integration requires Shopify API"

tech_stack_indicators:
  - technology: "Klaviyo"
    signal_strength: "strong"
    reasoning: "Indicates sophisticated email marketing, suggests they invest in tools"

  - technology: "Stripe"
    signal_strength: "medium"
    reasoning: "Modern payment stack, but not exclusive indicator"
```

### Behavioral Signals
```yaml
problem_signals:
  - signal: "Mentions 'high return rate' on FAQ or About page"
    indicates: "Aware of the problem we solve"

  - signal: "Job posting for 'Returns Coordinator' or 'Customer Service'"
    indicates: "Problem is severe enough to hire for it"

  - signal: "Return policy >30 days or very generous"
    indicates: "Likely dealing with fit/sizing issues"
```

## Common Mistakes & Fixes

### Mistake 1: Leaving Psychographics in the ICP
❌ **Bad ICP**:
```
Target: Mid-market SaaS companies with customer-centric cultures
```

✓ **Fixed ICP**:
```
Target:
- Company size: 100-500 employees
- Industry: B2B SaaS (G2 category)
- Customer success team: >5 people (per LinkedIn)
- NPS program mentioned on website/careers page
- Responds to G2/Capterra reviews within 1 week
```

### Mistake 2: Vague Size Ranges
❌ **Bad**: "Small to medium businesses"

✓ **Fixed**: "10-100 employees" OR "$500K-$5M revenue"

### Mistake 3: Unverifiable Claims
❌ **Bad**: "Fast-growing companies"

✓ **Fixed**:
- "20%+ headcount growth YoY (per LinkedIn)"
- "10+ open roles currently"
- "Raised Series A in last 18 months"

### Mistake 4: Category Instead of Specific Platform
❌ **Bad**: "Uses e-commerce platform"

✓ **Fixed**: "Shopify OR WooCommerce OR BigCommerce"

### Mistake 5: Assuming Intent
❌ **Bad**: "Looking to improve customer experience"

✓ **Fixed**:
- "Posted job for CX role in last 90 days"
- "Mentions CX in recent blog posts or social media"
- "Attended CX-focused conferences (via LinkedIn events)"

## Buyer Persona Framework

**Critical**: ICP defines the COMPANY. Personas define the PEOPLE within that company.

### Three Key Personas

**Economic Buyer** (Budget Authority)
- Title: VP Operations, CFO, COO
- Priorities: ROI, cost reduction, efficiency
- Decision criteria: Business case, payback period, total cost

**Technical Buyer** (Implementation Authority)
- Title: Engineering Manager, CTO, VP Product
- Concerns: Integration complexity, reliability, maintenance
- Evaluation criteria: API documentation, security, scalability

**End User** (Daily User)
- Role: Customer service rep, operations specialist
- Pain points: Time wasted on [problem], frustration with current process
- Success metrics: Time saved, easier workflow, fewer errors

**Example from GlamYouUp ICP**:
```yaml
buyer_personas:
  economic_buyer:
    title: "VP Operations, Director of E-commerce"
    priorities: ["Reduce return rate", "Improve unit economics", "Increase customer LTV"]
    decision_criteria: ["ROI from reduced returns", "Implementation cost", "Time to value"]

  technical_buyer:
    title: "Engineering Lead, CTO"
    concerns: ["Shopify integration complexity", "Page load impact", "Data privacy compliance"]
    evaluation_criteria: ["API quality", "Documentation", "Support SLA"]

  end_user:
    role: "E-commerce manager, Customer experience team"
    pain_points: ["Manual sizing recommendations", "High return volume processing", "Customer complaints about fit"]
    success_metrics: ["Return rate reduction", "Time saved on sizing questions", "Improved customer satisfaction"]
```

## Disqualification Criteria

**Hard Disqualifiers** (Immediate no-go):
```yaml
hard_disqualifiers:
  - "Revenue <$500K"
    reasoning: "Can't afford our solution, long sales cycle with low close rate"

  - "Already using competitor X with >1 year contract remaining"
    reasoning: "No buying window, waste of sales time"

  - "Platform: Magento 1.x"
    reasoning: "Our integration doesn't support this, would require custom dev"
```

**Soft Disqualifiers** (Deprioritize but don't discard):
```yaml
soft_disqualifiers:
  - "No in-house engineering team"
    reasoning: "Implementation may be difficult, but doable with agency support"
    when_to_reconsider: "If they have a retained development agency"

  - "Return rate <5%"
    reasoning: "Problem may not be severe enough to prioritize"
    when_to_reconsider: "If they're launching new product lines or expanding categories"
```

## Qualification Question Mapping

Every ICP criterion should map to a qualification question:

| ICP Criterion | Qualification Question |
|---------------|------------------------|
| "50-200 employees" | "How many people work at your company?" |
| "Shopify platform" | "What e-commerce platform is your store built on?" |
| "Return rate problem" | "What's your current return rate?" OR "How many returns do you process monthly?" |
| "$2M-$10M revenue" | "What's your approximate annual revenue?" OR "How many orders per month do you fulfill?" |
| "US/CA/UK" | "Where is your company headquartered?" OR "What markets do you sell in?" |

**Key**: Questions should be:
1. **Simple**: Can be answered in 5 seconds
2. **Objective**: Yes/no or numeric (not "Do you value customer experience?")
3. **Disqualifying**: A "wrong" answer = end the conversation politely

## The Kazanjy Sales Efficiency Test

**Your ICP passes the test if**:

1. **List Building**: Can a sales rep build a list of 100 qualified prospects in <30 minutes?
   - If no: Too vague, add observable filters

2. **Qualification Speed**: Can a rep determine fit in <10 minutes on a call?
   - If no: Too many criteria, or criteria are too subjective

3. **Low False Positive Rate**: Do >50% of companies that match the ICP actually have the problem?
   - If no: Filters aren't predictive of the problem

4. **Tool Compatibility**: Can you search for every criterion in standard prospecting tools?
   - If no: Characteristics are too psychographic

5. **Rep Alignment**: Can two reps independently build lists that 80%+ overlap?
   - If no: Criteria are too subjective or vague

## Progressive ICP Refinement

**Phase 1: Initial Hypothesis** (Pre-launch)
- Based on Canvas customer segments
- Heavy assumptions, minimal data
- Focus: Observable proxies for Canvas insights

**Phase 2: Early Validation** (First 10 customers)
- Note commonalities across first customers
- Identify false positives (matched ICP but didn't buy)
- Adjust filters based on closed-won patterns

**Phase 3: Data-Driven ICP** (50+ customers)
- Analyze closed-won vs closed-lost
- Calculate conversion rates by ICP segment
- Create A/B/C tiers of ICP fit

**Phase 4: Predictive ICP** (100+ customers)
- Statistical analysis of best-fit characteristics
- LTV, churn rate, implementation success by segment
- Refine disqualification criteria based on data

**Key**: Start with observable hypotheses, then refine with data. Never start with psychographics.

## References

- Pete Kazanjy, "Founding Sales" (2016), Chapter 3: "Ideal Customer Profile"
- Aaron Ross & Marylou Tyler, "Predictable Revenue" (2011), on ICP discipline
- Mark Roberge, "The Sales Acceleration Formula" (2015), on data-driven ICP refinement

## Quick Reference Checklist

When reviewing an ICP, verify:

- [ ] Every characteristic is searchable in a prospecting tool
- [ ] No psychographic language ("innovative", "customer-focused", etc.)
- [ ] Specific platform/technology names (not categories)
- [ ] Numeric ranges for size, revenue, growth metrics
- [ ] Geographic specificity (country codes or regions)
- [ ] Industry codes (NAICS/SIC) or specific verticals
- [ ] Disqualifiers are clear and objective
- [ ] Every criterion maps to a qualification question
- [ ] Buyer personas include specific titles and departments
- [ ] Problem signals include WHERE to look and WHAT to find
