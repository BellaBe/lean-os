# Success Metrics

LeanOS tracks success metrics based on your business model mode. Metrics adapt to VENTURE (scale focus) or BOOTSTRAP (profit focus) priorities.

## Mode-Specific Metrics

### Check Your Mode First

Before reviewing metrics, check `strategy/canvas/00-business-model-mode.md` to confirm your current mode.

---

## VENTURE Mode Metrics

**For funded startups pursuing scale**

### Primary Metrics

| Metric | Definition | Target |
|--------|------------|--------|
| **MAU** | Monthly Active Users | Growth >10% MoM |
| **ARR** | Annual Recurring Revenue | Growth >3x YoY |
| **User Growth Rate** | Month-over-month user growth | >15% MoM |
| **Market Share** | % of TAM/SAM captured | Increasing |
| **Burn Rate** | Monthly cash burned | Decreasing over time |
| **Runway** | Months until cash out | >12 months |

### Secondary Metrics

| Metric | Definition | Target |
|--------|------------|--------|
| **CAC** | Customer Acquisition Cost | Decreasing |
| **LTV** | Customer Lifetime Value | Increasing |
| **LTV:CAC Ratio** | Lifetime value to acquisition cost | >3:1 |
| **NPS** | Net Promoter Score | >50 |
| **Retention (Month 3)** | Users active after 3 months | >40% |
| **DAU/MAU** | Stickiness ratio | >20% |

### Strategic Metrics

- **TAM Penetration:** % of total addressable market reached
- **Competitive Position:** Market share vs top 3 competitors
- **Burn Multiple:** Burn rate / Net new ARR (<2x is excellent)
- **Growth Efficiency:** CAC payback period (<12 months)

### Dashboard Location

Template: `.claude/skills/ops-dashboard/references/metrics-venture-template.md`
Generated: `ops/metrics.md` (auto-populated from threads and Canvas)

---

## BOOTSTRAP Mode Metrics

**For profitable businesses pursuing cash flow**

### Primary Metrics

| Metric | Definition | Target |
|--------|------------|--------|
| **MRR** | Monthly Recurring Revenue | Positive growth |
| **Monthly Profit** | Net profit per month | Positive from month 3 |
| **Profit Margin** | (Revenue - Costs) / Revenue | >30% |
| **Cash Flow** | Net cash in - cash out | Positive |
| **LTV:CAC Ratio** | Lifetime value to acquisition cost | >5:1 |
| **Payback Period** | Months to recover CAC | <6 months |

### Secondary Metrics

| Metric | Definition | Target |
|--------|------------|--------|
| **Revenue per Customer** | Average monthly revenue per customer | Increasing |
| **Churn Rate** | Monthly customer churn | <5% |
| **Customer Count** | Total active paying customers | Growing |
| **CAC** | Customer Acquisition Cost | Stable or decreasing |
| **ARPC** | Average Revenue Per Customer | Stable or increasing |

### Operational Metrics

- **Revenue per Hour Worked:** Efficiency of founder time
- **Support Hours per Customer:** Scalability indicator
- **Break-even Customer Count:** Minimum viable customers
- **Months of Runway (zero revenue):** Cash reserves strength

### Dashboard Location

Template: `.claude/skills/ops-dashboard/references/metrics-bootstrap-template.md`
Generated: `ops/metrics.md` (auto-populated from threads and Canvas)

---

## Universal Metrics (Both Modes)

### Operational Efficiency

| Metric | Definition | Target |
|--------|------------|--------|
| **Decision Latency** | Time from input to decision | <24 hours |
| **AI Autonomy Rate** | % decisions made without human | >95% |
| **Human Review Time** | Daily time on ops review | <30 min/day |
| **Thread Completion Rate** | % threads reaching Stage 6 | >90% |

### Information Quality

| Metric | Definition | Target |
|--------|------------|--------|
| **Zero Duplication** | Single source of truth maintained | 100% |
| **Decision Traceability** | All decisions link to hypothesis | 100% |
| **Canvas Auto-update Accuracy** | Correct automated Canvas updates | >95% |
| **Assumption Validation Rate** | Hypotheses tested per month | Track trend |

### Sales Performance

| Metric | Definition | Target |
|--------|------------|--------|
| **Lead Response Time** | Time to respond to inbound lead | <24 hours |
| **Qualification Rate** | % leads meeting ICP criteria | >40% |
| **Demo Booking Rate** | % qualified leads � demos | >40% |
| **Close Rate** | % demos � closed deals | >50% |
| **Sales Cycle Length** | Days from first contact to close | Decreasing |

### Marketing Performance

| Metric | Definition | Target |
|--------|------------|--------|
| **Content Pieces Published** | Articles/posts per month | 4-8 |
| **Organic Traffic** | Website sessions from SEO/content | Growing |
| **Demos from Content** | Pipeline attributed to content | Track |
| **Content Conversion Rate** | Visitors � demo requests | >0.5% |
| **Top Performer Rate** | % content above avg conversion | >50% |

### Engineering Performance (Optional - if building systems)

| Metric | Definition | Target |
|--------|------------|--------|
| **System Correctness Rate** | % services passing type validation | 100% |
| **Standardization Coverage** | % services with all 5 standards applied | 100% |
| **Code Generation Success** | % requirements → working code | >95% |
| **Composition Validity** | % service compositions passing validation | 100% |
| **Type Safety Coverage** | % functions with type annotations | 100% |
| **Blueprint Completeness** | % services with OpenAPI specs | 100% |
| **Engineering Thread Velocity** | Days from requirement → deployed service | Decreasing |
| **System Integration Time** | Hours to integrate with sales/marketing | <24 hours |

**Engineering Quality Indicators:**
- All services pass correctness validation
- Zero type safety violations
- Standards applied uniformly (auth, validation, response, logging, rate-limiting)
- Category-theoretic composition laws verified

**Integration Success:**
- Engineering supports sales pilots (custom features delivered on time)
- Marketing content accurately reflects product capabilities
- Canvas solution (09-solution.md) stays synchronized with implementation

---

## Impact Score Distribution

Track the distribution of impact scores to ensure AI autonomy is working:

| Impact Range | Interpretation | Action |
|--------------|----------------|--------|
| 0.0 - 0.3 | Low impact, operational | Auto-execute |
| 0.4 - 0.6 | Medium impact, tactical | Auto-execute |
| 0.7 - 0.79 | High impact, near threshold | Auto-execute with caution |
| 0.8 - 1.0 | Strategic, high impact | Human approval required |

**Target Distribution:**
- <0.8 impact: >95% of decisions (AI autonomous)
- e0.8 impact: <5% of decisions (human review)

---

## Canvas Integrity Metrics

### Assumption Validation

Track hypothesis validation status in `strategy/canvas/10-assumptions.md`:

- **Validated ():** Hypotheses confirmed by evidence
- **In Testing (�):** Active threads testing hypothesis
- **Invalidated (L):** Hypotheses disproven, pivoted
- **Draft (=�):** New hypotheses not yet tested

**Target:** Validate or invalidate 3-5 assumptions per month

### Canvas Update Frequency

- **Daily:** metrics.md (from thread learning)
- **Weekly:** assumptions.md (validation status)
- **Monthly:** Full Canvas review for drift detection
- **Quarterly:** Strategic Canvas validation (human-led)

---

## Mode Comparison Table

| Aspect | VENTURE Mode | BOOTSTRAP Mode |
|--------|--------------|----------------|
| **North Star Metric** | MAU / ARR Growth | Monthly Profit / Cash Flow |
| **Priority** | Market share, scale | Profitability, sustainability |
| **Acceptable Burn** | Yes (if growing fast) | No (must be profitable) |
| **CAC Tolerance** | Higher (if LTV justifies) | Lower (fast payback required) |
| **Timeline** | 7-10 years to exit | Profitable in 3 months |
| **Success = ** | $100M ARR, market leader | $20-50k MRR, profitable |

---

## Tracking & Reporting

### Daily

- **ops/today.md:** High-priority items, autonomous decisions summary
- Quick scan: 5 minutes for human review

### Weekly

- **Thread velocity:** How many decisions made and executed
- **Pipeline health:** Sales/marketing funnel status
- **Canvas updates:** What assumptions validated/invalidated

### Monthly

- **Full metrics dashboard:** Populate mode-specific template
- **Trend analysis:** Month-over-month comparisons
- **Hypothesis validation report:** What we learned

### Quarterly

- **Strategic review:** Full Canvas validation with human
- **Mode assessment:** Should we switch modes?
- **System performance:** Is LeanOS delivering on efficiency targets?

---

## Success Benchmarks

### LeanOS System Success

 **Operational:**
- <30 min/day human time
- >95% AI autonomy
- <24h decision latency

 **Quality:**
- Zero duplication
- 100% traceability
- >95% auto-update accuracy

 **Business Impact:**
- Sales pipeline growing
- Marketing attribution clear
- Validated assumptions driving strategy

### Business Success (Mode-Specific)

**VENTURE Success:**
- MAU growing >10% MoM
- ARR >$1M within 18 months
- Runway >12 months
- Market share increasing

**BOOTSTRAP Success:**
- Profitable within 3 months
- MRR growing steadily
- Profit margin >30%
- Sustainable without funding

---

## When to Switch Modes

### BOOTSTRAP � VENTURE

Consider switching if:
-  Profitable for 3+ consecutive months
-  Market opportunity >$1B TAM
-  Ready to raise funding
-  Scalability validated

**Action:** Update `strategy/canvas/00-business-model-mode.md`

### VENTURE � BOOTSTRAP

Consider switching if:
-  Funding dried up, need profitability
-  Market smaller than expected (<$100M)
-  Want to maintain control vs scale
-  Profitable niche more appealing than scale

**Action:** Update `strategy/canvas/00-business-model-mode.md`

---

## Next Steps

- **Set your mode:** Configure [Business Model Mode](../../strategy/canvas/00-business-model-mode.md)
- **Choose dashboard:** Use appropriate [metrics template](../../ops/)
- **Track weekly:** Review metrics every Monday
- **Validate quarterly:** Full system and business review

---

**Last Updated:** 2025-11-18
**Version:** 1.1 (Dual-mode metrics)
