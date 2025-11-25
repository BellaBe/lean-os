---
name: business-metrics-tracker
description: Generate mode-aware business performance dashboards tracking revenue, growth, profitability, and customer metrics based on VENTURE or BOOTSTRAP business model mode
allowed-tools: [Read, Write, Bash]
---

# Business Metrics Tracker

You are an expert at extracting business performance data from Canvas and threads to generate mode-specific business metrics dashboards.

## Purpose

Generate business performance dashboards that track:
- **Revenue metrics:** MRR/ARR, growth rates, revenue breakdown
- **Profitability:** Gross margin, net profit, cash flow
- **Customer metrics:** CAC, LTV, LTV:CAC ratio, churn
- **Growth indicators:** Customer acquisition, expansion, market penetration
- **Mode-specific KPIs:** VENTURE (scale) vs BOOTSTRAP (profit) focus

**This is NOT operational metrics** (thread velocity, AI autonomy) - that's handled by `ops-dashboard` skill.

**This IS business performance** - measuring actual business outcomes from sales/marketing execution.

## When to Use This Skill

**Use when:**
- Weekly business review (update business metrics)
- Monthly/quarterly performance analysis
- Before investor/board meetings (VENTURE mode)
- Financial planning and cash flow analysis
- Evaluating business model effectiveness

**Don't use when:**
- Tracking operational system health (use `ops-dashboard` instead)
- Making strategic decisions (metrics inform, don't decide)
- Within individual threads (use `causal-flow` instead)

## Mode-Aware Operation

### Step 1: Determine Business Model Mode

```bash
# Read business model mode from Canvas
mode=$(grep "^\*\*Active Mode:\*\*" strategy/canvas/00-business-model-mode.md | sed 's/\*\*Active Mode:\*\* //' | tr -d ' ')
```

**Supported modes:**
- `VENTURE` - Scale-focused (funded startups, TAM >$1B)
- `BOOTSTRAP` - Profit-focused (self-funded, cash flow priority)
- `HYBRID` - Profit first, then scale (show both metric sets)

### Step 2: Select Template

**Template location:** `.claude/skills/business-metrics-tracker/references/`

- If mode = `VENTURE` → Use `metrics-venture-template.md`
- If mode = `BOOTSTRAP` → Use `metrics-bootstrap-template.md`
- If mode = `HYBRID` → Use both templates (separate sections)

## Data Sources

### Canvas Sources

**Primary metrics file:**
- `strategy/canvas/13-metrics.md` - Current metric values, targets, historical data

**Supporting Canvas files:**
- `strategy/canvas/00-business-model-mode.md` - Mode selection
- `strategy/canvas/01-context.md` - Product name, business context
- `strategy/canvas/11-pricing.md` - Pricing tiers, revenue model, ARPU
- `strategy/canvas/12-costs.md` - Cost structure, burn rate, COGS
- `strategy/canvas/04-segments.md` - Customer segment breakdown

### Thread Sources

**Sales threads (for revenue/customer metrics):**

Scan `threads/sales/*/6-learning.md` for:
- Deals closed (revenue, ARR/MRR added)
- Customer acquisition (new customers, expansion)
- Sales cycle length
- Win/loss rates
- Customer segment distribution

**Marketing threads (for acquisition metrics):**

Scan `threads/marketing/*/6-learning.md` for:
- Pipeline influenced ($ attributed to content)
- Demos generated
- Traffic → conversion metrics
- CAC calculation (marketing spend / customers acquired)

**Time windows:**
- Current month (month-to-date)
- Last month (comparison)
- Current quarter (quarter-to-date)
- Last quarter (comparison)

## Metrics Calculation

### VENTURE Mode Metrics

**Primary KPIs:**
```
MAU (Monthly Active Users):
  Source: strategy/canvas/13-metrics.md → user_metrics.mau

ARR (Annual Recurring Revenue):
  Source: Sum of all active MRR from sales threads × 12
  Calculation: SELECT SUM(mrr) FROM sales_threads WHERE status='active' × 12

User Growth Rate:
  Calculation: (MAU_current - MAU_previous) / MAU_previous × 100

Market Share:
  Source: strategy/canvas/03-opportunity.md → tam_analysis
  Calculation: ARR / TAM × 100

Burn Rate:
  Source: strategy/canvas/12-costs.md → monthly_burn

Runway:
  Source: strategy/canvas/12-costs.md → cash_balance / monthly_burn
```

**Secondary KPIs:**
```
CAC (Customer Acquisition Cost):
  Calculation: Total marketing + sales costs / New customers acquired

LTV (Customer Lifetime Value):
  Calculation: ARPU × (1 / monthly_churn_rate)

LTV:CAC Ratio:
  Target: >3:1 for venture
```

### BOOTSTRAP Mode Metrics

**Primary KPIs:**
```
MRR (Monthly Recurring Revenue):
  Source: Sum of all active MRR from sales threads
  Calculation: SELECT SUM(mrr) FROM sales_threads WHERE status='active'

Monthly Profit:
  Calculation: MRR - COGS - Operating Expenses
  Source: Canvas 11-pricing.md (revenue), 12-costs.md (costs)

Profit Margin:
  Calculation: Monthly Profit / MRR × 100

Cash Flow:
  Calculation: Cash in - Cash out (monthly)
  Source: strategy/canvas/12-costs.md → cash_flow
```

**Secondary KPIs:**
```
CAC:
  Target: <$500 for bootstrap (fast payback required)

CAC Payback Period:
  Calculation: CAC / (ARPU × Gross Margin)
  Target: <6 months for bootstrap

LTV:CAC Ratio:
  Target: >5:1 for bootstrap (higher than venture)
```

## Dashboard Generation Workflow

### Step 1: Read Mode and Select Template

```bash
# Determine mode
mode=$(grep "^\*\*Active Mode:\*\*" strategy/canvas/00-business-model-mode.md | sed 's/\*\*Active Mode:\*\* //' | tr -d ' ')

# Read template
if [ "$mode" = "VENTURE" ]; then
  template="references/metrics-venture-template.md"
elif [ "$mode" = "BOOTSTRAP" ]; then
  template="references/metrics-bootstrap-template.md"
else
  # HYBRID mode - use both
  template="both"
fi
```

### Step 2: Extract Canvas Metrics

**Read current metrics:**
```bash
# Read strategy/canvas/13-metrics.md
# Extract current values for all KPIs
# Parse historical data (last month, last quarter)
```

**Example extraction:**
```markdown
From 13-metrics.md:

## Monthly Recurring Revenue (MRR)
- **Current:** $24,500
- **Last Month:** $22,100
- **Growth:** +10.9% MoM

## Customer Metrics
- **Active Customers:** 49
- **New Customers (This Month):** 8
- **Churned Customers:** 1
- **Net Customer Growth:** +7
```

### Step 3: Scan Sales Threads for Revenue Data

```bash
# Find all completed sales threads (Stage 6 exists)
find threads/sales -name "6-learning.md" -type f

# For each thread, extract:
# - Deal closed (yes/no)
# - ARR/MRR value
# - Customer segment
# - Close date
# - Sales cycle length
```

**Example extraction:**
```markdown
Thread: threads/sales/{company}/6-learning.md

Deal Outcome: CLOSED
ARR: ${arr}
MRR: ${mrr}
Customer Segment: {segment}
Close Date: {date}
Sales Cycle: {days} days
```

### Step 4: Scan Marketing Threads for Attribution Data

```bash
# Find all completed marketing threads
find threads/marketing -name "6-learning.md" -type f

# For each thread, extract:
# - Pipeline influenced ($)
# - Demos generated
# - Traffic metrics
# - Conversion rates
```

**Example extraction:**
```markdown
Thread: threads/marketing/campaigns/dtc-awareness-nov-2024/6-learning.md

Campaign Performance:
- Sessions: 2,450
- Demos: 18
- Conversion Rate: 0.73%
- Pipeline Influenced: $125,000
- Deals Closed (attributed): 2 ($50K ARR)
```

### Step 5: Populate Template with Data

**Replace template placeholders:**
- `{date}` → Current date
- `{from strategy/canvas/01-context.md}` → Product name
- `${value}` → Calculated metric value
- `${target}` → Target from Canvas 13-metrics.md
- `{🟢/🟡/🔴}` → Status indicator (green if ≥target, yellow if 80-99%, red if <80%)
- `{percent}%` → Percentage values

**Calculate derived metrics:**
- MRR growth rate: (Current MRR - Last MRR) / Last MRR × 100
- LTV:CAC ratio: LTV / CAC
- Profit margin: (MRR - Costs) / MRR × 100
- CAC payback period: CAC / (ARPU × Gross Margin)

### Step 6: Generate Dashboard

**Output file:** `artifacts/business/metrics.md`

**Include:**
1. **Header:** Date, mode, product name
2. **Key Metrics Summary:** Table with current/target/status
3. **Revenue & Profitability:** Detailed revenue breakdown
4. **Customer Metrics:** Acquisition, retention, churn
5. **Growth Analysis:** MoM/QoQ growth trends
6. **Efficiency Metrics:** CAC, LTV, payback period
7. **Cash Flow:** (BOOTSTRAP) or Burn/Runway (VENTURE)
8. **Segment Breakdown:** Revenue by customer segment
9. **Historical Trends:** Last 3-6 months trend chart (text-based)

### Step 7: Generate Status Indicators

**Color coding:**
```
🟢 GREEN: Metric ≥ target (on track)
🟡 YELLOW: Metric 80-99% of target (watch closely)
🔴 RED: Metric <80% of target (action required)
```

**Trend indicators:**
```
↑ Improving (vs last period)
→ Flat (±5% vs last period)
↓ Declining (vs last period)
```

## Output Format

### BOOTSTRAP Mode Output

```markdown
# Bootstrap Mode Metrics Dashboard

**Date:** 2025-11-20
**Business Model Mode:** BOOTSTRAP
**Product:** {Product Name}

---

## Key Metrics Summary

| Metric | Current | Target | Status |
|--------|---------|--------|--------|
| Monthly Recurring Revenue (MRR) | $24,500 | $25,000 | 🟡 |
| Monthly Profit (MP) | $8,200 | $7,500 | 🟢 |
| Profit Margin | 33.5% | 30% | 🟢 |
| Cash Flow | +$5,800/mo | Positive | 🟢 |
| Customer Acquisition Cost (CAC) | $420 | <$500 | 🟢 |
| Customer Lifetime Value (LTV) | $4,900 | >$2,000 | 🟢 |
| LTV:CAC Ratio | 11.7:1 | >5:1 | 🟢 |

---

## Revenue & Profitability

### Monthly Recurring Revenue (MRR)
- **Current MRR:** $24,500
- **New MRR (This Month):** $3,300
- **Expansion MRR:** $400
- **Churned MRR:** -$1,300
- **Net New MRR:** +$2,400
- **MRR Growth Rate:** +10.9% MoM ↑

### Revenue Breakdown
- **Total Revenue (This Month):** $26,200
  - Recurring: $24,500 (93.5%)
  - One-time: $1,200 (4.6%)
  - Services: $500 (1.9%)
- **Total Revenue (Last Month):** $23,800
- **Revenue Growth:** +10.1% MoM ↑

...
```

### VENTURE Mode Output

```markdown
# Venture Mode Metrics Dashboard

**Date:** 2025-11-20
**Business Model Mode:** VENTURE
**Product:** {Product Name}

---

## Key Metrics Summary

| Metric | Current | Target | Status |
|--------|---------|--------|--------|
| MAU (Monthly Active Users) | 12,450 | 15,000 | 🟡 |
| ARR (Annual Recurring Revenue) | $294,000 | $500,000 | 🔴 |
| User Growth Rate | +18% MoM | >10% MoM | 🟢 |
| Market Share | 0.03% | Growing | 🟢 |
| Burn Rate | $45K/mo | <$50K/mo | 🟢 |
| Runway | 14 months | >12 months | 🟢 |

---

## User Metrics

### Monthly Active Users (MAU)
- **Current MAU:** 12,450
- **Last Month MAU:** 10,550
- **MoM Growth:** +18.0% ↑
- **New Users (This Month):** 2,850
- **Churned Users:** -950
- **Net User Growth:** +1,900

...
```

## Update Frequency

**Weekly:** Update dashboard with latest thread data
**Monthly:** Full metrics review, trend analysis
**Quarterly:** Historical comparison, strategic review

**Automated triggers:**
- Sales thread completes (Stage 6) → Update revenue metrics
- Marketing thread completes (Stage 6) → Update pipeline/CAC metrics
- Canvas 13-metrics.md updated → Regenerate dashboard

## Integration with Other Skills

**Upstream dependencies:**
- `causal-flow` (sales threads) → Provides revenue data
- `causal-flow` (marketing threads) → Provides attribution data
- `foundation-builder` → Maintains Canvas 13-metrics.md

**Downstream consumers:**
- Human review (Founder's weekly business review)
- Investor reporting (VENTURE mode)
- Financial planning
- Mode switching decisions (BOOTSTRAP → VENTURE transition)

## Success Criteria

✓ **Mode-aware:** Correct template used based on Canvas mode
✓ **Data-driven:** All metrics calculated from threads + Canvas (no manual entry)
✓ **Actionable:** Status indicators show what needs attention
✓ **Trend-aware:** Includes historical comparison (MoM, QoQ)
✓ **Segment breakdown:** Revenue/customers by segment
✓ **Auto-updated:** Regenerates when threads complete

## Best Practices

1. **Read mode first** - Always check `00-business-model-mode.md` before generating
2. **Validate data sources** - Ensure Canvas 13-metrics.md is current
3. **Include trends** - Always show direction (↑↓→) not just current values
4. **Segment granularity** - Break down metrics by customer segment when relevant
5. **Status indicators** - Use 🟢🟡🔴 consistently (≥100%, 80-99%, <80%)
6. **Cash flow focus (BOOTSTRAP)** - Emphasize profitability and payback period
7. **Growth focus (VENTURE)** - Emphasize user growth and market share
8. **Historical context** - Include last 3-6 months for trend analysis

## Remember

This skill tracks **business outcomes** (revenue, profit, growth), NOT operational efficiency (thread velocity, AI autonomy). For operational metrics, use `ops-dashboard` skill instead.

Business metrics answer: "Is the business growing and profitable?"
Operational metrics answer: "Is LeanOS running efficiently?"

Both are important, but serve different purposes.

---

**Last Updated:** 2025-11-20
**Version:** 1.0
