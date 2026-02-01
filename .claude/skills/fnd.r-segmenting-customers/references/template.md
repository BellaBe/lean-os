# Segments Canvas Output Template

Use this template for `strategy/canvas/04.segments.md`.

---

```markdown
# Customer Segments

## Primary Segment: {Name}

**Observable Filters:**
- {Filter 1: specific, searchable characteristic}
- {Filter 2}
- {Filter 3}

**Segment Profile:**
- **Size:** {N companies/people in addressable market}
- **Budget Range:** ${X} - ${Y} annually
- **Pain Intensity:** {1-5} — {evidence: job postings, quotes, reports}
- **Willingness to Pay:** {High/Medium/Low} — {justification}

**Why This Segment:**
{1-2 sentences on strategic priority — why start here}

**Key Problems:**
- {Problem 1 they experience}
- {Problem 2}

---

## Secondary Segment: {Name}

**Observable Filters:**
- {Filter 1}
- {Filter 2}

**Segment Profile:**
- **Size:** {N}
- **Budget Range:** ${X} - ${Y}
- **Pain Intensity:** {1-5} — {evidence}
- **Willingness to Pay:** {H/M/L} — {justification}

**Why This Segment:**
{Expansion rationale — why pursue after primary}

**Key Problems:**
- {Problem 1}
- {Problem 2}

---

## Segment Prioritization

| Segment | Size | Pain | WTP | Accessibility | Priority |
|---------|------|------|-----|---------------|----------|
| {Primary} | {N} | {1-5} | {H/M/L} | {H/M/L} | P0 |
| {Secondary} | {N} | {1-5} | {H/M/L} | {H/M/L} | P1 |

**Prioritization Rationale:**
{Why primary first — typically highest pain × WTP combination, or strongest existing signal}

---

## Observable Filter Summary

Quick reference for downstream ICP operationalization:

| Segment | Key Observable Filters | Data Sources |
|---------|----------------------|--------------|
| {Primary} | {filter1}, {filter2} | {LinkedIn, Crunchbase, etc.} |
| {Secondary} | {filter1}, {filter2} | {data sources} |
```

---

## Example: Completed Output

```markdown
# Customer Segments

## Primary Segment: High-Volume Fashion E-commerce

**Observable Filters:**
- E-commerce stores with 10K+ monthly orders
- Fashion/apparel category (NAICS 448)
- Return rate >20% (visible via review complaints)
- US-based operations

**Segment Profile:**
- **Size:** ~3,200 companies (8% of US fashion e-commerce)
- **Budget Range:** $2,000 - $10,000/month for returns solutions
- **Pain Intensity:** 5 — Returns are #1 margin killer; 47 active job postings for "returns manager"
- **Willingness to Pay:** High — Direct P&L impact, proven budget allocation

**Why This Segment:**
Highest pain intensity combined with clear budget authority. Returns cost $8-15/item to process, making ROI calculation straightforward.

**Key Problems:**
- Return processing costs crushing margins
- 30% of returns are preventable sizing issues
- Manual RMA process doesn't scale

---

## Secondary Segment: DTC Brands on Shopify Plus

**Observable Filters:**
- Shopify Plus merchants
- $5M-$50M annual GMV
- Consumer products (not B2B)

**Segment Profile:**
- **Size:** ~2,100 merchants
- **Budget Range:** $1,500 - $5,000/month
- **Pain Intensity:** 4 — Growing pains with returns as they scale
- **Willingness to Pay:** Medium — Cost-conscious but recognize need

**Why This Segment:**
Natural expansion from primary. Platform concentration (Shopify) enables efficient GTM. Growing into the pain primary segment already has.

**Key Problems:**
- Outgrowing manual returns process
- Need automation before next growth phase
- Customer experience suffering from slow refunds

---

## Segment Prioritization

| Segment | Size | Pain | WTP | Accessibility | Priority |
|---------|------|------|-----|---------------|----------|
| High-Volume Fashion | 3,200 | 5 | High | High | P0 |
| DTC Shopify Plus | 2,100 | 4 | Medium | High | P1 |

**Prioritization Rationale:**
Fashion e-commerce first: highest pain (5), proven WTP, and concentrated in identifiable channels (trade shows, industry publications). Shopify Plus segment is natural expansion — same problem, earlier stage, platform-specific GTM.

---

## Observable Filter Summary

| Segment | Key Observable Filters | Data Sources |
|---------|----------------------|--------------|
| High-Volume Fashion | 10K+ orders/mo, fashion NAICS, >20% returns | SimilarWeb, industry reports, LinkedIn |
| DTC Shopify Plus | Shopify Plus badge, $5-50M GMV, DTC | BuiltWith, Store Leads, Shopify partner data |
```