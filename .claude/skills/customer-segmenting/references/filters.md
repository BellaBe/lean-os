# Observable Filters Guide

Observable filters are **searchable criteria** that can identify companies or people in databases, LinkedIn, or public records.

## The Searchability Test

Ask: "Could I build a prospect list using this filter in LinkedIn Sales Navigator, Crunchbase, or a similar tool?"

- **Yes** → Valid observable filter
- **No** → Psychographic trait (avoid)

---

## Valid Observable Filters by Category

### Company Size

| Filter | Data Sources |
|--------|--------------|
| Employee count: 50-200 | LinkedIn, Crunchbase |
| Revenue: $10M-$50M ARR | Crunchbase, PitchBook |
| Funding stage: Series A-B | Crunchbase, news |
| Transaction volume: >10K/month | Industry reports, case studies |

**Examples:**
- "Companies with 100-500 employees"
- "Series B+ funded startups"
- "Revenue $5M-$25M"

### Industry / Vertical

| Filter | Data Sources |
|--------|--------------|
| NAICS code | Census, LinkedIn |
| SIC code | D&B, industry databases |
| Vertical keywords | LinkedIn, company websites |

**Examples:**
- "E-commerce, NAICS 454110"
- "Healthcare SaaS"
- "Manufacturing, automotive tier-1"

### Technology Stack

| Filter | Data Sources |
|--------|--------------|
| Platform used | BuiltWith, Wappalyzer |
| Tools in stack | G2, job postings |
| Infrastructure | BuiltWith, case studies |

**Examples:**
- "Uses Shopify Plus"
- "Salesforce customers"
- "AWS infrastructure"
- "Job postings mention Kubernetes"

### Geography

| Filter | Data Sources |
|--------|--------------|
| Country/region | LinkedIn, Crunchbase |
| City tier | Census data |
| Timezone | Implicit from HQ |

**Examples:**
- "US-based, headquarters"
- "EMEA region"
- "Tier-1 US cities (NYC, SF, LA, Chicago)"

### Behavioral / Operational

| Filter | Data Sources |
|--------|--------------|
| Hiring patterns | LinkedIn jobs, Indeed |
| Growth signals | News, funding announcements |
| Public metrics | App stores, SimilarWeb |

**Examples:**
- "Hiring 3+ engineers this quarter"
- "Monthly active users >100K"
- "Return rate >20%" (via review analysis)
- "NPS mentioned in reviews <30"

### Role / Title (B2B)

| Filter | Data Sources |
|--------|--------------|
| Job title | LinkedIn |
| Department | LinkedIn, org charts |
| Seniority level | LinkedIn |

**Examples:**
- "VP of Engineering"
- "Head of Operations"
- "Director+ in Finance"

---

## Invalid Filters (Psychographic)

These cannot be searched — avoid them:

| Invalid Filter | Why It Fails | Replace With |
|----------------|--------------|--------------|
| "Innovative companies" | No database field for innovation | "Companies with R&D job postings" |
| "Growth-minded founders" | Mindset not searchable | "Founders who raised in last 18 months" |
| "Customer-centric" | Subjective | "NPS program in place" (job postings) |
| "Forward-thinking" | Meaningless | "Early adopters of [specific tech]" |
| "Struggling with X" | Not observable | "Job postings for X-related roles" |
| "Ready to buy" | Intent not visible | "Actively evaluating" (G2 reviews) |

---

## Filter Specificity Levels

### Too Broad (avoid)

- "Tech companies"
- "SMBs"
- "E-commerce stores"

### Appropriate Specificity

- "B2B SaaS companies, 50-200 employees, Series A-B"
- "E-commerce stores with $1M+ GMV on Shopify"
- "Manufacturing companies in automotive supply chain"

### Too Narrow (watch out)

- "Shopify Plus stores in Austin selling pet products with >$5M revenue founded after 2020"

Overly narrow = tiny addressable market. Aim for segments of 1,000+ potential customers.

---

## Combining Filters

Use 2-4 filters per segment. More filters = smaller segment.

**Good combination:**
```
Industry: E-commerce (fashion)
Size: 10K+ monthly orders
Technology: Modern platform (Shopify, BigCommerce)
Geography: US-based
```
→ ~3,000 companies

**Over-filtered:**
```
Industry: E-commerce (fashion)
Size: 10K+ monthly orders
Technology: Shopify Plus specifically
Geography: US-based
Revenue: $10-50M
Founded: 2018-2022
Funding: Series A+
```
→ ~200 companies (too small)

---

## Data Source Reference

| Source | Best For | Access |
|--------|----------|--------|
| LinkedIn Sales Navigator | Titles, company size, industry | Paid |
| Crunchbase | Funding, revenue estimates | Freemium |
| BuiltWith | Technology stack | Freemium |
| SimilarWeb | Traffic, engagement | Freemium |
| G2/Capterra | Software usage, reviews | Free |
| Indeed/LinkedIn Jobs | Hiring signals | Free |
| Census/NAICS | Industry classification | Free |
| Store Leads | E-commerce specific | Paid |

---

## Validation Checklist

For each filter, confirm:

- [ ] Can search this in at least one database
- [ ] Returns 1,000+ results (not too narrow)
- [ ] Returns <50,000 results (not too broad)
- [ ] Clearly differentiates from other segments
- [ ] Data source identified