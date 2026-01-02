---
name: sales-prospect-research
description: Research and identify target companies matching ICP observable characteristics using web search, score against ICP criteria, output prioritized prospect list. Use when you need to find and qualify potential customers.
allowed-tools: [Read, Write, WebSearch]
---

# Prospect Research Subskill

## Purpose

Discover and qualify target companies that match ICP observable characteristics using systematic web research. Score each prospect against ICP criteria and output prioritized list for outreach.

**Operates on**: ONE product per invocation
**Research method**: Web search for observable characteristics
**Output**: Scored and prioritized prospect list in CSV format

## Input Parameters

**Required**:
- `segment`: ICP segment name ("dtc-fashion-smb", "marketplace-reseller", etc.)
- `icp_path`: `research/customer/icp/{segment}-icp.md`

**Optional**:
- `target_count`: Number of prospects to find (default: 50, max: 200)
- `segment`: "primary" | "secondary" | "all" (which ICP segment, default: "all")
- `geography_filter`: Specific geography constraint (overrides ICP, e.g., "California only")

## Workflow

### 1. Load ICP Filters

**Read ICP** from `research/customer/icp/{segment}-icp.md`:

Extract observable characteristics:
```markdown
firmographics:
  company_size:
    employees: "{min}-{max}"
  geography:
    primary: ["{geo1}", "{geo2}", "{geo3}"]
  industry:
    primary: ["{Industry}"]

technographics:
  required_platforms: ["{platform}"]
  tech_stack_indicators: ["{tech1}", "{tech2}"]

problem_signals:
  website_indicators:
    - signal: "FAQ mentions {problem area}"
    - signal: "{Problem indicator}"
  job_posting_signals:
    - role: "{Problem-related role 1}"
    - role: "{Problem-related role 2}"
```

**Parse into searchable filters**:
- Platform: "{platform}"
- Industry: "{Industry}"
- Geography: "{geo1}, {geo2}, {geo3}"
- Size: "{min}-{max} employees"
- Problem keywords: "{keyword1}", "{keyword2}", "{keyword3}"

---

### 2. Execute Web Research

Use systematic web search to find companies matching ICP filters.

#### Search Pattern 1: Platform + Industry Discovery

**For platform-based ICP** (Example):
```
Search: "{platform} stores {industry} {geography}"
Search: site:builtwith.com {platform} {industry}
Search: "{platform} Plus {industry} brands"
Search: "best {platform} {industry} stores {year}"
```

**Extract from results**:
- Company names
- Website domains
- Brief descriptions

**For other platforms**:
- {Platform A}: "{Platform A} stores {industry}"
- {Platform B}: "{Platform B} {industry} stores"
- Custom: "{industry} {business type} sites"

#### Search Pattern 2: Industry Directory Discovery

**E-commerce/Retail** (Example):
```
Search: "{industry} e-commerce brands {geography}"
Search: "DTC {industry} brands list"
Search: "{industry} companies {city/region}"
Search: "{industry} retailers {platform}"
```

**Professional Services** (Example):
```
Search: "{service type} firms {state}"
Search: "{industry} firms {city}"
Search: "{industry} companies"
Search: "{regulatory body} registered {service type}"
```

**Extract from results**:
- Company names
- Locations
- Size indicators (if mentioned)

#### Search Pattern 3: Technology Stack Detection

**For required technologies**:
```
Search: "companies using {technology} {industry}"
Search: site:stackshare.io {platform} {tech stack}
Search: "{technology} customers {industry}"
```

**Verify technology**:
- Visit company website
- Check page source for platform indicators
- Look for technology badges/logos

#### Search Pattern 4: Size & Growth Indicators

**For company size verification**:
```
Search: "{company name}" employees
Search: "{company name}" LinkedIn company size
Search: "{company name}" Crunchbase
Search: "{company name}" funding revenue
```

**Estimate employee count**:
- LinkedIn company page: "XX employees"
- Crunchbase listing: Employee range
- News articles mentioning team size
- "About Us" page team photos/bios

**Estimate revenue** (if needed):
```
Search: "{company name}" revenue annual
Search: "{company name}" sales figures
```

If not public, infer from:
- Employee count (rough: 1 employee ≈ $100K-$150K revenue for SaaS)
- Funding raised (Series A ≈ $1-5M revenue run rate)
- Traffic data if available

#### Search Pattern 5: Problem Signal Detection

**Website Content Search**:
```
Search: site:{domain} "returns"
Search: site:{domain} "return policy"
Search: site:{domain} "sizing guide"
Search: site:{domain} FAQ
```

**Review Site Search**:
```
Search: site:trustpilot.com "{company name}" sizing
Search: site:trustpilot.com "{company name}" returns
Search: "{company name}" reviews fit issues
```

**Job Posting Search**:
```
Search: site:lever.co OR site:greenhouse.io "{company name}" "customer service"
Search: site:lever.co OR site:greenhouse.io "{company name}" "returns"
Search: "{company name}" jobs customer service
```

**Social Media Search**:
```
Search: site:x.com "{company name}" returns
Search: site:linkedin.com "{company name}" customer experience
```

**Problem signal scoring**:
- Website mentions problem: +1 point
- Reviews mention problem (>5 reviews): +1 point
- Job posting for problem-related role: +1 point
- Social mentions of problem: +0.5 points
- Total: 0-3.5 problem signal score

---

### 3. Score Each Prospect

**Calculate match score (0.0 to 1.0)** based on ICP fit:

#### Platform Match (0.3 max)
- Required platform confirmed: 0.3
- Alternative acceptable platform: 0.15
- Platform unknown/not detected: 0.0

**Verification**:
- Check website page source for platform indicators
- Look for "{platform} powered by" footer
- Check BuiltWith or similar tool mentions

#### Size Match (0.2 max)
- Within ICP employee range: 0.2
- Adjacent to range (±25%): 0.1
- Outside range: 0.0

**Verification**:
- LinkedIn company page employee count
- Crunchbase data
- "About Us" page size mentions
- News articles

#### Geography Match (0.2 max)
- Primary geography (ICP listed): 0.2
- Secondary geography: 0.1
- Outside target geographies: 0.0

**Verification**:
- Company website location
- LinkedIn company page HQ
- Shipping/contact page location
- Domain TLD (.com, .co.uk, .ca)

#### Problem Signal Strength (0.2 max)
- Strong signals (3+ indicators): 0.2
- Moderate signals (2 indicators): 0.1
- Weak signals (1 indicator): 0.05
- No signals detected: 0.0

**Verification**:
- Problem mentioned on website
- Reviews mentioning problem
- Job postings for problem-related roles
- Social mentions

#### Secondary Characteristics (0.1 max)
- Tech stack indicators present (Klaviyo, Stripe, etc.): +0.05
- Industry-specific signals: +0.05
- Growth indicators (hiring, funding): +0.05
- Recent activity (blog posts, news): +0.05
- Total capped at 0.1

**Total Score**: Sum of above (max 1.0)

#### Priority Tier Assignment

Based on total score:
- **Tier 1 (High Priority)**: Score >= 0.75
  - Strong ICP match across all criteria
  - Multiple problem signals
  - Recommended for immediate outreach

- **Tier 2 (Medium Priority)**: Score 0.5 - 0.74
  - Good ICP match, some gaps
  - At least one problem signal
  - Recommended for outreach after Tier 1

- **Tier 3 (Low Priority)**: Score 0.3 - 0.49
  - Partial ICP match
  - Weak or no problem signals
  - Consider for future outreach or nurture

- **Disqualified**: Score < 0.3
  - Poor ICP fit
  - Don't include in output list

---

### 4. Research Process (Step-by-Step)

For each company discovered:

**Step 1: Initial Discovery**
- Find company via industry/platform search
- Extract: name, domain, basic description

**Step 2: Platform Verification**
- Visit website
- Check page source or footer for platform
- Verify required platform (Shopify, WooCommerce, etc.)
- If platform doesn't match ICP → skip to next company

**Step 3: Size Verification**
- Search for employee count (LinkedIn, Crunchbase)
- Estimate if not public (team page, office size)
- If size significantly outside range → lower priority

**Step 4: Geography Verification**
- Check HQ location (website, LinkedIn)
- Verify primary markets served
- If geography outside ICP → deprioritize

**Step 5: Problem Signal Search**
- Search website for problem keywords
- Check reviews for problem mentions
- Search job postings for related roles
- Tally problem signal score (0-3.5)

**Step 6: Secondary Characteristics**
- Check for tech stack indicators
- Look for growth signals (hiring, funding, news)
- Note recent activity

**Step 7: Calculate Score & Priority**
- Sum all component scores (max 1.0)
- Assign priority tier (1, 2, 3, or disqualify)
- Record match reasoning

**Step 8: Document & Move to Next**
- Add to prospect list if score >= 0.3
- Record all findings
- Continue until target_count reached

---

### 5. Output Structured List

Create `research/customer/prospects/{segment}-prospects-{date}.csv`:

**CSV Columns**:
```csv
company_name,domain,industry,employee_count,revenue_estimate,geography,platform,match_score,platform_score,size_score,geography_score,problem_score,secondary_score,match_reason,problem_signals,priority_tier,segment,research_notes
```

**Example rows**:
```csv
{Company1},{domain1}.com,{Industry},{employees},$XM,{geo},{platform},0.85,0.30,0.20,0.20,0.15,0.00,"Perfect platform match ({platform}); size within range ({employees} employees); {geo}-based; strong problem signals ({observable indicators})","Website FAQ mentions {problem area}; Reviews mention {problem} ({N} reviews); Job posting for {Problem-related role} on {job board}; {Observable signal}",1,primary,"Excellent fit. {Problem area} mentioned in reviews. Recently posted {Problem-related role} suggesting {implication}."

{Company2},{domain2}.com,{Industry},{employees},$XM,{geo},{platform},0.70,0.30,0.20,0.20,0.00,0.00,"Perfect platform match; size within range; {geo}-based; no problem signals detected","No obvious problem signals on website; Standard policies; No relevant job postings found",2,primary,"Good ICP fit but lacking problem signals. Consider for outreach with generic value prop or monitor for problem signals."

{Company3},{domain3}.com,{Industry},{employees},$XM,{geo-secondary},{platform},0.60,0.30,0.20,0.10,0.00,0.00,"Perfect platform match; size within range; {geo-secondary}-based (secondary geography); no problem signals","No problem signals detected",3,secondary,"Good platform and size fit but secondary geography. Low priority unless expanding {geo-secondary} market."
```

Also create `research/customer/prospects/{segment}-prospects-{date}-summary.md`:

```markdown
# Prospect Research Summary - {Segment}
Generated: {date}

## Overview
- Total companies researched: {count}
- Qualified prospects: {count in CSV}
- Average match score: {avg score}

## Breakdown by Priority
- Tier 1 (High): {count} companies (score >= 0.75)
- Tier 2 (Medium): {count} companies (score 0.5-0.74)
- Tier 3 (Low): {count} companies (score 0.3-0.49)
- Disqualified: {count} companies (score < 0.3)

## Top 10 Prospects
1. {Company 1} - Score: {score} - {brief reason}
2. {Company 2} - Score: {score} - {brief reason}
...

## Problem Signal Analysis
- Companies with strong signals (3+): {count}
- Companies with moderate signals (2): {count}
- Companies with weak signals (1): {count}
- Companies with no signals: {count}

## Research Methodology
- Platform searches: {list sources used}
- Industry directories: {list sources}
- Problem signal searches: {list methods}
- Data sources: BuiltWith, LinkedIn, Crunchbase, Trustpilot, etc.

## Recommended Next Steps
1. Begin outreach to Tier 1 prospects ({count} companies)
2. Research contacts for Tier 1 using contact-finding subskill
3. Monitor Tier 2/3 for problem signals before outreach
4. Consider expanding search if Tier 1 count < 20

## Data Quality Notes
- Employee counts: {% with confirmed data}
- Platform confirmations: {% verified}
- Problem signals: {% with at least 1 signal}
```

---

### 6. Segmentation & Tagging

**Segment by ICP tier**:
- Primary segment: Best fit (all primary characteristics match)
- Secondary segment: Good fit (some secondary characteristics)

**Tag by problem signal strength**:
- `high-signal`: 3+ problem indicators
- `medium-signal`: 2 indicators
- `low-signal`: 1 indicator
- `no-signal`: 0 indicators

**Tag by urgency indicators**:
- `hiring`: Currently hiring for relevant roles
- `funded`: Recently raised funding (buying window)
- `growing`: Evidence of growth (20%+ headcount increase)

**Output tags in separate column or summary**:
```csv
tags
"high-signal,hiring"
"medium-signal"
"low-signal,funded,growing"
```

---

## Web Search Best Practices

### Discovery Searches (Finding Companies)

**Pattern 1: Platform + Industry**
```
"{platform} stores {industry}"
"{platform} {industry} brands"
"{platform} {industry} {category}"
```

**Pattern 2: Industry + Geography**
```
"{industry} e-commerce companies {geography}"
"DTC {industry} brands {region}"
"online {industry} retailers {city}"
```

**Pattern 3: Industry Lists/Rankings**
```
"top {industry} e-commerce brands {year}"
"best {platform} {industry} stores"
"fastest growing {industry} companies"
```

**Pattern 4: Technology + Industry**
```
"companies using {technology} {industry}"
"{platform} Plus {industry} customers"
"{payment provider} {industry} e-commerce"
```

### Verification Searches (Confirming Fit)

**Platform Verification**:
```
site:builtwith.com "{company name}"
"{company name}" powered by Shopify
"{company name}" e-commerce platform
```

**Size Verification**:
```
"{company name}" employees
"{company name}" team size
site:linkedin.com/company "{company name}"
site:crunchbase.com "{company name}"
```

**Geography Verification**:
```
"{company name}" headquarters
"{company name}" location
"{company name}" about us
```

### Problem Signal Searches

**Website Content**:
```
site:{domain} "returns"
site:{domain} "return policy"
site:{domain} FAQ
site:{domain} "sizing guide"
```

**Reviews**:
```
site:trustpilot.com "{company name}" returns
site:trustpilot.com "{company name}" sizing
"{company name}" reviews fit
```

**Job Postings**:
```
site:lever.co "{company name}" customer service
site:greenhouse.io "{company name}" returns
"{company name}" jobs careers
```

**Social Media**:
```
site:x.com "{company name}" returns
site:linkedin.com/company "{company name}"
```

---

## Scoring Algorithm Details

### Component Scores

**1. Platform Match (0.3 max)**:
```
IF platform = ICP.required_platform THEN 0.3
ELSE IF platform IN ICP.acceptable_platforms THEN 0.15
ELSE 0.0
```

**2. Size Match (0.2 max)**:
```
employee_count = verified count from LinkedIn/Crunchbase
ICP_min = ICP.company_size.min
ICP_max = ICP.company_size.max

IF ICP_min <= employee_count <= ICP_max THEN 0.2
ELSE IF (ICP_min * 0.75) <= employee_count <= (ICP_max * 1.25) THEN 0.1
ELSE 0.0
```

**3. Geography Match (0.2 max)**:
```
IF geography IN ICP.geography.primary THEN 0.2
ELSE IF geography IN ICP.geography.secondary THEN 0.1
ELSE 0.0
```

**4. Problem Signal Strength (0.2 max)**:
```
signal_count = 0
IF problem_mentioned_on_website THEN signal_count += 1
IF problem_in_reviews (>5 reviews) THEN signal_count += 1
IF problem_related_job_posting THEN signal_count += 1
IF social_mentions_problem THEN signal_count += 0.5

IF signal_count >= 3 THEN 0.2
ELSE IF signal_count >= 2 THEN 0.1
ELSE IF signal_count >= 1 THEN 0.05
ELSE 0.0
```

**5. Secondary Characteristics (0.1 max)**:
```
secondary_score = 0
IF tech_stack_match (Klaviyo, Stripe, etc.) THEN secondary_score += 0.05
IF industry_specific_signals THEN secondary_score += 0.05
IF growth_indicators (hiring, funding) THEN secondary_score += 0.05
IF recent_activity (blog, news) THEN secondary_score += 0.05

RETURN MIN(secondary_score, 0.1)
```

**Total Score**:
```
total = platform_score + size_score + geography_score + problem_score + secondary_score
```

**Priority Tier**:
```
IF total >= 0.75 THEN tier = 1 (High Priority)
ELSE IF total >= 0.5 THEN tier = 2 (Medium Priority)
ELSE IF total >= 0.3 THEN tier = 3 (Low Priority)
ELSE disqualify (don't include in output)
```

---

## Constraints & Quality Checks

**Observable Characteristics ONLY**:
- [ ] All scored criteria are verifiable via web search
- [ ] No psychographic traits ("innovative", "forward-thinking")
- [ ] All match reasons cite specific evidence

**Searchable Filters**:
- [ ] All ICP criteria map to web search queries
- [ ] Platform is verifiable (page source, BuiltWith)
- [ ] Size is confirmable (LinkedIn, Crunchbase, website)
- [ ] Geography is verifiable (website, LinkedIn)

**Calculable Scores**:
- [ ] Score components sum to total (no arbitrary scores)
- [ ] Match score is reproducible (same inputs → same score)
- [ ] Priority tier is objective (based on score threshold)

**Verifiable Problem Signals**:
- [ ] Problem signals cite specific sources (URL, review text, job posting)
- [ ] No assumptions ("they probably have this problem")
- [ ] Evidence is current (not outdated)

---

## Error Handling

**ICP file not found**:
```
ERROR: ICP not found at {icp_path}
Action: Generate ICP first using icp-generator skill
```

**No companies found**:
```
WARNING: No companies matching ICP filters found
Possible reasons:
- ICP filters too restrictive
- Industry/platform combination rare
- Geography too narrow
Action: Broaden search or adjust ICP criteria
```

**Low match scores across board**:
```
WARNING: Average match score < 0.5
{count} companies researched, {qualified_count} qualified
Possible reasons:
- ICP criteria misaligned with available companies
- Problem signals not detectable via web search
Action: Review ICP fit or adjust scoring weights
```

**Rate limiting / search issues**:
```
WARNING: Web search rate limited
Researched {count} of {target_count} companies
Action: Wait and resume, or use results gathered so far
```

---

## Limitations

**Claude can**:
- Search public web for companies matching ICP
- Verify observable characteristics (platform, size, geography)
- Detect problem signals from public content (website, reviews, job postings)
- Calculate objective match scores
- Prioritize prospects by ICP fit

**Claude cannot**:
- Access proprietary databases (BuiltWith full data, ZoomInfo, etc.)
- Guarantee employee count accuracy (estimates from public data)
- Access LinkedIn Sales Navigator filters directly
- Scrape protected content
- Verify revenue with certainty (public companies only)

**Best used when**:
- ICP characteristics are observable via public web
- Platform/technology is detectable
- Problem signals are publicly visible
- Target market has public web presence

**Consider manual prospecting when**:
- ICP requires proprietary data (exact revenue, private company details)
- Target companies have minimal web presence
- Need exhaustive list (100s of prospects) - Claude is better for targeted lists
- Need real-time database access (BuiltWith, ZoomInfo subscriptions)

---

## Success Criteria

Quality prospect research delivers:
1. **50+ qualified prospects** matching ICP (or target_count specified)
2. **>60% Tier 1/2 prospects** (score >= 0.5)
3. **Verifiable data** (all scores backed by evidence)
4. **Problem signals for >40%** of prospects (at least 1 signal)
5. **Actionable insights** (match reasons enable personalized outreach)

---

## References

Detailed methodologies in `references/`:
- `research-sources.md` - Web search patterns, tools, databases
- `company-scoring.md` - Scoring algorithm details and examples
- `problem-signal-detection.md` - Where to find evidence, what to look for
- `geographic-databases.md` - Regulatory/compliance databases for Detekta-style products
