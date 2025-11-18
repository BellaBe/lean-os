# Company Scoring Methodology

## Scoring Algorithm

Total score: 0.0 to 1.0 (sum of component scores)

### Component 1: Platform Match (0.3 max)

**Scoring**:
- Required platform confirmed: **0.3**
- Acceptable alternative platform: **0.15**
- Platform unknown or wrong: **0.0**

**Examples** (Shopify required):
```
Company A: Shopify confirmed (page source) → 0.3
Company B: WooCommerce (ICP lists as acceptable) → 0.15
Company C: Magento (not in ICP) → 0.0
Company D: Platform unknown (can't verify) → 0.0
```

**Verification methods**:
1. Page source inspection (look for platform-specific code)
2. Footer "Powered by {platform}" badge
3. URL patterns (myshopify.com subdomain)
4. BuiltWith search results
5. Stack Share listings

---

### Component 2: Size Match (0.2 max)

**ICP range**: e.g., 50-200 employees

**Scoring**:
- Within range (50-200): **0.2**
- Adjacent to range (±25%): **0.1**
  - 38-50 or 200-250 employees
- Outside range: **0.0**

**Examples** (ICP: 50-200 employees):
```
Company A: 75 employees (LinkedIn) → 0.2
Company B: 45 employees (25% below min) → 0.1
Company C: 220 employees (10% above max) → 0.1
Company D: 15 employees (well below) → 0.0
Company E: 500 employees (well above) → 0.0
```

**Verification methods**:
1. LinkedIn company page ("XX employees")
2. Crunchbase employee range
3. About Us page team size
4. News articles mentioning headcount
5. Estimate from office size/funding

---

### Component 3: Geography Match (0.2 max)

**Scoring**:
- Primary geography (ICP primary): **0.2**
- Secondary geography (ICP secondary): **0.1**
- Outside target geographies: **0.0**

**Examples** (ICP: Primary=US,CA,UK; Secondary=AU,NZ):
```
Company A: US (confirmed HQ) → 0.2
Company B: UK (confirmed) → 0.2
Company C: Australia (secondary) → 0.1
Company D: Germany (not in ICP) → 0.0
```

**Verification methods**:
1. Website contact/about page
2. LinkedIn company HQ location
3. Domain TLD (.com, .co.uk, .ca)
4. Shipping/terms page

---

### Component 4: Problem Signal Strength (0.2 max)

**Signal counting**:
- Website mentions problem: +1 point
- Reviews mention problem (>5 reviews): +1 point
- Job posting for problem role: +1 point
- Social mentions problem: +0.5 points
- Max: 3.5 points

**Scoring**:
- Strong signals (3+ points): **0.2**
- Moderate signals (2 points): **0.1**
- Weak signals (1 point): **0.05**
- No signals: **0.0**

**Examples** (Returns/sizing problem for GlamYouUp):
```
Company A:
- FAQ mentions sizing: +1
- 18 Trustpilot reviews about fit: +1
- Hiring "Returns Coordinator": +1
- Twitter mentions: +0.5
Total: 3.5 points → Score: 0.2

Company B:
- Generous return policy (60 days): +1
- 3 reviews mention sizing (< 5 threshold): +0
Total: 1 point → Score: 0.05

Company C:
- No problem signals found: 0 points → Score: 0.0
```

**Verification methods**:
1. site:{domain} "{problem keyword}"
2. site:trustpilot.com "{company}" {problem}
3. site:lever.co "{company}" {role}
4. site:twitter.com "{company}" {problem}

---

### Component 5: Secondary Characteristics (0.1 max)

**Scoring** (capped at 0.1):
- Tech stack match (Klaviyo, Stripe, etc.): +0.05
- Industry-specific signals: +0.05
- Growth indicators (hiring, funding): +0.05
- Recent activity (blog, news): +0.05

**Examples**:
```
Company A:
- Uses Klaviyo (found in page source): +0.05
- Fashion industry signals (styling quiz): +0.05
- Hiring (5 open roles): +0.05
- Blog updated last week: +0.05
Total: 0.20 → Capped at 0.1

Company B:
- No tech stack indicators: +0.0
- Industry match confirmed: +0.05
Total: 0.05
```

**Verification methods**:
1. Page source for tech stack
2. Careers page for hiring
3. Crunchbase for funding
4. Blog/news for activity

---

## Priority Tier Assignment

**Based on total score**:

### Tier 1: High Priority (Score >= 0.75)
- **Characteristics**: Strong match across all criteria
- **Action**: Immediate outreach
- **Expected conversion**: 15-20%

**Example**:
```
Company: ChicThreads
Platform: 0.3 (Shopify confirmed)
Size: 0.2 (45 employees, in range)
Geography: 0.2 (US)
Problem: 0.2 (3.5 problem signals)
Secondary: 0.05 (uses Klaviyo)
Total: 0.95 → Tier 1
```

### Tier 2: Medium Priority (Score 0.5 - 0.74)
- **Characteristics**: Good match, some gaps
- **Action**: Outreach after Tier 1
- **Expected conversion**: 8-12%

**Example**:
```
Company: TrendyStyles
Platform: 0.3 (Shopify confirmed)
Size: 0.2 (120 employees, in range)
Geography: 0.2 (US)
Problem: 0.0 (no signals)
Secondary: 0.0
Total: 0.7 → Tier 2
```

### Tier 3: Low Priority (Score 0.3 - 0.49)
- **Characteristics**: Partial match, weak signals
- **Action**: Nurture or future outreach
- **Expected conversion**: 3-5%

**Example**:
```
Company: UrbanWear
Platform: 0.3 (Shopify confirmed)
Size: 0.1 (35 employees, slightly below)
Geography: 0.1 (UK, secondary)
Problem: 0.0 (no signals)
Secondary: 0.0
Total: 0.5 → Tier 3 (on the edge)
```

### Disqualified (Score < 0.3)
- **Characteristics**: Poor fit
- **Action**: Don't include in output

**Example**:
```
Company: FastFashion
Platform: 0.0 (Magento, not in ICP)
Size: 0.0 (2000 employees, enterprise)
Geography: 0.2 (US)
Problem: 0.0
Secondary: 0.0
Total: 0.2 → Disqualified
```

---

## Match Reason Documentation

**For each prospect, document WHY they scored as they did**:

### High Score Example (0.85)
```
Match Reason:
"Perfect platform match (Shopify confirmed in page source); size within ICP range (45 employees per LinkedIn); US-based (primary geography); strong problem signals detected (FAQ mentions sizing issues, 18 Trustpilot reviews about fit problems, actively hiring Returns Coordinator role on Lever, 60-day return policy suggests high return rate); uses Klaviyo for email marketing (tech stack match)."

Problem Signals:
"Website FAQ section has 'How do I find my size?' and 'What if it doesn't fit?' questions; Trustpilot has 18 reviews (out of 87 total) mentioning 'too small', 'sizing off', or 'fit issues'; Lever job posting for 'Returns Coordinator' posted 2 weeks ago; Return policy is 60 days free returns (vs industry standard 30 days, suggesting high return volume)."
```

### Medium Score Example (0.70)
```
Match Reason:
"Perfect platform match (Shopify); size within range (120 employees); US-based; no problem signals detected on website, reviews, or job postings; standard 30-day return policy; no relevant customer service roles posted."

Problem Signals:
"No obvious problem signals found. May not be experiencing significant pain or problem is not publicly visible."
```

### Low Score Example (0.50)
```
Match Reason:
"Platform match (Shopify); size slightly below range (35 employees, ICP is 50-200); UK-based (secondary geography, primary is US); no problem signals."

Problem Signals:
"None detected."
```

---

## Scoring Edge Cases

### Unknown Employee Count
**Approach**: Estimate from available signals
- Team page photos: Count visible employees
- Office size mentions: "small office" = <50, "multiple offices" = >100
- Funding stage: Seed = 5-15, Series A = 20-50, Series B = 50-200
- Revenue: $1M-$5M ≈ 10-50 employees, $5M-$15M ≈ 50-150 employees

**Scoring**: Use conservative estimate, note uncertainty in research notes

### Platform Unknown
**Approach**: Try to verify through multiple methods
- Page source inspection
- BuiltWith search
- Contact form inspection (Shopify forms have specific format)

**Scoring**: If truly unknown, score 0.0 for platform (can't confirm fit)

### Mixed Geography (HQ vs Markets)
**Approach**: Prioritize where decision-makers are located
- HQ in US, sells globally → Score as US
- HQ in UK, US subsidiary → Score as UK (decision-makers likely there)

**Scoring**: Use HQ geography unless explicit US operations with autonomy

### Conflicting Data Sources
**Approach**: Prioritize source reliability
1. LinkedIn (most current, self-reported)
2. Crunchbase (reliable for funded companies)
3. News articles (depends on date, verify currency)
4. Website (may be outdated)

**Scoring**: Use most reliable source, note conflict in research notes

---

## Quality Validation

**Before finalizing score**, verify:
- [ ] All score components sum correctly (no arithmetic errors)
- [ ] Match reason cites specific evidence (not assumptions)
- [ ] Problem signals include source/URL
- [ ] Priority tier matches score threshold
- [ ] Research notes document any uncertainty

**Red flags requiring manual review**:
- Score doesn't match documented evidence
- Conflicting data not resolved
- Problem signals vague or unsourced
- Score components don't add up to total
