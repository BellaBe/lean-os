# Company Scoring Methodology

## Scoring Algorithm

Total score: 0.0 to 1.0 (sum of component scores)

### Component 1: Platform Match (0.3 max)

**Scoring**:
- Required platform confirmed: **0.3**
- Acceptable alternative platform: **0.15**
- Platform unknown or wrong: **0.0**

**Examples** ({required platform}):
```
Company A: {required platform} confirmed (page source) → 0.3
Company B: {acceptable alternative platform} (ICP lists as acceptable) → 0.15
Company C: {incompatible platform} (not in ICP) → 0.0
Company D: Platform unknown (can't verify) → 0.0
```

**Verification methods**:
1. Page source inspection (look for platform-specific code)
2. Footer "Powered by {platform}" badge
3. URL patterns ({platform-specific subdomain})
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

**Examples** ({Problem area} for {Product Name}):
```
Company A:
- FAQ mentions {problem}: +1
- 18 Trustpilot reviews about {problem}: +1
- Hiring "{Problem-related role}": +1
- Twitter mentions: +0.5
Total: 3.5 points → Score: 0.2

Company B:
- {Problem indicator} (60 days): +1
- 3 reviews mention {problem} (< 5 threshold): +0
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
Company: {Customer}
Platform: 0.3 ({required platform} confirmed)
Size: 0.2 (45 employees, in range)
Geography: 0.2 ({primary geography})
Problem: 0.2 (3.5 problem signals)
Secondary: 0.05 (uses {tech stack tool})
Total: 0.95 → Tier 1
```

### Tier 2: Medium Priority (Score 0.5 - 0.74)
- **Characteristics**: Good match, some gaps
- **Action**: Outreach after Tier 1
- **Expected conversion**: 8-12%

**Example**:
```
Company: {Customer}
Platform: 0.3 ({required platform} confirmed)
Size: 0.2 (120 employees, in range)
Geography: 0.2 ({primary geography})
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
Company: {Customer}
Platform: 0.3 ({required platform} confirmed)
Size: 0.1 (35 employees, slightly below)
Geography: 0.1 ({secondary geography})
Problem: 0.0 (no signals)
Secondary: 0.0
Total: 0.5 → Tier 3 (on the edge)
```

### Disqualified (Score < 0.3)
- **Characteristics**: Poor fit
- **Action**: Don't include in output

**Example**:
```
Company: {Customer}
Platform: 0.0 ({incompatible platform}, not in ICP)
Size: 0.0 (2000 employees, enterprise)
Geography: 0.2 ({primary geography})
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
"Perfect platform match ({required platform} confirmed in page source); size within ICP range (45 employees per LinkedIn); US-based (primary geography); strong problem signals detected (FAQ mentions {problem area}, 18 Trustpilot reviews about {problem}, actively hiring {Problem-related role} role on Lever, {problem indicator} suggests high {metric} rate); uses {tech stack tool} for {function} (tech stack match)."

Problem Signals:
"Website FAQ section has '{Problem question 1}' and '{Problem question 2}' questions; Trustpilot has 18 reviews (out of 87 total) mentioning '{problem keyword 1}', '{problem keyword 2}', or '{problem keyword 3}'; Lever job posting for '{Problem-related role}' posted 2 weeks ago; {Problem indicator} (vs industry standard, suggesting high {metric})."
```

### Medium Score Example (0.70)
```
Match Reason:
"Perfect platform match ({required platform}); size within range (120 employees); {primary geography}-based; no problem signals detected on website, reviews, or job postings; standard {policy}; no relevant customer service roles posted."

Problem Signals:
"No obvious problem signals found. May not be experiencing significant pain or problem is not publicly visible."
```

### Low Score Example (0.50)
```
Match Reason:
"Platform match ({required platform}); size slightly below range (35 employees, ICP is 50-200); {secondary geography}-based (secondary geography, primary is {primary geography}); no problem signals."

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
- HQ in {geography A}, sells globally → Score as {geography A}
- HQ in {geography B}, {geography A} subsidiary → Score as {geography B} (decision-makers likely there)

**Scoring**: Use HQ geography unless explicit {target geography} operations with autonomy

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
