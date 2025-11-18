# Research Sources & Search Patterns

## Overview

Systematic web search patterns for finding companies that match ICP observable characteristics.

## Primary Discovery Sources

### 1. Platform-Specific Discovery

**BuiltWith (via web search)**:
```
Search: site:builtwith.com Shopify {industry}
Search: "companies using {platform}" {industry}
```

**Stack Share**:
```
Search: site:stackshare.io {platform} {technology}
```

### 2. Industry Directories

**Fashion/Apparel**:
- "top fashion e-commerce brands 2024"
- "DTC fashion companies United States"
- "Shopify fashion stores list"

**Financial Services**:
- "SEC registered investment advisors {state}"
- "RIA firms {city}"
- "financial advisory companies"

**General B2B SaaS**:
- "{industry} software companies"
- "B2B {category} vendors"
- "{industry} SaaS list"

### 3. Company Size Verification

**LinkedIn**:
```
Search: site:linkedin.com/company "{company name}"
Look for: "XX employees on LinkedIn"
```

**Crunchbase**:
```
Search: site:crunchbase.com "{company name}"
Look for: Employee count, funding, revenue estimates
```

**Company Website**:
- About/Team page employee photos
- Office size mentions
- "We're a team of X people"

### 4. Geographic Databases

**US Companies**:
- Business directories by state
- Chamber of Commerce listings
- Local business databases

**Regulatory (Detekta example)**:
- SEC IARD database (financial advisors)
- State licensing boards
- Professional association directories

### 5. Technology Stack Detection

**Website Inspection**:
- View page source for platform indicators
- Check footer for "Powered by {platform}"
- Look for platform-specific code patterns

**Third-Party Tools (via search)**:
```
Search: "{company name}" technology stack
Search: "{company name}" uses {technology}
```

## Problem Signal Sources

### Website Content

**Direct Search**:
```
Search: site:{domain} "{problem keyword}"
Search: site:{domain} FAQ
Search: site:{domain} "return policy"
```

**What to look for**:
- FAQ sections mentioning problem
- Policy pages addressing problem
- Blog posts discussing problem
- Help documentation for problem

### Review Sites

**Trustpilot**:
```
Search: site:trustpilot.com "{company name}" {problem keyword}
```

**Google Reviews**:
```
Search: "{company name}" reviews {problem keyword}
```

**Industry-Specific Review Sites**:
- G2/Capterra for B2B SaaS
- Yelp for local services
- Better Business Bureau

### Job Postings

**Job Boards**:
```
Search: site:lever.co "{company name}" {role}
Search: site:greenhouse.io "{company name}" {role}
Search: "{company name}" careers {role}
```

**Roles indicating problems**:
- "Customer Service" (high support volume)
- "Returns Coordinator" (high return rates)
- "Compliance Manager" (regulatory issues)
- "Operations" (scaling challenges)

### Social Media

**Twitter/X**:
```
Search: site:twitter.com "{company name}" {problem keyword}
```

**LinkedIn**:
```
Search: site:linkedin.com/company "{company name}"
Look for: Company updates mentioning challenges
```

## Search Query Patterns

### Discovery Patterns

**Platform + Industry**:
```
"Shopify stores fashion"
"WooCommerce {industry} brands"
"{platform} customers {industry}"
```

**Industry + Geography**:
```
"{industry} companies {city}"
"{industry} {state} businesses"
"top {industry} brands {country}"
```

**Size + Industry**:
```
"small {industry} companies"
"mid-size {industry} firms"
"{industry} startups {geography}"
```

### Verification Patterns

**Platform Confirmation**:
```
site:builtwith.com "{company name}"
"{company name}" powered by {platform}
"{company name}" e-commerce platform
```

**Size Confirmation**:
```
"{company name}" employees
"{company name}" team size
"{company name}" LinkedIn company size
```

**Geography Confirmation**:
```
"{company name}" headquarters
"{company name}" location
"{company name}" contact us
```

### Problem Signal Patterns

**Website Problem Detection**:
```
site:{domain} "returns"
site:{domain} "return policy"
site:{domain} "sizing guide"
site:{domain} FAQ
```

**Review Problem Detection**:
```
site:trustpilot.com "{company name}" {problem}
"{company name}" reviews {problem}
```

**Job Posting Problem Detection**:
```
site:lever.co OR site:greenhouse.io "{company name}" "{role}"
"{company name}" jobs {role}
```

## Data Quality Indicators

**High Confidence**:
- LinkedIn company page (employee count)
- Crunchbase listing (funding, size)
- SEC/regulatory filings
- Direct website About page

**Medium Confidence**:
- News articles mentioning size
- Industry reports
- Third-party estimates
- Inference from other signals

**Low Confidence**:
- No public data available
- Conflicting sources
- Outdated information
- Estimates only

## Search Tips

**Boolean Operators**:
- Use quotes for exact phrases: "Shopify stores"
- Use OR for alternatives: (Shopify OR WooCommerce)
- Use site: for specific domains: site:linkedin.com

**Time Constraints**:
- Add "2024" or "2023" for recent results
- Use "recent" or "latest" for current data

**Exclude Noise**:
- Use -word to exclude: "fashion brands" -blog
- Exclude job boards if looking for company pages: -indeed -glassdoor
