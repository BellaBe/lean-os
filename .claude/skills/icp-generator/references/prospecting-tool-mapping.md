# Prospecting Tool Mapping

## Overview

This guide maps ICP characteristics to actual search queries in major prospecting tools. Each section provides exact syntax and filter options.

## Core Prospecting Tools

### 1. LinkedIn Sales Navigator

**Best for**: Company firmographics, employee roles, hiring signals, growth indicators

#### Company Search Filters

**Company Size**
```
Filter: "Company headcount"
Options:
  - 1-10
  - 11-50
  - 51-200
  - 201-500
  - 501-1,000
  - 1,001-5,000
  - 5,001-10,000
  - 10,001+

Example ICP Mapping:
ICP: "50-200 employees"
→ Sales Nav: Select "51-200"
```

**Industry**
```
Filter: "Industry"
Options: LinkedIn's standard industry categories
  - Computer Software
  - Internet
  - Information Technology & Services
  - Retail
  - Apparel & Fashion
  - Financial Services
  - [100+ more industries]

Example ICP Mapping:
ICP: "Fashion e-commerce"
→ Sales Nav: Select "Apparel & Fashion" + "Internet"
```

**Geography**
```
Filter: "Company headquarters location"
Options: Country, State/Province, City, Postal Code

Example ICP Mapping:
ICP: "US-based, primarily California and New York"
→ Sales Nav:
  - Country: United States
  - State: California, New York
```

**Revenue**
```
Filter: "Revenue"
Options:
  - <$1M
  - $1M - $10M
  - $10M - $50M
  - $50M - $100M
  - $100M - $500M
  - $500M - $1B
  - $1B+

Note: Revenue data is estimated/self-reported, not always accurate

Example ICP Mapping:
ICP: "$2M-$15M annual revenue"
→ Sales Nav: Select "$1M - $10M" + "$10M - $50M"
```

**Growth Signals**
```
Filter: "Company headcount growth" (6-month or 2-year)
Options:
  - Growing (general)
  - Growing fast (>20% growth)

Filter: "Hiring on LinkedIn"
Options: Filter by number of jobs posted

Example ICP Mapping:
ICP: "Fast-growing companies"
→ Sales Nav:
  - Headcount growth: "Growing fast"
  - Hiring on LinkedIn: ">10 jobs"
```

**Funding**
```
Filter: "Funding"
Options:
  - Seed
  - Series A
  - Series B
  - Series C+
  - Private Equity
  - IPO/Public

Example ICP Mapping:
ICP: "Early-stage funded startups"
→ Sales Nav: Select "Seed" + "Series A"
```

#### Lead/Contact Search Filters

**Job Titles**
```
Filter: "Title"
Search: Keyword search with Boolean logic

Example ICP Mapping:
Economic Buyer: "VP Operations, Director E-commerce"
→ Sales Nav:
  Title: "VP Operations" OR "Director Operations" OR "VP E-commerce" OR "Director E-commerce"
```

**Seniority Level**
```
Options:
  - Entry
  - Senior
  - Manager
  - Director
  - VP
  - CXO
  - Partner
  - Owner

Example ICP Mapping:
Buyer Persona: "Director level or above in Operations"
→ Sales Nav:
  - Seniority: Director, VP, CXO
  - Keywords: "Operations"
```

**Function**
```
Options:
  - Engineering
  - Operations
  - Sales
  - Marketing
  - Product Management
  - Finance
  - Customer Success
  - [etc.]

Example ICP Mapping:
Technical Buyer: "Engineering leadership"
→ Sales Nav:
  - Function: Engineering
  - Seniority: Director, VP, CXO
```

#### Advanced Filters

**Technologies Used**
```
Filter: "Company uses technology"
Search: Technology name (limited to LinkedIn's database)

Example:
ICP: "Uses Salesforce"
→ Sales Nav: Company uses technology: "Salesforce"

Note: Coverage is incomplete; use BuiltWith for better tech stack data
```

**Job Postings**
```
Filter: "Posted jobs in last [timeframe]"
Search: Keywords in job titles or descriptions

Example ICP Mapping:
Problem Signal: "Hiring for customer service (indicates high support burden)"
→ Sales Nav:
  - Posted jobs in last 90 days
  - Job title keywords: "Customer Service" OR "Customer Support" OR "CX"
```

### 2. BuiltWith

**Best for**: Website technology stack, platform identification, installed tools

#### Technology Search

**E-commerce Platforms**
```
Search: https://builtwith.com/websites-using/Shopify

Supported platforms:
  - Shopify
  - WooCommerce
  - Magento
  - BigCommerce
  - Salesforce Commerce Cloud
  - Custom platforms

Example ICP Mapping:
ICP: "Shopify stores"
→ BuiltWith: Search for "Shopify" technology
```

**Payment Processors**
```
Search: https://builtwith.com/websites-using/Stripe

Supported processors:
  - Stripe
  - PayPal
  - Braintree
  - Square
  - Authorize.net

Example ICP Mapping:
Signal: "Modern payment stack"
→ BuiltWith: Filter for "Stripe" or "Braintree"
```

**Analytics & Marketing Tools**
```
Technologies tracked:
  - Google Analytics
  - Segment
  - Amplitude
  - Mixpanel
  - Klaviyo (email marketing)
  - HubSpot
  - Marketo

Example ICP Mapping:
Signal: "Sophisticated marketing stack (suggests tool investment)"
→ BuiltWith:
  - Klaviyo (email)
  - Segment (data)
  - Google Analytics 4
```

**Geographic Filters**
```
Filter: "Country"
Options: All countries

Example:
ICP: "US-based Shopify stores"
→ BuiltWith:
  - Technology: Shopify
  - Country: United States
```

**Traffic Filters** (via BuiltWith Pro)
```
Options:
  - Low traffic
  - Medium traffic
  - High traffic
  - Very high traffic

Note: Requires paid BuiltWith Pro subscription

Example ICP Mapping:
ICP: "Established e-commerce sites with significant traffic"
→ BuiltWith Pro:
  - Technology: Shopify
  - Traffic: High or Very High
```

#### Advanced BuiltWith Queries

**Vertical Detection**
```
Some verticals can be detected via technology:
  - Fashion: Instagram Shopping, Pinterest Tag
  - SaaS: Stripe + Intercom
  - Publishing: WordPress + AdSense
  - Food/Delivery: Toast POS, DoorDash integration

Example:
ICP: "Fashion e-commerce"
→ BuiltWith:
  - Shopify + Instagram Shopping
  - Or: Shopify + Pinterest Tag
```

**Technology Combinations**
```
Advanced search allows Boolean logic:
  - Technology A AND Technology B
  - Technology A NOT Technology C

Example:
ICP: "Modern Shopify stores (not using old tracking)"
→ BuiltWith:
  - Shopify AND Google Analytics 4
  - NOT Google Analytics (Universal)
```

### 3. SimilarWeb

**Best for**: Website traffic estimates, engagement metrics, visitor geography

#### Traffic Estimates

**Global Rank**
```
Filter: "Global Rank"
Options: Rank ranges or specific thresholds

Example ICP Mapping:
ICP: "Established online presence"
→ SimilarWeb: Global Rank < 500,000
```

**Monthly Visits**
```
Metric: "Total Visits"
Options: Custom ranges

Example ICP Mapping:
ICP: "10K-100K monthly visitors"
→ SimilarWeb:
  - Total Visits: 10,000 - 100,000 per month
```

**Engagement Metrics**
```
Metrics available:
  - Pages per Visit
  - Avg. Visit Duration
  - Bounce Rate

Example ICP Mapping:
Signal: "High engagement (suggests quality traffic)"
→ SimilarWeb:
  - Pages per Visit: >3
  - Avg. Visit Duration: >2 minutes
  - Bounce Rate: <50%
```

#### Geographic Breakdown

**Traffic by Country**
```
View: "Geography" tab
Data: % of traffic from each country

Example ICP Mapping:
ICP: "Primarily US traffic"
→ SimilarWeb:
  - United States traffic: >70%
```

#### Traffic Sources

**Channel Distribution**
```
Channels:
  - Direct
  - Referral
  - Search (Organic)
  - Search (Paid)
  - Social
  - Email
  - Display Ads

Example ICP Mapping:
Signal: "Strong organic presence (suggests SEO investment)"
→ SimilarWeb:
  - Organic Search: >30% of traffic
```

#### Industry/Category

**Website Category**
```
Filter: "Category"
Options: SimilarWeb's category taxonomy

Example:
ICP: "E-commerce > Fashion & Apparel"
→ SimilarWeb: Filter by category "Shopping > Fashion and Apparel"
```

### 4. Crunchbase

**Best for**: Funding data, investor relationships, revenue estimates, founding date

#### Funding Filters

**Funding Stage**
```
Options:
  - Pre-Seed
  - Seed
  - Series A
  - Series B
  - Series C+
  - Private Equity
  - IPO/Public

Example ICP Mapping:
ICP: "Recently funded startups (have budget)"
→ Crunchbase:
  - Funding stage: Series A, Series B
  - Last funding: Within 12 months
```

**Total Funding Amount**
```
Filter: "Funding Total"
Options: Custom ranges

Example:
ICP: "Well-funded ($5M+) but not enterprise scale"
→ Crunchbase:
  - Funding Total: $5M - $50M
```

**Last Funding Date**
```
Filter: "Last Funding Date"
Options: Date ranges

Example ICP Mapping:
Signal: "Recent funding (buying window)"
→ Crunchbase:
  - Last Funding Date: Last 6 months
```

#### Company Filters

**Employee Count**
```
Filter: "Number of Employees"
Options: Ranges (similar to LinkedIn)

Example:
ICP: "50-200 employees"
→ Crunchbase: Employees: 51-100, 101-250
```

**Revenue Range**
```
Filter: "Estimated Revenue"
Options:
  - <$1M
  - $1M-$10M
  - $10M-$50M
  - $50M-$100M
  - $100M-$500M
  - $500M+

Note: Estimates, not always accurate

Example ICP Mapping:
ICP: "$2M-$15M revenue"
→ Crunchbase: Revenue: $1M-$10M, $10M-$50M
```

**Founded Date**
```
Filter: "Founded Date"
Options: Year ranges

Example ICP Mapping:
Signal: "Established but not legacy (past product-market fit)"
→ Crunchbase:
  - Founded: 2018-2021 (3-6 years old)
```

**Headquarters Location**
```
Filter: "Location"
Options: Country, State, City

Example:
ICP: "San Francisco Bay Area"
→ Crunchbase:
  - Location: San Francisco, Palo Alto, Mountain View, etc.
```

#### Investor Signals

**Investor Type**
```
View: "Investors" tab
Use: Identify quality of investors (tier-1 VCs suggest quality)

Example Signal:
"Funded by Sequoia, a16z, Accel" → High-quality startup
```

### 5. Google Search Operators

**Best for**: Problem signals, content verification, technology detection

#### Site-Specific Searches

**FAQ/About Pages**
```
Query: site:example.com "returns" OR "return policy"

Example ICP Mapping:
Problem Signal: "Mentions return rate on website"
→ Google: site:example.com ("high return rate" OR "return policy" OR "returns FAQ")
```

**Job Postings**
```
Query: site:lever.co OR site:greenhouse.io "company-name" "Customer Service"

Example ICP Mapping:
Signal: "Hiring for customer service (high support burden)"
→ Google:
  - site:lever.co "shopify-brand-name" ("Customer Service" OR "Support")
  - site:greenhouse.io "shopify-brand-name" ("Customer Service" OR "Support")
```

**Technology Stack**
```
Query: site:example.com "powered by Shopify"

Example:
Verify Platform: Is this a Shopify store?
→ Google: site:example.com ("powered by Shopify" OR "myshopify.com")
```

**Review Mentions**
```
Query: site:trustpilot.com OR site:reviews.io "company-name" "sizing"

Example ICP Mapping:
Problem Signal: "Customer complaints about fit/sizing"
→ Google:
  - site:trustpilot.com "brand-name" ("sizing" OR "fit" OR "too small" OR "too large")
```

### 6. Apollo.io

**Best for**: Combined company + contact data, technographics, intent signals

#### Company Filters

**Industry & Keywords**
```
Filter: "Industry" + "Keywords"
Options: Apollo's industry taxonomy + free-text

Example:
ICP: "E-commerce apparel"
→ Apollo:
  - Industry: Retail, Apparel
  - Keywords: "e-commerce", "online store"
```

**Technologies**
```
Filter: "Technologies Used"
Database: 100+ technologies tracked

Example:
ICP: "Shopify stores using Klaviyo"
→ Apollo:
  - Technologies: Shopify, Klaviyo
```

**Employee Count & Revenue**
```
Filters: "# Employees", "Revenue"
Options: Custom ranges

Example:
ICP: "50-200 employees, $2M-$15M revenue"
→ Apollo:
  - Employees: 50-200
  - Revenue: $1M-$10M
```

**Intent Signals** (Apollo Pro)
```
Filter: "Buying Intent"
Signals: Website visits, content downloads, searches

Example:
Signal: "Actively researching solutions"
→ Apollo: Show companies with recent buying intent signals
```

### 7. ZoomInfo

**Best for**: Enterprise contact data, org charts, technographics, scoops (news)

#### Advanced Filters

**Technographics**
```
Filter: "Installed Technologies"
Database: 15,000+ technologies

Example:
ICP: "Shopify Plus stores (enterprise)"
→ ZoomInfo: Installed Technologies: "Shopify Plus"
```

**Scoops (Trigger Events)**
```
Filter: "Scoops"
Events tracked:
  - New funding
  - Executive changes
  - Office openings
  - Hiring sprees
  - Product launches

Example ICP Mapping:
Trigger: "Recently raised funding (buying window)"
→ ZoomInfo: Scoops: "Recent funding" in last 90 days
```

**Org Chart Depth**
```
Feature: "Department Org Charts"
Use: Identify team size, structure, decision-makers

Example:
Verify: "Has dedicated operations team (5+ people)"
→ ZoomInfo: View Operations department org chart
```

## Multi-Tool Workflows

### Workflow 1: Shopify Store with Problem Signals

**Step 1 - BuiltWith**: Find Shopify stores in target geography
```
Technology: Shopify
Country: United States
Traffic: Medium to High
→ Export list of 500 Shopify sites
```

**Step 2 - SimilarWeb**: Filter by traffic quality
```
Import list from BuiltWith
Filter:
  - Monthly visits: 10K-100K
  - Pages per visit: >3 (engaged visitors)
→ Reduces to 200 sites
```

**Step 3 - Google Search**: Check for problem signals
```
For each site, search:
  site:[domain] ("returns" OR "return policy")
  site:[domain] ("sizing" OR "fit guide")

Flag sites mentioning these topics prominently
→ Identifies 75 sites with problem awareness
```

**Step 4 - LinkedIn Sales Navigator**: Find decision-makers
```
Search for companies (by name or domain)
Filter:
  - Title: "VP Operations" OR "Director E-commerce" OR "Founder"
  - Seniority: Director, VP, CXO

→ Build list of 75 specific contacts at qualified companies
```

### Workflow 2: Fast-Growing SaaS Companies

**Step 1 - Crunchbase**: Find recently funded companies
```
Filters:
  - Funding stage: Series A, Series B
  - Last funding: Last 12 months
  - Industry: SaaS, B2B
  - Employees: 50-200
→ List of 300 companies
```

**Step 2 - LinkedIn Sales Navigator**: Verify growth signals
```
Import company list
Additional filters:
  - Headcount growth: Growing fast
  - Hiring on LinkedIn: >5 jobs posted
→ Reduces to 120 companies showing growth
```

**Step 3 - Apollo/ZoomInfo**: Check tech stack
```
Import company list
Filter:
  - Technologies: Salesforce, HubSpot (suggests sales maturity)
  - NOT using [competitor]
→ Final list of 80 qualified companies
```

**Step 4 - LinkedIn**: Identify personas
```
For each company, find:
  - Economic buyer: VP Sales, CRO
  - Technical buyer: VP Engineering, CTO
  - Champion: Sales Ops Manager
→ 240 specific contacts (3 per company)
```

## Tool Selection Matrix

| ICP Characteristic | Best Tool(s) | Why |
|-------------------|--------------|-----|
| Company size | LinkedIn, Crunchbase, ZoomInfo | Most accurate headcount data |
| Revenue | Crunchbase, ZoomInfo, LinkedIn | Estimates available |
| Geography | All tools | Standard filter |
| Industry/Vertical | LinkedIn, Apollo, Crunchbase | Standard taxonomies |
| E-commerce platform | BuiltWith | Dedicated technology detection |
| Tech stack | BuiltWith, Apollo, ZoomInfo | Varies by technology |
| Website traffic | SimilarWeb | Only tool with traffic data |
| Funding stage | Crunchbase | Most comprehensive funding data |
| Growth signals | LinkedIn (hiring), Crunchbase (funding) | Real-time signals |
| Problem signals | Google Search, review sites | Manual verification |
| Buyer contacts | LinkedIn, Apollo, ZoomInfo | Contact databases |
| Intent signals | Apollo, ZoomInfo, 6sense | Intent platforms |

## Common Limitations & Workarounds

### Limitation 1: Technology Detection Coverage
**Issue**: BuiltWith doesn't detect all technologies
**Workaround**:
- Use Google: `site:example.com "powered by [platform]"`
- Check page source for platform indicators
- Use multiple tools (BuiltWith + Wappalyzer + Apollo)

### Limitation 2: Revenue Data Accuracy
**Issue**: Revenue estimates are often wrong (especially for private companies)
**Workaround**:
- Use traffic as proxy: SimilarWeb traffic correlates with revenue
- Use employee count: 50 employees ≈ $5-10M revenue (rough)
- Use funding: Series A ≈ $1-5M revenue, Series B ≈ $5-15M

### Limitation 3: Problem Signal Automation
**Issue**: Most tools can't search website content for problem mentions
**Workaround**:
- Manual Google searches: `site:example.com "[problem keyword]"`
- Scrape FAQ/About pages programmatically
- Monitor review sites (Trustpilot, G2) manually

### Limitation 4: Real-Time Data Lag
**Issue**: Company data can be 3-6 months outdated
**Workaround**:
- Check LinkedIn for recent posts/updates
- Verify on company website
- Use ZoomInfo "Scoops" for recent events

## Output Format for ICP YAML

When translating ICP → tool queries, document in YAML:

```yaml
prospecting_queries:
  builtwith:
    - query: "Shopify stores in United States"
      filters:
        - "Technology: Shopify"
        - "Country: United States"
        - "Traffic: Medium or High"
      url: "https://builtwith.com/shopify"

  linkedin_sales_navigator:
    - company_filters:
        industry: ["Apparel & Fashion", "Retail"]
        company_size: "51-200 employees"
        geography: "United States"
      contact_filters:
        title: ["VP Operations", "Director E-commerce", "Founder"]
        seniority: ["Director", "VP", "CXO"]

  similarweb:
    - filters:
        monthly_visits: "10,000 - 100,000"
        category: "Shopping > Fashion and Apparel"
        geography: ">70% United States traffic"

  google_search:
    - query: 'site:{domain} ("returns" OR "return policy" OR "sizing issues")'
      purpose: "Verify problem awareness on website"
```

## Quick Reference: Search Syntax

**LinkedIn Sales Navigator**: Use AND/OR in text fields
```
Title: "VP Operations" OR "Director Operations"
Keywords: "e-commerce" AND "returns"
```

**BuiltWith**: Filter-based (no search syntax needed)

**SimilarWeb**: Filter-based (no search syntax needed)

**Google**: Use operators
```
site:example.com         → Search specific site
"exact phrase"           → Exact match
OR                       → Either term
-excluded                → Exclude term
```

**Apollo/ZoomInfo**: Filter-based with keyword search

---

**Remember**: The best prospecting workflow uses MULTIPLE tools in sequence:
1. Broad filter (BuiltWith, Crunchbase) → Generate list
2. Refinement (SimilarWeb, LinkedIn) → Qualify list
3. Verification (Google, manual checks) → Validate problem
4. Contact discovery (LinkedIn, Apollo) → Find buyers
