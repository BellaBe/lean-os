# B2B vs B2C ICP Patterns

## Overview

While Pete Kazanjy's framework emphasizes **observable characteristics** for both B2B and B2C, the *types* of characteristics differ significantly.

**Key insight**: Even B2C ICPs should be observable and quantifiable, not psychographic.

## B2B ICP Characteristics

### Primary Focus: Company Characteristics

**Core components**:
1. Firmographics (company attributes)
2. Technographics (technology stack)
3. Organizational structure (teams, roles)
4. Behavioral signals (hiring, funding, partnerships)

### Firmographics

**Observable B2B characteristics**:
```yaml
company_size:
  employees: "50-200"
  revenue: "$2M-$15M ARR"
  customers: "100-1,000 active customers"

geography:
  headquarters: "US, CA, UK"
  markets_served: "English-speaking countries"

industry:
  naics: ["448", "454"]  # Clothing, Nonstore retail
  g2_category: "E-commerce Platforms"

maturity:
  founded: "2018-2022" (3-6 years old)
  stage: "Series A to Series B"
  funding_total: "$5M-$30M"
```

**Why these work**: All searchable in LinkedIn, Crunchbase, company websites

### Technographics

**Observable B2B tech stack**:
```yaml
required_platforms:
  - "Shopify" (via BuiltWith)
  - "Stripe" (via BuiltWith)

tech_stack_indicators:
  - "Klaviyo" (email marketing sophistication)
  - "Segment" (data infrastructure)
  - "Zendesk" (customer support scale)

api_requirements:
  - "REST API documented publicly"
  - "Webhooks supported"
```

**Why these work**: BuiltWith, job postings, tech blogs

### Organizational Structure

**Observable team characteristics**:
```yaml
team_structure:
  operations: "3-8 people" (per LinkedIn)
  customer_success: ">5% of headcount"
  engineering: "10-30 engineers"

hiring_signals:
  - "5+ open roles currently"
  - "Customer Service Manager role posted"
  - "Operations Lead role posted"

decision_makers:
  economic_buyer: "VP Operations, COO, Director E-commerce"
  technical_buyer: "CTO, VP Engineering"
  champion: "Operations Manager, E-commerce Manager"
```

**Why these work**: LinkedIn team pages, job postings

### Behavioral Signals

**Observable B2B behaviors**:
```yaml
growth_signals:
  - "20%+ headcount growth in 6 months"
  - "Raised funding in last 12 months"
  - "Expanded to new market/geography"

problem_signals:
  - "Mentions 'returns' on FAQ page"
  - "Job posting for Returns Coordinator"
  - "Trustpilot reviews mention sizing issues"

sophistication_signals:
  - "Published API documentation"
  - "Engineering blog updated monthly"
  - "Case studies on website"
```

**Why these work**: Public data, verifiable

---

## B2C ICP Characteristics

### Primary Focus: Consumer Demographics & Behaviors

**Core components**:
1. Demographics (age, location, income)
2. Behavioral patterns (purchase history, engagement)
3. Psychographics (but ONLY if quantifiable!)
4. Channel/platform usage

**Critical difference**: For B2C, you're profiling the END USER, not a company. But characteristics must STILL be observable.

### Demographics (Observable)

**Observable B2C demographics**:
```yaml
age_range: "25-45"
  verification: "Facebook Ads targeting data"

gender: "Female (70%), Male (30%)"
  verification: "Google Analytics demographics"

geography: "US urban areas, household income >$75K"
  verification: "Zip code analysis, census data"

life_stage: "Parents with children under 10"
  verification: "Survey data, purchase patterns"
```

**Why these work**: Advertising platforms, analytics, survey data

### Behavioral Patterns (Observable)

**Observable B2C behaviors**:
```yaml
purchase_frequency:
  - "Buys fashion items 2-4x per quarter"
  verification: "Transaction history, industry benchmarks"

channel_preference:
  - "Online shoppers (not in-store)"
  verification: "E-commerce transaction data"

brand_loyalty:
  - "Repeat customers (3+ purchases)"
  verification: "Customer database"

price_sensitivity:
  - "Average order value: $80-$150"
  verification: "Transaction data"

device_usage:
  - "70% mobile, 30% desktop"
  verification: "Google Analytics"
```

**Why these work**: First-party data, analytics platforms

### Psychographics (ONLY if Quantifiable)

**❌ BAD (Unobservable)**:
- "Values sustainability"
- "Cares about fashion"
- "Trend-conscious consumers"

**✓ GOOD (Observable proxies)**:
```yaml
sustainability_signals:
  - "Has purchased from sustainable brands (Reformation, Patagonia)"
  verification: "Purchase history, lookalike audiences"

  - "Engaged with sustainability content"
  verification: "Facebook engagement data"

  - "Searches for 'sustainable fashion' keywords"
  verification: "Google search behavior"

fashion_engagement:
  - "Follows 5+ fashion influencers on Instagram"
  verification: "Instagram interest targeting"

  - "Reads fashion blogs (Refinery29, Who What Wear)"
  verification: "Web traffic data, ad targeting"

  - "Engages with fashion content on Pinterest"
  verification: "Pinterest analytics"
```

**Why these work**: Ad platform targeting, behavioral data

### Channel/Platform Usage (Observable)

**Observable B2C channels**:
```yaml
social_media_usage:
  - "Active on Instagram (daily usage)"
  verification: "Instagram ad targeting data"

  - "Pinterest user (fashion/style boards)"
  verification: "Pinterest audience insights"

content_consumption:
  - "Reads fashion blogs/publications"
  verification: "Referral traffic, content partnerships"

  - "Watches fashion YouTube channels"
  verification: "YouTube ad targeting"

shopping_behavior:
  - "Uses mobile apps for shopping"
  verification: "App download data"

  - "Engages with email marketing (>20% open rate)"
  verification: "Email marketing data"
```

**Why these work**: Platform data, first-party data

---

## Hybrid Model: B2B Product with B2C End Users

**Example**: GlamYouUp (AI fitting room for fashion brands)

### Dual ICP Approach

**ICP #1: B2B Customer (The Fashion Brand)**

```yaml
# This is who BUYS the product
firmographics:
  company_size: "20-150 employees"
  revenue: "$2M-$15M ARR"
  industry: "Fashion & Apparel e-commerce"
  platform: "Shopify"

problem_signals:
  - "Return rate 15%+"
  - "Hiring for customer service/returns roles"

buyer_personas:
  economic_buyer: "VP Operations, COO"
  technical_buyer: "CTO, Engineering Lead"
```

**ICP #2: B2C End User (The Fashion Shopper)**

```yaml
# This is who USES the product (influences buying decision)
demographics:
  age: "25-45"
  gender: "Female (primary)"
  geography: "US urban areas"

behaviors:
  - "Online fashion shoppers"
  - "Return items due to fit issues"
  - "Use mobile for shopping"

channels:
  - "Instagram active users"
  - "Reads fashion blogs"
```

### How They Connect

**B2B ICP** → Who you SELL to
**B2C ICP** → Informs product-market fit and messaging

**Example decision flow**:
1. Prospect fashion brand (B2B ICP)
2. Verify their customer base matches B2C ICP
   - "What demographics are your customers?"
   - "What's your return rate by customer segment?"
3. If B2C end users match your ICP → Strong fit
4. If mismatch (e.g., they sell to 60+ age range) → Deprioritize

**B2C ICP influences B2B qualification**:
```yaml
qualification_questions:
  - "What's the age range of your typical customer?"
    qualified: "25-45" (matches our B2C ICP)
    deprioritize: "18-24 or 50+" (outside our B2C ICP)

  - "What percentage of your customers shop on mobile?"
    qualified: ">60% mobile"
    deprioritize: "<40% mobile"

  - "What's your return rate?"
    qualified: "15%+ returns" (end users have fit issues)
    deprioritize: "<10% returns"
```

---

## B2B2C Pattern

**Definition**: You sell to a business (B2B), who serves consumers (B2C). Your product affects the end consumer experience.

**Examples**:
- Payment processors (sell to merchants, serve shoppers)
- E-commerce plugins (sell to brands, serve customers)
- Review platforms (sell to businesses, engage consumers)

### Dual ICP Requirements

**B2B ICP (Direct Customer)**:
- Observable company characteristics
- Technographic requirements
- Organizational readiness

**B2C ICP (End User)**:
- Observable demographics
- Behavioral patterns
- Channel usage

**Critical**: Both must be observable. Don't say "innovative brands serving trend-conscious consumers." Instead:

```yaml
b2b_icp:
  company:
    industry: "Fashion e-commerce"
    platform: "Shopify"
    revenue: "$2M-$15M"

  end_user_base:
    age_range: "25-45"
    geography: "US urban"
    mobile_usage: ">60%"
    return_rate: "15%+" (indicates fit issues)
```

---

## Prospecting Tool Differences

### B2B Prospecting Tools

**Primary**:
- LinkedIn Sales Navigator (company + contact data)
- BuiltWith (technology stack)
- Crunchbase (funding, company data)
- Apollo/ZoomInfo (contact data)

**Example search**:
```
LinkedIn: Companies with 50-200 employees, Apparel industry, US
BuiltWith: Shopify stores in United States
Crunchbase: Series A funded, $5M-$30M total funding
```

### B2C Prospecting "Tools"

**Primary**:
- Facebook/Instagram Ads (demographic + interest targeting)
- Google Ads (intent-based targeting)
- Pinterest Ads (interest-based)
- Lookalike audiences (based on existing customers)

**Example targeting**:
```
Facebook Ads:
  - Age: 25-45
  - Gender: Female
  - Location: US
  - Interests: Fashion, Online Shopping, Sustainable Living
  - Behaviors: Engaged Shoppers
```

**Key difference**: B2B uses *research tools* to find companies. B2C uses *advertising platforms* to target consumers.

---

## Qualification Question Differences

### B2B Qualification

**Focus**: Company fit, organizational readiness, decision process

```
1. "What's your company size?"
2. "What platform are you on?"
3. "What's your return rate?" (problem severity)
4. "Who else would be involved in evaluating this?"
5. "Do you have budget allocated?"
```

### B2C Qualification

**Focus**: Individual fit, purchase intent, budget

```
1. "How often do you shop for [category]?"
2. "What's your biggest frustration with [problem area]?"
3. "What's your budget for [product]?"
4. "When are you looking to purchase?"
5. "Have you tried [competitor]?"
```

**Note**: B2C qualification often happens via quiz, survey, or website behavior (not phone calls)

### B2B2C Qualification (Hybrid)

**Ask the B2B customer about their B2C users**:

```
1. B2B firmographic: "What's your company size?"
2. B2B technographic: "What platform are you on?"
3. B2B problem: "What's your return rate?"
4. B2C demographics: "What's the age range of your typical customer?"
5. B2C behavior: "What percentage shop on mobile?"
6. B2C problem: "What do customers complain about most?"
```

---

## ICP Template Comparison

### B2B ICP Template

```yaml
product: [product-name]

b2b_icp:
  firmographics:
    company_size: "[range]"
    revenue: "[range]"
    geography: "[locations]"
    industry: "[NAICS or description]"

  technographics:
    required_platforms: ["platform1", "platform2"]
    tech_stack_signals: ["tool1", "tool2"]

  organizational:
    team_structure: "[key teams and sizes]"
    decision_makers: "[titles]"

  problem_signals:
    website: "[what to look for]"
    reviews: "[complaint patterns]"
    hiring: "[job postings]"

  disqualifiers:
    hard: ["dealbreaker1", "dealbreaker2"]
```

### B2C ICP Template

```yaml
product: [product-name]

b2c_icp:
  demographics:
    age_range: "[range]"
    gender: "[distribution]"
    geography: "[locations]"
    income: "[range]"

  behaviors:
    purchase_frequency: "[frequency]"
    channel_preference: "[online/offline/both]"
    device_usage: "[mobile/desktop split]"
    price_sensitivity: "[AOV range]"

  interests:
    categories: ["interest1", "interest2"]
    verification: "[how to observe these]"

  channels:
    social_media: ["platforms"]
    content: ["types and sources]"

  problem_signals:
    pain_points: "[observable behaviors]"
    workarounds: "[what they do now]"
```

### B2B2C Hybrid Template

```yaml
product: [product-name]

b2b_customer_icp:
  # [Use B2B template structure]

end_user_profile:
  # [Use B2C template structure]

alignment_criteria:
  - criterion: "[How B2C profile affects B2B fit]"
    example: "Brand's customers must be 70%+ mobile users"

  - criterion: "[Another alignment factor]"
    example: "Return rate correlates with end user demographics"
```

---

## Common Mistakes

### Mistake 1: Psychographics in B2C

❌ **Bad B2C ICP**:
```
Target: Fashion-forward women who value quality and are willing to invest in their wardrobe
```

✓ **Fixed B2C ICP**:
```
Demographics:
  - Age: 25-45
  - Gender: Female
  - Income: $75K+
  - Geography: US urban areas

Behaviors:
  - Purchases from premium brands (AOV $100+)
  - Shops online 3+ times per quarter
  - Engages with fashion content on Instagram

Verification:
  - Facebook Ads audience insights
  - Google Analytics demographics
  - Customer purchase history
```

### Mistake 2: Ignoring B2C When Selling B2B

❌ **Bad B2B ICP** (for product affecting end users):
```
Target: E-commerce companies with 50-200 employees
```

✓ **Fixed B2B ICP**:
```
B2B Customer:
  - Company size: 50-200 employees
  - Industry: Fashion e-commerce
  - Platform: Shopify

End User Profile (must match):
  - Age 25-45, female-skewed
  - Mobile shoppers (60%+)
  - High return rate (15%+) indicating fit issues
```

### Mistake 3: Different Observability Standards

❌ **Inconsistent**:
```
B2B ICP: "50-200 employees" (observable)
B2C ICP: "Values customer experience" (psychographic)
```

✓ **Consistent**:
```
B2B ICP: "50-200 employees" (observable)
B2C ICP: "NPS promoters (9-10 score)" (observable)
```

**Both must be equally observable**

---

## Quick Reference

| Aspect | B2B | B2C | B2B2C |
|--------|-----|-----|-------|
| **Primary Unit** | Company | Individual | Both |
| **Data Sources** | LinkedIn, Crunchbase, BuiltWith | Ad platforms, analytics, surveys | Both |
| **Key Characteristics** | Firmographics, technographics | Demographics, behaviors | Both |
| **Qualification Method** | Sales calls | Quizzes, forms, behavior | Sales calls (ask about end users) |
| **Psychographics Allowed?** | No (use proxies) | No (use proxies) | No |
| **Example Observable** | "Uses Shopify" | "Shops on mobile 60%+ of time" | Both |
| **Prospecting** | Research → outreach | Advertising → inbound | Both |

**Universal rule**: Observable characteristics ONLY, whether B2B or B2C.

---

## Example: GlamYouUp (Full Hybrid ICP)

### B2B ICP: Fashion E-commerce Brands

```yaml
firmographics:
  company_size: "20-150 employees"
  revenue: "$2M-$15M ARR"
  geography: "US, CA, UK"
  industry: "Fashion & Apparel E-commerce (NAICS 448, 454)"

technographics:
  required: "Shopify"
  signals: ["Klaviyo", "Stripe", "Yotpo"]

problem_signals:
  - "Return rate 15-40%"
  - "FAQ mentions sizing/fit"
  - "Job postings for returns/CS roles"

buyer_personas:
  economic: "VP Operations, COO"
  technical: "CTO, Engineering Lead"
  champion: "E-commerce Manager, Ops Manager"
```

### B2C Profile: Fashion Shoppers

```yaml
demographics:
  age: "25-45"
  gender: "Female (70%), Male (30%)"
  geography: "US urban, household income $75K+"

behaviors:
  - "Online fashion shoppers (not in-store)"
  - "Mobile usage 60%+"
  - "Return items 20-30% of time"
  - "Purchase frequency: 3-6x per year"

channels:
  - "Instagram active users"
  - "Pinterest (fashion boards)"
  - "Fashion blog readers"

problem_indicators:
  - "Reviews mention sizing issues"
  - "Searches for size guides before purchase"
  - "Engages with 'fit' content on social"
```

### Alignment Criteria

```yaml
b2c_fit_requirements:
  - criterion: "Brand's customer base is 60%+ female, age 25-45"
    qualification_question: "What's the demographic breakdown of your customers?"

  - criterion: "Mobile shoppers (60%+ mobile traffic)"
    qualification_question: "What percentage of your customers shop on mobile?"

  - criterion: "High return rate (indicates sizing issues in target demo)"
    qualification_question: "What's your return rate?"
```

**Result**: Only pursue fashion brands whose end customers match our B2C profile, because the product solves their specific problem.

---

**Key Takeaway**: Whether B2B, B2C, or hybrid, Pete Kazanjy's principle holds: **Observable characteristics only**. The types of data differ, but the rigor is the same.
