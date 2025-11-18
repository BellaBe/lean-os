# Problem Signal Patterns

## Purpose

Identify **observable evidence** that a company is experiencing the problem your product solves.

**Key principle**: Don't assume companies have the problem. Find proof.

## Core Signal Categories

### 1. Website Content Signals
### 2. Review & Complaint Signals
### 3. Job Posting Signals
### 4. Social Media Signals
### 5. Customer Behavior Signals
### 6. Operational Signals

---

## 1. Website Content Signals

**Where to look**: FAQ, About, Policy pages, Product pages, Blog, Help center

### Pattern A: Problem Mentioned Directly

**What to search for**:
- FAQ mentions the problem
- Help docs address the problem
- Policy page tries to mitigate the problem
- Blog posts discuss the problem

**Example (Fashion Returns Problem)**:

Search: `site:example.com "returns" OR "return policy"`

**Positive signals**:
```
✓ FAQ: "What's your return policy?"
✓ FAQ: "Why do items fit differently than expected?"
✓ Return policy: "We offer free returns for sizing issues"
✓ Product pages: "See our size guide" (prominent placement)
✓ Blog: "How to find your perfect fit"
```

**Strength indicators**:
- **Strong**: Problem mentioned multiple places (FAQ + policy + product pages)
- **Medium**: Problem mentioned on FAQ or policy page
- **Weak**: Generic mention without emphasis

**Google Search Syntax**:
```
site:shopifybrand.com ("return policy" OR "free returns" OR "sizing issues" OR "fit guide")
```

### Pattern B: Defensive/Proactive Content

**What to look for**:
- Overly detailed policies (suggests high incident rate)
- Pre-emptive warnings or disclaimers
- Extensive help content on the topic
- Comparison guides or educational content

**Example (E-commerce Returns)**:

**Positive signals**:
```
✓ Size chart on every product page (prominent)
✓ "This item runs small - size up!" warnings
✓ Return window >30 days (suggests they expect returns)
✓ "Free returns" prominently marketed (cost of doing business)
✓ Video guides on "How to measure yourself"
```

**Example (Customer Support Volume)**:

**Positive signals**:
```
✓ Extensive FAQ (50+ questions)
✓ "Before contacting us, check our FAQ" message
✓ Chatbot prominently featured
✓ Multiple support channels listed (email, chat, phone, social)
```

### Pattern C: Product/Feature to Address Problem

**What to look for**:
- Tools or features they've built to mitigate the problem
- Integrations they've added to solve the problem
- Workarounds they've documented

**Example (API Reliability Issues)**:

**Positive signals**:
```
✓ Status page prominently linked
✓ Webhook retry logic documented
✓ Rate limiting documentation extensive
✓ "Best practices for handling timeouts" guide
```

**Example (Inventory Management)**:

**Positive signals**:
```
✓ Real-time stock indicators on product pages
✓ "Back in stock" notifications
✓ "Only 3 left!" urgency messaging
✓ Pre-order functionality
```

---

## 2. Review & Complaint Signals

**Where to look**: Trustpilot, Google Reviews, Yelp, BBB, G2/Capterra (for B2B), App Store reviews

### Pattern A: Recurring Complaint Themes

**What to search for**: Keywords related to your problem in reviews

**Example (Fashion Sizing Issues)**:

Search on Trustpilot/Google Reviews:
- "too small"
- "too large"
- "fit"
- "size"
- "return"

**Positive signals**:
```
✓ 10+ reviews mentioning "sizing issues"
✓ 3-star reviews (not terrible, but frustrated with specific issue)
✓ Positive reviews that mention "great return policy" (implies returns are common)
```

**Strength indicators**:
- **Strong**: 20%+ of reviews mention the problem
- **Medium**: 10-20% mention the problem
- **Weak**: <10% mention the problem

### Pattern B: Company Response Patterns

**What to look for**: How the company responds to complaints

**Positive signals** (problem is significant):
```
✓ Company responds to sizing complaints with apologies + free return labels
✓ Company acknowledges "we're working on better size guides"
✓ Formulaic responses (suggests high volume, need for templates)
✓ Response times slow (>48 hours) suggests overwhelmed team
```

**Example**:
> Customer: "Item was too small, very disappointed."
> Company: "We're so sorry! We know sizing can be tricky. We've sent you a prepaid return label. Please check our updated size guide for your next order."

This response suggests:
1. Sizing is a known, recurring issue
2. They've invested in "updated size guide"
3. They offer free returns (cost they're willing to absorb)

### Pattern C: Star Rating Distribution

**What to analyze**: Distribution of ratings, not just average

**Positive signals** (problem is real but not fatal):
```
✓ Bimodal distribution (many 5-stars, many 1-stars) suggests specific issue affects some customers
✓ 3-star reviews specifically (not terrible product, but issue prevents 4-5 stars)
```

**Example**:
- 60% 5-star reviews: "Love the style!"
- 10% 4-star reviews
- 5% 3-star reviews: "Great product but sizing is off"
- 5% 2-star reviews
- 20% 1-star reviews: "Had to return, too small"

**Interpretation**: Product quality is good (high 5-star), but sizing issue creates 1-star returns.

---

## 3. Job Posting Signals

**Where to look**: LinkedIn Jobs, company careers page, Lever, Greenhouse, Indeed

### Pattern A: Problem-Specific Roles

**What to search for**: Job titles or descriptions that indicate the problem

**Example (High Return Volume)**:

Search LinkedIn: `"company name" AND ("returns coordinator" OR "returns specialist" OR "reverse logistics")`

**Positive signals**:
```
✓ "Returns Coordinator" role posted
✓ "Customer Service - Returns Specialist"
✓ "Reverse Logistics Manager"
✓ Job description mentions "high volume returns processing"
```

**Example (Customer Support Volume)**:

Search LinkedIn: `"company name" AND ("customer support" OR "customer service")`

**Positive signals**:
```
✓ 3+ customer support roles open simultaneously
✓ "Customer Support Representative (High Volume)"
✓ "Support Team Lead" (suggests growing team)
✓ Job description: "Handle 50+ tickets per day"
```

**Example (Security/Compliance Issues)**:

**Positive signals**:
```
✓ "Security Compliance Analyst" role
✓ "SOC 2 Program Manager"
✓ Job description: "Lead SOC 2 Type II certification"
✓ "Information Security Engineer" on small team (disproportionate focus)
```

### Pattern B: Job Description Keywords

**What to search for**: Specific phrases in JD that reveal the problem

**Example (Data Infrastructure Issues)**:

Job title: "Data Engineer"

**Positive signals in description**:
```
✓ "Migrate from legacy data warehouse"
✓ "Improve data pipeline reliability"
✓ "Reduce data processing time from hours to minutes"
✓ "Rebuild ETL infrastructure"
```

**Example (Sales Process Inefficiency)**:

Job title: "Sales Operations Manager"

**Positive signals in description**:
```
✓ "Streamline lead qualification process"
✓ "Reduce sales cycle time"
✓ "Implement sales automation"
✓ "Clean up CRM data and improve data hygiene"
```

### Pattern C: Hiring Volume for Problem Area

**What to measure**: Number of roles in problem-related department

**Positive signals**:
```
✓ 5+ customer support roles (suggests understaffed, high volume)
✓ 3+ ops roles (suggests operational challenges)
✓ 2+ compliance roles at <100 person company (disproportionate)
```

---

## 4. Social Media Signals

**Where to look**: Twitter, LinkedIn, Facebook, Instagram, Reddit

### Pattern A: Direct Customer Complaints

**What to search for**: Public mentions of the problem

**Example (Fashion Sizing)**:

Twitter search: `@brandname (sizing OR fit OR "too small" OR "too large")`

**Positive signals**:
```
✓ 5+ tweets per month mentioning sizing issues
✓ Brand responds to sizing complaints (acknowledges problem)
✓ Customers posting photos of ill-fitting items
```

### Pattern B: Brand Communication Patterns

**What to look for**: How often brand discusses the problem

**Example (Sustainability Concerns)**:

**Positive signals**:
```
✓ Brand posts about sustainability initiatives frequently
✓ Responds to sustainability questions from customers
✓ Announces "carbon-neutral shipping" (proactive problem-solving)
```

**Interpretation**: If they're marketing solutions, they're aware customers care about the problem.

### Pattern C: Community Discussions

**What to search for**: Reddit, Facebook groups, forums discussing the brand

**Example (SaaS Integration Issues)**:

Reddit search: `"ProductName" AND (integration OR API OR "doesn't work with")`

**Positive signals**:
```
✓ Reddit threads: "How to integrate ProductName with X?"
✓ Community-built workarounds shared
✓ Users asking "Does ProductName work with Y yet?"
```

---

## 5. Customer Behavior Signals

**Where to look**: Website behavior (if you can observe), App Store reviews, user-generated content

### Pattern A: Workaround Adoption

**What to look for**: Evidence customers are building their own solutions

**Example (Limited Reporting in SaaS Product)**:

**Positive signals**:
```
✓ Google Sheets templates shared for "exporting ProductName data"
✓ Zapier integrations to export data to BI tools
✓ Blog posts: "How I analyze my ProductName data in Excel"
```

**Example (E-commerce Sizing)**:

**Positive signals**:
```
✓ Customers posting fit photos on Instagram (#brandnamefit)
✓ "Size up!" comments on brand's social posts
✓ Third-party size guide websites/apps that include the brand
```

### Pattern B: App Store Review Patterns

**What to search for**: Feature requests in reviews

**Example (Mobile App Missing Features)**:

**Positive signals**:
```
✓ Reviews saying "Would be 5 stars if it had [feature]"
✓ Common feature requests (20+ reviews asking for same feature)
✓ "I have to use desktop for [task] because app can't do it"
```

### Pattern C: Usage Pattern Indicators

**What to infer from observable behavior**:

**Example (High Churn SaaS)**:

**Positive signals** (if you can observe):
```
✓ Trial-to-paid conversion <10% (suggests onboarding issues)
✓ Free tier has 10x users of paid tier (suggests hesitation to commit)
✓ High support ticket volume in first 30 days (suggests confusion)
```

---

## 6. Operational Signals

**Where to look**: News, press releases, company blog, LinkedIn updates

### Pattern A: Announced Initiatives

**What to search for**: Company announces projects to address the problem

**Example (Supply Chain Issues)**:

**Positive signals**:
```
✓ Press release: "Opening new fulfillment center"
✓ Blog: "How we're improving delivery times"
✓ LinkedIn: Hiring "Supply Chain Manager"
✓ News: "Brand partners with 3PL to reduce shipping delays"
```

### Pattern B: Executive Changes

**What to look for**: New hires or role changes focused on problem area

**Example (Customer Retention Issues)**:

**Positive signals**:
```
✓ New VP of Customer Success hired
✓ Promoted "Director of Retention"
✓ Press release emphasizes new exec's "retention expertise"
```

### Pattern C: Partnership Announcements

**What to look for**: Integrations or partnerships to solve the problem

**Example (Payment Processing Issues)**:

**Positive signals**:
```
✓ Announces "New partnership with Stripe"
✓ Blog: "We've upgraded our payment infrastructure"
✓ "Now accepting Apple Pay" (suggests modernizing payments)
```

---

## Problem Signal Scoring

Create a scoring rubric for each prospect:

### Signal Strength Tiers

**Tier 1: Strong Signal (4-5 points)**
- Problem mentioned on website (FAQ, policy, product pages)
- 10+ reviews mentioning the problem
- Job posting specifically for problem area
- Company announced initiative to address problem

**Tier 2: Medium Signal (2-3 points)**
- Problem mentioned in reviews (5-10 mentions)
- Generic role that might be related (e.g., "Customer Support" for volume issues)
- Social media complaints (3-5 per month)

**Tier 3: Weak Signal (1 point)**
- Problem mentioned once or twice in reviews
- Inferred from industry patterns (not specific to company)

### Minimum Threshold for Qualification

**Recommended**: 6+ points across multiple signal types

**Example Scoring** (Fashion Returns Problem):

Prospect: "ChicThreads"
- FAQ mentions sizing issues (4 points)
- 15 Trustpilot reviews mention "fit" or "size" (4 points)
- Hiring for "Returns Coordinator" (5 points)
- Generous return policy (60 days) (3 points)

**Total**: 16 points → **STRONG FIT**

Prospect: "TrendyStyles"
- Return policy exists but generic (1 point)
- 3 reviews mention sizing (2 points)
- No job postings related to returns (0 points)

**Total**: 3 points → **WEAK FIT** (deprioritize)

---

## Automating Problem Signal Detection

### Google Search Operators

**Search for website mentions**:
```
site:example.com ("problem keyword" OR "related term" OR "pain point phrase")
```

**Search for reviews**:
```
site:trustpilot.com OR site:reviews.io "brand name" ("problem keyword")
```

**Search for job postings**:
```
site:lever.co OR site:greenhouse.io "company name" ("problem role" OR "related role")
```

### Spreadsheet Workflow

Create a prospect tracker:

| Company | Website Signal | Review Signal | Job Signal | Social Signal | Total Score | Priority |
|---------|---------------|---------------|------------|---------------|-------------|----------|
| Brand A | 4 (FAQ)       | 4 (12 reviews)| 5 (hiring) | 2 (tweets)    | 15          | High     |
| Brand B | 0             | 2 (3 reviews) | 0          | 1             | 3           | Low      |

### Tool-Assisted Detection

**SimilarWeb**: Check traffic patterns
- Bounce rate >60% might indicate UX issues
- Low pages/visit might indicate navigation problems

**Mention.com / Brand24**: Monitor social mentions
- Set alerts for "[brand] + [problem keyword]"
- Track frequency of problem mentions

---

## Problem Signal Examples by Industry

### E-commerce (Returns/Sizing)
```yaml
website_signals:
  - "FAQ mentions sizing, fit, or returns"
  - "Size guide on product pages"
  - "Free returns policy prominently displayed"

review_signals:
  - "Reviews mentioning 'too small', 'too large', 'fit issues'"
  - "Return-related complaints >10% of reviews"

job_signals:
  - "Returns Coordinator role posted"
  - "Customer Service (Returns focus) role"

social_signals:
  - "Twitter complaints about sizing"
  - "Instagram comments asking about fit"
```

### B2B SaaS (Integration/API Issues)
```yaml
website_signals:
  - "API documentation extensive (suggests complexity)"
  - "Integration page lists workarounds"
  - "Webhooks, rate limits heavily documented"

review_signals:
  - "G2 reviews mentioning integration challenges"
  - "Requests for specific integrations in reviews"

job_signals:
  - "Integrations Engineer role posted"
  - "API Support Engineer role"

community_signals:
  - "Reddit threads about integration difficulties"
  - "Third-party integration tools/services"
```

### SaaS (Onboarding/Adoption Issues)
```yaml
website_signals:
  - "Extensive onboarding documentation"
  - "Video tutorials prominently featured"
  - "Free training or certification programs"

review_signals:
  - "Reviews: 'Steep learning curve'"
  - "Requests for better onboarding in reviews"

job_signals:
  - "Customer Onboarding Specialist role"
  - "Implementation Consultant role"

support_signals:
  - "High volume of 'getting started' help articles"
  - "Live onboarding webinars offered"
```

### Professional Services (Hiring/Retention)
```yaml
website_signals:
  - "10+ open roles on careers page"
  - "Careers page emphasizes 'great culture'"
  - "Employee testimonials featured"

review_signals:
  - "Glassdoor reviews mention turnover"
  - "Indeed reviews: 'Great but understaffed'"

job_signals:
  - "Recruiter or Talent Acquisition roles posted"
  - "People Ops or Culture roles posted"

social_signals:
  - "LinkedIn posts about hiring initiatives"
  - "Founder posts about 'building the team'"
```

---

## Quality Checklist

Before using problem signals in ICP, verify:

- [ ] Signals are observable (not inferred or assumed)
- [ ] You've checked multiple signal sources (not just one)
- [ ] Signals are current (within last 6-12 months)
- [ ] You can replicate the search (documented search queries)
- [ ] Signals correlate with actual customer data (if available)
- [ ] Scoring rubric is consistent across prospects

**Remember**: Problem signals help prioritize prospects, but always validate on the qualification call.
