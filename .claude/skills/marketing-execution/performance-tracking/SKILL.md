---
name: performance-tracking
description: Monitor published content performance across channels. Tracks traffic, engagement, conversions, and SEO rankings. Identifies top performers, flags underperformers, and feeds insights back to content strategy for continuous improvement.
allowed-tools: "Read,Write,Bash"
---

# Performance Tracking

You measure content impact and feed insights back to strategy.

## Purpose

Published content → Performance data → Strategic insights → Improved strategy

**Core principle:** Track what matters (pipeline impact), not vanity metrics (likes).

---

## Input Requirements

### Required Inputs

**1. Distribution records:**
```
distribution-record-{date}-{slug}.yaml
```

**2. Analytics access (when available):**
- Google Analytics (traffic, conversions)
- LinkedIn Analytics (engagement)
- Email platform (open/click rates)
- Search Console (rankings, impressions)

**3. Business goals (from Canvas):**
```
strategy/canvas/13-metrics.md
```

---

## Tracking Periods

### Standard Tracking Windows

**Immediate (Days 1-7):**
- Blog traffic spike
- LinkedIn engagement peak
- Email open/click rates
- Initial SEO indexing

**Short-term (Days 8-30):**
- Organic traffic growth
- SEO ranking improvements
- Conversion rate stabilization
- Social sharing patterns

**Long-term (Days 31-90):**
- SEO ranking position
- Cumulative conversions
- Content authority (backlinks)
- Compounding traffic

**Evergreen (90+ days):**
- Sustained organic traffic
- Long-tail keyword rankings
- Total conversions (lifetime)
- ROI calculation

---

## Metrics by Channel

### Blog Metrics

**Traffic metrics:**
- Sessions: Total visits to article
- Unique visitors: Individual people
- Page views: Total views (includes repeat)
- Traffic sources: Organic, social, email, direct, referral

**Engagement metrics:**
- Average time on page: How long readers stay
- Scroll depth: Percentage of article read
- Bounce rate: Single-page sessions
- Pages per session: Navigation to other pages

**Conversion metrics:**
- Demo requests: From article (tracked via UTM)
- Newsletter signups: In-article CTA
- Downloads: Lead magnets, resources
- Product page visits: Navigation to /pricing, /demo

**SEO metrics:**
- Ranking position: For target keyword
- Impressions: Times shown in SERP
- Click-through rate: Clicks / impressions
- Ranking keywords: All keywords ranking
- Backlinks: External sites linking

**Business impact:**
- Pipeline influenced: Deals where article was touchpoint
- Revenue influenced: ARR from influenced pipeline
- Cost per acquisition: Content cost / conversions

---

### LinkedIn Metrics

**Reach metrics:**
- Impressions: Times post shown in feed
- Unique impressions: Individual viewers
- Follower reach: % of followers who saw it
- Virality: Reach beyond immediate followers

**Engagement metrics:**
- Likes/reactions: Total engagement actions
- Comments: Discussion generated
- Shares/reposts: Content amplification
- Click-through rate: Link clicks / impressions

**Audience metrics:**
- Top demographics: Who engaged most
- Job titles: Decision-maker engagement
- Companies: Target accounts engaging
- Seniority: IC vs manager vs executive

**Conversion metrics:**
- Website visits: Traffic from LinkedIn
- Profile visits: Company page views
- Follow increase: New followers
- Lead generation: Demo requests from LinkedIn traffic

---

### Email Metrics

**Delivery metrics:**
- Sent: Total emails sent
- Delivered: Successfully delivered
- Bounced: Failed delivery (hard + soft)
- Spam complaints: Marked as spam

**Engagement metrics:**
- Open rate: Opens / delivered
- Click rate: Clicks / delivered
- Click-to-open rate: Clicks / opens
- Time to open: How quickly opened

**Conversion metrics:**
- Demo requests: From email CTA
- Content downloads: Resources clicked
- Website visits: Traffic to blog/product pages
- Unsubscribes: Opt-outs

**Segmentation insights:**
- Open rate by segment: Which segments engage
- Click rate by segment: Which segments convert
- Best performing subject lines: A/B test winners
- Best send times: Day/time optimization

---

### Website Metrics

**Page performance:**
- Page views: Total views
- Unique page views: Individual visitors
- Average time on page: Engagement duration
- Exit rate: % who leave from this page

**Conversion metrics:**
- Demo requests: From page CTA
- Form submissions: Contact, newsletter
- Product page visits: Navigation to /pricing
- Trial signups: Direct conversions

**SEO metrics:**
- Organic traffic: Search engine visits
- Ranking keywords: All ranking terms
- Page authority: Domain authority score
- Backlinks: External links to page

---

## Data Collection Process

### Step 1: Load Distribution Record

**Read tracking file:**
```yaml
content_slug: "elsaai-white-label-sdk-case-study"
publish_date: "2024-11-16"
channels:
  - blog: {url, utm}
  - linkedin: {url, utm}
  - email: {url, utm}
```

### Step 2: Collect Channel Data

**For each channel, collect metrics:**

**Blog (if analytics available):**
```bash
# Pseudo-code for analytics query
GET /analytics/pageviews
  ?url=/blog/elsaai-white-label-sdk-case-study
  &start_date=2024-11-16
  &end_date=2024-11-23
  
Response:
  sessions: 650
  unique_visitors: 580
  avg_time_on_page: "4:32"
  bounce_rate: 42%
  conversions: 8 (demo requests)
```

**LinkedIn (if API available):**
```bash
GET /linkedin/post-analytics
  ?post_id={linkedin_post_id}
  
Response:
  impressions: 12500
  clicks: 380
  likes: 145
  comments: 23
  shares: 18
```

**Email (if ESP API available):**
```bash
GET /email/campaign-stats
  ?campaign_id={campaign_id}
  
Response:
  sent: 1250
  opened: 312 (24.96%)
  clicked: 78 (6.24%)
  bounced: 8 (0.64%)
  unsubscribed: 2 (0.16%)
```

**If APIs unavailable:**
- Manual data entry (from analytics dashboards)
- Flag: "Manual tracking required"
- Update performance record manually

### Step 3: Calculate Derived Metrics

**From raw data, calculate:**

**Engagement score:**
```
Engagement = (Time on page × 0.4) + (Scroll depth × 0.3) + (Pages per session × 0.3)

Example:
Time on page: 4:32 (272 seconds) → Normalized: 0.9 (if target is 300s)
Scroll depth: 78% → Normalized: 0.78
Pages per session: 2.1 → Normalized: 0.7 (if target is 3)

Engagement score = (0.9 × 0.4) + (0.78 × 0.3) + (0.7 × 0.3) = 0.804 (80.4%)
```

**Content quality score:**
```
Quality = (Avg time on page / Target) × (Scroll depth / 100) × (1 - Bounce rate)

Example:
Avg time: 272s / 300s = 0.91
Scroll depth: 78% = 0.78
Bounce rate: 42% = 0.58 (1 - 0.42)

Quality score = 0.91 × 0.78 × 0.58 = 0.411 (41.1%)
```

**Conversion rate:**
```
Conversion rate = Conversions / Sessions

Example:
Conversions: 8 (demo requests)
Sessions: 650

Conversion rate = 8 / 650 = 0.0123 (1.23%)
```

**ROI estimate:**
```
Content cost: $X (human time + AI cost)
Pipeline influenced: $Y (deals where article was touchpoint)
ROI = (Pipeline influenced - Cost) / Cost

Example:
Cost: $500 (10 hours @ $50/hr)
Pipeline influenced: $50K (2 deals, $25K avg)
ROI = ($50,000 - $500) / $500 = 99x (9,900%)
```

### Step 4: Identify Patterns

**Top performers (outliers):**
- Sessions >2x average
- Conversion rate >2x average
- Engagement score >0.8

**Underperformers (attention needed):**
- Sessions <50% of average
- Conversion rate <50% of average
- Engagement score <0.4

**Anomalies:**
- High traffic, low conversions (targeting issue?)
- Low traffic, high conversions (hidden gem?)
- High bounce rate (content mismatch?)

---

## Performance Report Format

### Weekly Performance Summary
```markdown
# Content Performance Report - Week of {date}

Generated: {date}
Period: {start_date} to {end_date}

## Overview

**Content published this week:** 2
- ElsaAI White-Label Case Study (blog, LinkedIn, email)
- Fashion Return Reduction Guide (blog, LinkedIn)

**Total traffic:** 1,850 sessions (+32% vs last week)
**Total conversions:** 18 demos requested
**Top performer:** ElsaAI case study (650 sessions, 8 demos)

---

## Top Performers

### 1. ElsaAI White-Label SDK Case Study

**Published:** 2024-11-16
**Channels:** Blog, LinkedIn, Email
**Performance (Days 1-7):**

**Blog:**
- Sessions: 650
- Avg time on page: 4:32 (target: 3:00) ✓
- Scroll depth: 78% (target: 75%) ✓
- Conversions: 8 demos (1.23% rate)
- Traffic sources:
  - Organic: 45% (294 sessions)
  - LinkedIn: 30% (195 sessions)
  - Email: 20% (130 sessions)
  - Direct: 5% (31 sessions)

**LinkedIn:**
- Impressions: 12,500
- Clicks: 380 (3.04% CTR)
- Engagement: 186 (1.49% rate)
  - Likes: 145
  - Comments: 23
  - Shares: 18

**Email:**
- Sent: 1,250 (enterprise segment)
- Opened: 312 (24.96% rate) ✓
- Clicked: 78 (6.24% rate) ✓
- Conversions: 3 demos (3.85% of clicks)

**SEO (Days 1-7):**
- Indexed: ✓ (Day 2)
- Ranking: Position 24 for "white-label SDK" (target: <20)
- Impressions: 145
- Clicks: 12 (8.28% CTR)

**Business impact:**
- Demos requested: 8
- Qualified leads: 6 (75% qualification rate)
- Pipeline influenced: $50K (2 deals mention article)

**Why it performed:**
- Strong customer proof (specific metrics)
- High-intent keyword (white-label SDK)
- Multi-channel amplification
- Email segment highly relevant

**Next steps:**
- Create follow-up content (white-label implementation guide)
- Monitor SEO ranking improvement (target: top 10)
- Use as sales enablement (share with prospects)

---

### 2. Fashion Return Reduction Guide

**Published:** 2024-11-14
**Performance (Days 1-9):**

{Similar detailed breakdown}

---

## Underperformers

### API Rate Limiting Technical Post

**Published:** 2024-11-10
**Performance (Days 1-13):**

**Blog:**
- Sessions: 42 (expected: 200+)
- Avg time: 2:15 (low engagement)
- Conversions: 0

**Why it underperformed:**
- Niche technical topic (low search volume)
- No pillar alignment (orphan content)
- Minimal LinkedIn promotion

**Action:**
- Reassess: Is this marketing content or technical docs?
- Consider: Move to developer docs, not blog
- Skip: Future similar topics unless strategic

---

## Trends & Insights

**Content themes that perform:**
1. **Case studies with metrics:** 2x traffic vs averages
2. **Implementation guides:** High engagement (avg 5:12 on page)
3. **Industry analysis:** Strong LinkedIn performance

**Content themes that underperform:**
1. **Pure technical posts:** Low traffic, narrow audience
2. **Generic how-tos:** High competition, low ranking

**Channel insights:**
- **Blog:** Organic traffic growing (+15% month-over-month)
- **LinkedIn:** Case studies outperform thought leadership
- **Email:** Enterprise segment converts 3x better than SMB

**Keyword insights:**
- **High-value keywords:** "white-label SDK" (low volume, high intent)
- **Opportunity keywords:** "reduce fashion returns" (high volume, ranking #24)

---

## Recommendations

### Content Strategy Updates

1. **Double down on case studies**
   - Highest conversion rate (1.2% vs 0.4% avg)
   - Strong LinkedIn engagement
   - Sales team requests more

2. **Deprioritize technical deep-dives**
   - Unless explicitly requested by sales
   - Or move to developer documentation

3. **Optimize underperforming content**
   - "Fashion Return Reduction Guide" ranking #24 → Update for top 10
   - Add internal links from high-performers

### SEO Priorities

1. **Target keyword:** "reduce fashion returns"
   - Current: Position 24
   - Opportunity: Position 8-12 achievable
   - Action: Update content, build internal links

2. **Monitor:** "white-label SDK"
   - Current: Position 24 (just indexed)
   - Track: Expect climb to top 10 in 30 days

### Channel Optimization

1. **LinkedIn:** Focus on case studies and customer results
2. **Email:** Segment further (luxury vs fast fashion)
3. **Blog:** Continue SEO-focused education

---

## Metrics Summary

| Metric | This Week | Last Week | Change |
|--------|-----------|-----------|--------|
| **Traffic** | 1,850 | 1,400 | +32% |
| **Conversions** | 18 | 12 | +50% |
| **Avg time on page** | 3:45 | 3:20 | +12% |
| **Conversion rate** | 0.97% | 0.86% | +13% |
| **LinkedIn CTR** | 3.04% | 2.15% | +41% |
| **Email open rate** | 24.96% | 22.10% | +13% |

---

## Next Week Priorities

1. Monitor ElsaAI case study SEO ranking (target: top 20)
2. Create follow-up content (white-label implementation guide)
3. Optimize "Fashion Return Reduction Guide" for better ranking
4. Review underperforming technical content strategy
```

---

### Monthly Performance Dashboard
```yaml
# monthly-performance-2024-11.yaml

month: "November 2024"
period: "2024-11-01 to 2024-11-30"

summary:
  content_published: 8
  total_sessions: 12,450
  total_conversions: 78
  avg_conversion_rate: 0.63%
  pipeline_influenced: $425K

top_performers:
  - slug: "elsaai-white-label-sdk-case-study"
    sessions: 2,340
    conversions: 28
    conversion_rate: 1.20%
    pipeline: $150K
    
  - slug: "reduce-fashion-returns-guide"
    sessions: 1,890
    conversions: 18
    conversion_rate: 0.95%
    pipeline: $75K

underperformers:
  - slug: "api-rate-limiting-technical"
    sessions: 42
    conversions: 0
    issue: "Niche topic, no pillar alignment"
    
  - slug: "fashion-trends-q4"
    sessions: 156
    conversions: 1
    issue: "Too generic, high competition"

channel_performance:
  blog:
    sessions: 8,950
    conversions: 52
    top_source: "organic" (4,920 sessions, 55%)
    
  linkedin:
    impressions: 85,400
    clicks: 2,280
    ctr: 2.67%
    conversions: 18
    
  email:
    sent: 12,500
    opened: 3,125 (25%)
    clicked: 750 (6%)
    conversions: 8

seo_progress:
  keywords_ranking:
    top_10: 3 (+1 vs Oct)
    top_20: 8 (+3 vs Oct)
    top_50: 24 (+8 vs Oct)
  
  top_ranking_keywords:
    - keyword: "white-label SDK"
      position: 12 (was: not ranking)
      
    - keyword: "reduce fashion returns"
      position: 18 (was: 24)
      
    - keyword: "luxury fashion returns"
      position: 8 (was: 15)

insights:
  - "Case studies convert 2x better than guides"
  - "LinkedIn drives highest-quality traffic (1.2% vs 0.6% blog avg)"
  - "Enterprise email segment converts 4x better than general"
  - "Keyword 'luxury fashion returns' reached top 10 (strong opportunity)"

recommendations:
  - priority: "high"
    action: "Create 2 more case studies (based on recent deals)"
    rationale: "Highest conversion rate, sales team loves them"
    
  - priority: "medium"
    action: "Optimize 3 underperforming articles for better SEO"
    rationale: "Quick wins, ranking positions 15-25"
    
  - priority: "low"
    action: "Retire technical posts or move to dev docs"
    rationale: "Not serving marketing goals"
```

---

## Alerts & Notifications

### Auto-Flag in ops/today.md

**Top performer alert:**
```markdown
## Content Alerts

🎉 **Top Performer (Last 7 Days)**
- ElsaAI White-Label Case Study: 650 sessions, 8 demos (1.23% rate)
- Action: Create follow-up content, use in sales enablement
```

**Underperformer alert:**
```markdown
⚠️ **Underperformer (Last 30 Days)**
- API Rate Limiting Post: 42 sessions, 0 demos
- Issue: Niche topic, no pillar alignment
- Action: Reassess content strategy for technical posts
```

**SEO milestone alert:**
```markdown
📈 **SEO Milestone**
- "luxury fashion returns" reached position 8 (top 10!)
- Traffic potential: +500 sessions/month
- Action: Monitor ranking, create related content
```

**Conversion anomaly:**
```markdown
🔍 **Conversion Anomaly**
- Fashion Trends Q4: 156 sessions, 1 demo (0.64% rate)
- Expected: 1.5-2 demos based on traffic
- Possible issue: Traffic quality (wrong audience?)
- Action: Review traffic sources, adjust targeting
```

---

## Feedback Loop to Strategy

### Update content-strategy Based on Performance

**After 30 days of tracking:**

1. **Identify top-performing pillars:**
```
Pillar: "Product capabilities" (case studies)
- Avg sessions: 1,850
- Avg conversions: 18
- Conversion rate: 0.97%

→ Recommendation: Increase pillar allocation (20% → 30%)
```

2. **Identify underperforming pillars:**
```
Pillar: "Technical implementation" (deep-dives)
- Avg sessions: 98
- Avg conversions: 0.2
- Conversion rate: 0.20%

→ Recommendation: Reduce or retire pillar (20% → 5%)
```

3. **Update SEO strategy:**
```
Keyword: "luxury fashion returns"
- Position: 8 (top 10)
- Traffic: 450 sessions/month
- Conversions: 9 demos

→ Recommendation: Create cluster content around this keyword
```

4. **Adjust channel mix:**
```
Channel: LinkedIn
- Traffic quality: High (1.2% conversion)
- Effort: Medium

→ Recommendation: Increase LinkedIn content (1x/week → 2x/week)
```

---

## Success Metrics

**Tracking completeness:**
- Content tracked: 100% (all published content)
- Data accuracy: >95% (vs manual verification)
- Reporting timeliness: Weekly (within 24 hours)

**Performance insights:**
- Top performers identified: >80% accuracy
- Underperformers flagged: 100% (none missed)
- Recommendations actionable: >90%

**Business impact:**
- Pipeline influenced tracked: >90% attribution
- ROI calculated: For all content
- Strategy updates: Quarterly based on performance

---

## Usage Example

**Scenario:** ElsaAI case study published (Day 7 performance review)
```
1. Load distribution record:
   - content_slug: "elsaai-white-label-sdk-case-study"
   - publish_date: "2024-11-16"
   - channels: [blog, linkedin, email]

2. Collect blog data:
   - Sessions: 650
   - Avg time: 4:32
   - Conversions: 8

3. Collect LinkedIn data:
   - Impressions: 12,500
   - Clicks: 380
   - Engagement: 186

4. Collect email data:
   - Opened: 312 (24.96%)
   - Clicked: 78 (6.24%)
   - Conversions: 3

5. Calculate derived metrics:
   - Overall conversion rate: 1.23% (8 / 650)
   - LinkedIn CTR: 3.04% (380 / 12,500)
   - Email CTR: 6.24% (78 / 1,250)

6. Compare to benchmarks:
   - Conversion rate: 1.23% vs 0.60% avg = 2x ✓
   - LinkedIn CTR: 3.04% vs 2.0% avg = 1.5x ✓
   - Email open: 24.96% vs 22% avg = 1.13x ✓

7. Flag as top performer:
   - Add to ops/today.md: "Top performer alert"
   - Recommendation: Create follow-up content

8. Update performance record:
   - Save: performance-2024-11-16-elsaai-white-label.yaml
   - Include all metrics + insights

9. Feed back to strategy:
   - Insight: Case studies convert 2x better
   - Action: Prioritize case study content in next sprint
```

---

## Remember

**Performance tracking is:**
- Measuring what matters (pipeline impact, not vanity metrics)
- Identifying patterns (top performers, underperformers)
- Feeding insights back to strategy (continuous improvement)
- Proving ROI (content cost vs pipeline influenced)

**Performance tracking is NOT:**
- Obsessing over likes and shares
- Tracking without action
- Vanity metrics without business impact
- Reporting without recommendations

**Success = Data-driven content strategy that compounds over time.**