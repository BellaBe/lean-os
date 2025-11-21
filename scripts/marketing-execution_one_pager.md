================================================================================
Markdown Tree for: /home/bellabe/personal-os/.claude/skills/marketing-execution
================================================================================
marketing-execution/
├── content-distribution/
│   └── SKILL.md
├── content-generation/
│   ├── references/
│   │   ├── linkedin-post-pattern.md
│   │   ├── substack-article-pattern.md
│   │   └── twitter-thread-pattern.md
│   └── SKILL.md
├── content-strategy/
│   ├── references/
│   │   └── campaign-framework.md
│   └── SKILL.md
├── performance-tracking/
│   └── SKILL.md
├── seo-optimization/
│   └── SKILL.md
└── SKILL.md

================================================================================
Concatenated Markdown From: /home/bellabe/personal-os/.claude/skills/marketing-execution
Total files: 10
================================================================================


<!-- FILE: SKILL.md -->

# SKILL.md

```markdown
---
name: marketing-execution
description: Orchestrates marketing campaigns following 6-stage causal-flow. Coordinates content-strategy (opportunity identification), content-generation (draft creation), seo-optimization (keyword application), content-distribution (publishing), and performance-tracking (metrics analysis) subskills to execute campaign decisions.
allowed-tools: "Read,Write,Bash"
---

# Marketing Execution Orchestrator

You orchestrate marketing campaigns from planning through measurement using causal-flow methodology.

## Purpose

Execute marketing campaigns as decision threads, coordinating subskills to produce, publish, and measure content.

**Core principle:** Campaigns are threads following 6-stage causal-flow. All content is part of a campaign.

---

## Available Subskills

**Strategy:**
- `marketing-execution/content-strategy` - Identify content opportunities from threads

**Execution:**
- `marketing-execution/content-generation` - Generate content drafts
- `marketing-execution/seo-optimization` - Apply SEO to content
- `marketing-execution/content-distribution` - Publish to channels
- `marketing-execution/performance-tracking` - Measure impact

---

## Campaign Structure

**All marketing content is part of a campaign thread:**

```
threads/marketing/campaigns/{campaign-slug}/
├── metadata.yaml
├── 1-input.md        # Trigger (sales learning, market event, strategic decision)
├── 2-hypothesis.md   # What we believe (links to Canvas)
├── 3-implication.md  # Business impact (sessions, demos, revenue)
├── 4-decision.md     # Content plan (what to produce)
├── 5-actions/
│   └── execution-log.md  # Track content creation/publishing
└── 6-learning.md     # Measured results, Canvas updates
```

**Published content location:**

```
artifacts/marketing/campaigns/{campaign-slug}/
├── blog/
├── linkedin/
├── email/
└── distribution-record.yaml
```

---

## Campaign Workflow (6-Stage Causal-Flow)

### Stage 1-4: Planning (Human-Driven)

**Trigger:** Business event creates campaign opportunity
- Sales segment ready for awareness
- Product launch needs announcement
- Market trend warrants thought leadership

**Process:**
1. Create campaign thread: `threads/marketing/campaigns/{slug}/`
2. Stage 1 (Input): Document trigger
3. Stage 2 (Hypothesis): Link to Canvas assumption
4. Stage 3 (Implication): Calculate impact (sessions → demos → revenue)
5. Stage 4 (Decision): Define content to produce
   - List specific articles, posts, emails
   - Channels, keywords, timeline
   - Impact score, alternatives considered

### Stage 5: Execution (AI-Assisted)

**Orchestrator coordinates subskills to execute Stage 4 decision:**

```
For each content piece in Stage 4:
    ↓
1. content-generation (draft)
    ↓
2. Human review (accuracy, voice)
    ↓
3. seo-optimization (keywords, structure)
    ↓
4. Human approve
    ↓
5. content-distribution (publish to channels)
    ↓
6. Update execution-log.md (track progress)
```

**execution-log.md tracks:**
- [x] Article 1: Draft → Review → Optimize → Publish → URL
- [ ] Article 2: In progress
- [ ] LinkedIn post 1: Pending

### Stage 6: Learning (Automated + Human Analysis)

**performance-tracking monitors:**
- Traffic per content piece
- Conversions (demos, signups)
- Top/underperformers

**Human writes learning:**
- What worked, what didn't
- Canvas updates (validate/invalidate hypothesis)
- Next campaign opportunities

---

## Orchestration Modes

### Mode 1: Execute Campaign (Stage 5 Execution)

**Trigger:** Campaign thread reaches Stage 5, decision approved

**Input:**
```
Campaign: threads/marketing/campaigns/dtc-awareness-nov-2024/
Stage: Execute Stage 4 decision
```

**Process:**
1. Read Stage 4 decision (content plan)
2. For each content piece:
   - Invoke content-generation (create draft)
   - Save to campaign thread temp location
   - Flag for human review
   - After approval: Invoke seo-optimization
   - After approval: Invoke content-distribution
   - Publish to: artifacts/marketing/campaigns/{slug}/
   - Update execution-log.md
3. Report progress in ops/today.md

**Example execution-log.md:**
```markdown
# Execution Log - DTC Awareness Campaign

## Article 1: "Why 30% of Returns Are Fit-Related"
- [x] Draft created: 2024-11-16
- [x] Human review: Approved with minor edits
- [x] SEO optimized: Keyword "fashion return rate"
- [x] Published: artifacts/marketing/campaigns/dtc-awareness-nov-2024/blog/
- [x] URL: glamyouup.com/blog/fit-statistics (UTM tracked)

## LinkedIn Post 1: Fit Statistics Thread
- [x] Draft created: 2024-11-17
- [x] Published: artifacts/marketing/campaigns/dtc-awareness-nov-2024/linkedin/
- [ ] Scheduled: 2024-11-18 10am

## Article 2: "Body Shape vs Measurements"
- [x] Draft created: 2024-11-18
- [ ] Human review: Pending
```

### Mode 2: Campaign Opportunity Detection (Automated)

**Trigger:** Daily scan of business/sales threads

**Process:**
1. Invoke content-strategy subskill
2. Scan threads/{business,sales}/**/6-learning.md
3. Match learning to content pillars
4. Flag campaign opportunities in ops/today.md:
   ```markdown
   ## Campaign Opportunities

   1. [Priority: 0.85] DTC Product Awareness Campaign
      - Trigger: DTC segment ready, 191 prospects identified
      - Content: 3 articles on fit problems (educational)
      - Goal: 20 demos from organic traffic
      - Action: Create campaign thread?
   ```
5. Human decides: Create campaign or defer

### Mode 3: Campaign Performance Tracking (Stage 6 Support)

**Trigger:** Campaign content published, tracking period active

**Process:**
1. Invoke performance-tracking subskill
2. Monitor campaign metrics:
   - Traffic per content piece
   - Demo conversions
   - Top/underperformers
3. Report weekly in ops/today.md:
   ```markdown
   ## Active Campaign Performance

   **DTC Awareness (Week 2):**
   - Sessions: 1,200 / 2,000 target (60%)
   - Demos: 8 / 20 target (40%)
   - Top performer: "Body Shape" article (650 sessions, 5 demos)
   - Underperformer: "Hidden Cost" (150 sessions, 0 demos)
   - Action: Consider pausing underperformer
   ```
4. After campaign completes: Provide data for Stage 6 learning

---

## Subskill Coordination

### Data Flow Between Subskills

**content-strategy → content-generation:**
```
Output: content-opportunity.yaml
Fields:
  - topic: "Enterprise white-label demand"
  - pillar: "Product capabilities"
  - content_type: "case study"
  - source_thread: "threads/sales/elsa-white-label/"
  - priority: 0.85
  - keyword: "white-label SDK"
```

**content-generation → seo-optimization:**
```
Output: draft-content.md
Fields:
  - title: "{Original title}"
  - content: "{Full draft}"
  - target_keyword: "white-label SDK"
  - content_type: "case study"
```

**seo-optimization → content-distribution:**
```
Output: optimized-content.md
Fields:
  - title: "{SEO-optimized title}"
  - meta_description: "{160 chars}"
  - content: "{Optimized with H1/H2/keywords}"
  - internal_links: ["{link1}", "{link2}"]
```

**content-distribution → performance-tracking:**
```
Output: published-content.yaml
Fields:
  - url: "https://glamyouup.com/blog/white-label-sdk-case-study"
  - utm_params: "?utm_source=organic&utm_medium=blog"
  - publish_date: "2024-11-16"
  - channels: ["blog", "linkedin", "email"]
```

---

## Quality Gates

**Between each stage, validate:**

### After Content Strategy
- [ ] Opportunity maps to content pillar
- [ ] Source thread has sufficient learning
- [ ] Priority score calculated with reasoning
- [ ] Keyword identified from SEO strategy

### After Content Generation
- [ ] Draft follows brand voice (educational, technical)
- [ ] Includes data/sources from thread
- [ ] Proper length for content type
- [ ] No sales pitch (knowledge sharing only)

### After SEO Optimization
- [ ] Keyword in H1, first 100 words, H2s
- [ ] Meta description 150-160 chars
- [ ] Internal links relevant and working
- [ ] Alt text on images

### After Human Review
- [ ] Technical accuracy verified
- [ ] Voice/tone approved
- [ ] Depth sufficient (not surface-level)
- [ ] Ready for publication

### After Content Distribution
- [ ] Published to correct channels
- [ ] UTM parameters applied
- [ ] Cross-promotion scheduled
- [ ] URLs tracked

---

## Human Touchpoints

### Required Human Actions

**1. Approve content creation** (after content-strategy)
- Review flagged opportunities in ops/today.md
- Decide: Create this content? (yes/no)

**2. Review draft** (after seo-optimization)
- Check technical accuracy
- Validate voice/depth
- Edit if needed, approve when ready

**3. Publish approval** (before content-distribution)
- Final check before public
- Confirm channels (blog, LinkedIn, email)

### Optional Human Actions

**Override priority score:**
- Content-strategy suggests low priority
- Human knows it's strategically important
- Force creation anyway

**Request revisions:**
- Draft doesn't meet quality bar
- Request specific changes
- Regenerate with guidance

**Manual distribution:**
- Special announcement requires custom timing
- Coordinate with product launch, event, etc.

---

## Output Structure

### Campaign Thread (Decision + Execution Tracking)

**Campaign in threads:**
```
threads/marketing/campaigns/{campaign-slug}/
├── metadata.yaml
│   ├── campaign_name: "DTC Awareness Nov 2024"
│   ├── segment: "dtc-fashion"
│   ├── goal: "20 qualified demos"
│   ├── status: "active|completed"
│   └── created: "2024-11-16"
├── 1-input.md
├── 2-hypothesis.md
├── 3-implication.md
├── 4-decision.md (content plan)
├── 5-actions/
│   └── execution-log.md (track progress)
└── 6-learning.md (results + Canvas updates)
```

### Published Campaign Content

**Final outputs in:**
```
artifacts/marketing/campaigns/{campaign-slug}/
├── blog/
│   ├── fit-statistics-fashion-returns.md
│   └── body-shape-vs-measurements.md
├── linkedin/
│   ├── 2024-11-16-fit-statistics.md
│   └── 2024-11-17-body-shape.md
├── email/ (if any)
│   └── 2024-11-20-campaign-update.md
└── distribution-record.yaml
    ├── campaign: "dtc-awareness-nov-2024"
    ├── content_pieces: 4 (2 blog + 2 linkedin)
    ├── urls: {...}
    └── performance: {sessions, demos, conversion}
```

### Temporary Working Files

**During Stage 5 execution:**
```
threads/marketing/campaigns/{slug}/5-actions/
├── execution-log.md (progress tracking)
└── drafts/ (temporary, deleted after publishing)
    ├── article-1-draft.md
    ├── article-1-optimized.md
    └── ...
```

**Workflow:**
1. Generate draft → Save to drafts/
2. Human reviews → Edits in place
3. Optimize SEO → Overwrite in drafts/
4. Human approves → Publish to artifacts/
5. Delete drafts/ (content now in artifacts)

---

## Monitoring & Alerts

### Auto-flag in ops/today.md

**High-priority opportunities (score ≥ 0.7):**
```markdown
## Content Opportunities

1. [Priority: 0.85] Case study: ElsaAI white-label success
   - Source: threads/sales/elsa-white-label/6-learning.md
   - Pillar: Product capabilities
   - Keyword: "white-label SDK"
   - Estimated impact: 500 sessions/month, 25 demos
   - Action: Approve to generate draft
```

**Drafts awaiting review:**
```markdown
## Content Drafts Ready

1. "How Enterprise Fashion Brands Use White-Label SDKs"
   - Type: Case study (1,200 words)
   - Location: threads/marketing/campaigns/luxury-validation-nov-2024/5-actions/drafts/case-study-optimized.md
   - Action: Review and approve for publication
```

**Performance alerts:**
```markdown
## Content Performance

Top performer (last 7 days):
- "Reduce Returns Guide": 850 sessions, 42 demo requests (+120% vs avg)
- Action: Create follow-up content on this topic

Underperformer (last 30 days):
- "Fashion E-commerce Trends": 45 sessions, 0 conversions
- Action: Review SEO, consider update or archive
```

---

## Success Metrics

**Content pipeline efficiency:**
- Time from thread completion to published content: <7 days
- Human review time per draft: <30 minutes
- Revision rounds before approval: <2

**Content quality:**
- Technical accuracy: 100% (verified by human)
- SEO optimization: All required elements present
- Brand voice: Educational, technical, non-promotional

**Business impact:**
- Organic traffic from content: {target sessions/month}
- Demos from content: {target conversions/month}
- Pipeline influenced: {target revenue influenced}

---

## Error Handling

**If source thread incomplete:**
- Skip content-strategy, wait for thread to finish
- Flag: "Thread X in progress, defer content creation"

**If SEO keyword research fails (web_search unavailable):**
- Use keywords from marketing-narrative/seo-strategy.md
- Flag: "Used fallback keywords, validate post-publication"

**If human rejects draft:**
- Log rejection reason
- Regenerate with feedback
- Track: Rejection rate by content type/pillar

**If publication fails:**
- Keep draft in threads/marketing/campaigns/{campaign-slug}/5-actions/drafts/
- Alert in ops/today.md
- Retry with human assistance

---

## Usage Examples

### Example 1: Automated Pipeline

**Scenario:** Sales thread closes (ElsaAI deal won)
```
1. Thread: threads/sales/elsa-white-label/6-learning.md completes
   - Learning: "Luxury brands prefer white-label (validated)"

2. marketing-execution/content-strategy detects opportunity
   - Campaign: "Luxury Validation Nov 2024"
   - Type: Validation (case study)
   - Priority: 0.85 (high)
   - Keyword: "white-label SDK"

3. Flag in ops/today.md:
   "Create campaign: Luxury validation case study? (Priority: 0.85)"

4. Bella approves: "Yes, create campaign thread"

5. Human creates campaign thread: threads/marketing/campaigns/luxury-validation-nov-2024/
   - Stage 1-4: Campaign planning (hypothesis, implication, content plan)

6. marketing-execution orchestrates Stage 5:

   6a. marketing-execution/content-generation:
       - Reads campaign decision + source thread 6-learning.md
       - Generates 1,200-word case study
       - Saves to: 5-actions/drafts/case-study-draft.md

   6b. marketing-execution/seo-optimization:
       - Keyword "white-label SDK" in H1, H2s
       - Meta description: 160 chars
       - Internal links: 3 related articles
       - Saves to: 5-actions/drafts/case-study-optimized.md

   6c. Flag for review: "Draft ready for review"

   6d. Bella reviews, edits, approves

   6e. marketing-execution/content-distribution:
       - Publish to: artifacts/marketing/campaigns/luxury-validation-nov-2024/
         - blog/elsaai-case-study.md
         - linkedin/2024-11-17-elsaai.md
       - UTM: utm_campaign=luxury-validation-nov-2024
       - Delete drafts/

   6f. Update execution-log.md: [x] Case study published

7. marketing-execution/performance-tracking:
   - Monitor traffic (first 30 days)
   - Track demo requests attributed to campaign
   - Report weekly in ops/today.md

8. Human completes Stage 6 (Learning):
   - Measured: 650 sessions, 8 demos, 1.23% conversion
   - Canvas update: H1 validated (case studies convert better)
```

### Example 2: Manual Content Request

**Scenario:** Bella wants specific content
```
Bella: "Create a blog post about reducing fashion returns, 
        target keyword 'ecommerce return rate'"

1. marketing-execution receives request
   - Topic: Reduce fashion returns
   - Type: Blog article
   - Keyword: "ecommerce return rate"
   - Source: None specified (use Canvas + sales narratives)

2. Skip content-strategy (manual request)

3. marketing-execution/content-generation:
   - Load: Canvas problem.md, sales narratives
   - Generate: 1,800-word educational guide
   - Structure: Problem → Solutions → Implementation

4. marketing-execution/seo-optimization:
   - Optimize for "ecommerce return rate"
   - Add related keywords: "reduce returns", "fit issues"

5. Save to drafts/, notify Bella

6. Bella reviews, approves

7. marketing-execution/content-distribution:
   - Publish to blog
   - Schedule LinkedIn posts (3 excerpts)
   - Add to newsletter

8. marketing-execution/performance-tracking:
   - Track ranking for "ecommerce return rate"
   - Monitor organic traffic growth
```

---

## Best Practices

**1. Learning-driven, not calendar-driven**
- Content created when threads generate insights
- No "publish 4 posts this week" quotas
- Quality and substance over frequency

**2. Human in the loop for quality**
- AI generates drafts (80% complete)
- Human ensures accuracy and depth (20% refinement)
- Never auto-publish without human review

**3. SEO without keyword stuffing**
- Keywords integrated naturally
- Educational content that happens to rank
- Not "SEO content" that sacrifices quality

**4. Cross-channel coordination**
- Same core message, adapted format
- Blog → LinkedIn excerpts → Email highlights
- Consistent positioning across channels

**5. Continuous improvement**
- Track what content drives pipeline
- Double down on top performers
- Retire underperforming topics/formats

---

## Remember

**Marketing execution is:**
- Creating valuable content from business learning
- Building authority through educational depth
- Optimizing for discovery while maintaining quality
- Measuring impact on business goals (demos, pipeline)

**Marketing execution is NOT:**
- Hitting arbitrary publishing quotas
- Gaming engagement algorithms
- Keyword stuffing for SEO
- Sales pitches disguised as content

**Success = Content that educates AND converts organically.**
```


<!-- FILE: content-distribution/SKILL.md -->

# content-distribution/SKILL.md

```markdown
---
name: content-distribution
description: Publish optimized content to appropriate channels (blog, LinkedIn, website, email) with proper formatting, UTM tracking, and cross-promotion scheduling. Coordinates multi-channel distribution while maintaining consistent messaging and tracking attribution.
allowed-tools: "Read,Write,Bash"
---

# Content Distribution

You publish optimized content to appropriate channels with tracking.

## Purpose

Optimized content → Published across channels → Tracked for performance

**Core principle:** Consistent positioning, channel-adapted execution, full attribution tracking.

---

## Input Requirements

### Required Inputs

**1. Optimized content:**
```
threads/marketing/campaigns/{campaign-slug}/5-actions/drafts/{piece}-optimized.md
```

**2. Distribution plan (from metadata or manual):**
```yaml
channels: ["blog", "linkedin", "email"]
publish_date: "2024-11-16"
priority: "high"
```

**3. Channel guidelines:**
```
artifacts/marketing/narrative/channel-guidelines.md
```

---

## Distribution Channels

### Supported Channels

**Primary:**
- `blog` - Company blog (hosted on website)
- `linkedin` - Company LinkedIn page
- `website` - Website pages (product, pricing, about)
- `email` - Email newsletters/announcements

**Secondary (future):**
- `twitter` - Company Twitter/X account
- `youtube` - Video content
- `medium` - Syndicated content

---

## Distribution Process

### Step 1: Validate Content Ready

**Check optimized content:**
- [ ] SEO optimization complete
- [ ] Human approval received
- [ ] Customer names approved (if applicable)
- [ ] No confidential information
- [ ] Images compressed and optimized
- [ ] Internal links functional

**If not ready:**
- Flag in ops/today.md: "Content blocked - awaiting approval"
- Do not proceed to publication

### Step 2: Prepare Channel-Specific Versions

**Load channel guidelines:**
```bash
artifacts/marketing/narrative/channel-guidelines.md
```

**For each target channel:**
1. Read channel-specific formatting requirements
2. Adapt content to channel format
3. Add channel-specific elements (UTMs, hashtags, CTAs)
4. Validate formatting

---

## Channel-Specific Formatting

### Blog Distribution

**Target:** Company blog at `{website}/blog/{slug}`

**Process:**

1. **Convert to blog format:**
```markdown
---
title: "{SEO-optimized title}"
description: "{Meta description}"
author: "{Author name or 'GlamYouUp Team'}"
date: "{YYYY-MM-DD}"
categories: ["{pillar}", "{secondary category}"]
tags: ["{keyword}", "{related tags}"]
featured_image: "{image URL}"
---

{Optimized content body}
```

2. **Add blog-specific elements:**
- Author bio (bottom of article)
- Related articles (3-5 links, same pillar)
- Newsletter signup CTA (bottom)
- Social share buttons

3. **Set URL structure:**
```
https://{website}/blog/{slug}

Example:
https://glamyouup.com/blog/elsaai-white-label-sdk-case-study
```

4. **Add UTM parameters for tracking:**
```
Base URL: https://glamyouup.com/blog/elsaai-white-label-sdk-case-study

For LinkedIn share: ?utm_source=linkedin&utm_medium=social&utm_campaign={campaign-slug}
For Email: ?utm_source=email&utm_medium=newsletter&utm_campaign={campaign-slug}
For Organic: No UTM (default)
```

5. **Generate sitemap entry:**
```xml
<url>
  <loc>https://glamyouup.com/blog/elsaai-white-label-sdk-case-study</loc>
  <lastmod>2024-11-16</lastmod>
  <changefreq>monthly</changefreq>
  <priority>0.8</priority>
</url>
```

6. **Output location:**
```
artifacts/marketing/blog/{slug}.md
```

---

### LinkedIn Distribution (Company Page)

**Target:** LinkedIn company page post

**Process:**

1. **Determine post type:**
- Full article: Publish to LinkedIn Articles (long-form)
- Excerpt: Standard post (300-600 words) with link to blog
- Announcement: Product/feature announcement format

**For excerpt post (most common):**

2. **Create LinkedIn version:**
```markdown
{Opening hook - 1-2 sentences from article}

{Key insight or data point - 150-200 words}

{Implication or learning - 100-150 words}

{Soft link to full article}

---

Read the full case study: {blog URL with UTM}
```

**Example (ElsaAI case study):**
```markdown
We closed 5 enterprise fashion deals in Q4. All 5 chose white-label SDK over co-branded.

This wasn't random. Luxury brands ($100M+ GMV) prioritize brand consistency over vendor recognition.

What we learned:

**Co-branded widgets break luxury aesthetics**
Even minimal branding ("Powered by X") creates friction. One customer told us: "Our customers don't care who powers fit recommendations. They care that it looks like us."

**The numbers prove it matters**
ElsaAI (luxury marketplace, $200M GMV) saw:
- 38% return reduction with white-label
- 94% fit accuracy
- $805K annual savings

They paid 3x more for white-label because brand consistency is non-negotiable.

**Industry insight:** Customer segment dictates product packaging. Same technology, different positioning.

Full case study with metrics and technical implementation: https://glamyouup.com/blog/elsaai-white-label-sdk-case-study?utm_source=linkedin&utm_medium=social&utm_campaign={campaign-slug}
```

3. **Add LinkedIn-specific elements:**
- Hashtags (3-5 max): `#B2BSaaS #FashionTech #EnterpriseSDK`
- Placement: End of post (not mid-text)
- First comment: Additional context or link to technical docs

4. **Formatting:**
- Short paragraphs (1-2 sentences)
- Line breaks for readability
- Bold for key points (sparingly)
- No emoji (professional B2B tone)

5. **Image:**
- Size: 1200x627px (landscape)
- Include: Key stat or quote as graphic
- Alt text: Descriptive with keyword

6. **Posting schedule:**
- Optimal time: Tuesday-Thursday, 8-10am or 12-1pm (target timezone)
- Avoid: Weekends, holidays, late evenings

7. **Output location:**
```
artifacts/marketing/linkedin/posts/{date}-{slug}.md
```

---

### Website Distribution

**Target:** Website pages (product, case studies, resources)

**Process:**

1. **Determine page type:**
- Case study page: Add to `/case-studies/{slug}`
- Resource: Add to `/resources/` or `/blog/`
- Product page update: Update existing page

**For case study page:**

2. **Create website version:**
```html
<!-- Hero section -->
<section class="hero">
  <h1>{Customer Name}: {Result}</h1>
  <p class="lead">{One-sentence summary}</p>
  <img src="{customer-logo}" alt="{Customer name} logo">
</section>

<!-- Stats callout -->
<section class="stats">
  <div class="stat">
    <h2>38%</h2>
    <p>Return reduction</p>
  </div>
  <div class="stat">
    <h2>$805K</h2>
    <p>Annual savings</p>
  </div>
  <div class="stat">
    <h2>30 days</h2>
    <p>Time to results</p>
  </div>
</section>

<!-- Content sections -->
{Optimized content formatted for web}

<!-- CTA section -->
<section class="cta">
  <h2>Ready for similar results?</h2>
  <a href="/demo" class="btn">Request Demo</a>
</section>
```

3. **Add structured data (JSON-LD):**
```json
{
  "@context": "https://schema.org",
  "@type": "CaseStudy",
  "name": "ElsaAI White-Label SDK Implementation",
  "description": "How ElsaAI reduced returns by 38% using white-label fit recommendations",
  "author": {
    "@type": "Organization",
    "name": "GlamYouUp"
  },
  "result": "38% reduction in return rate, $805K annual savings"
}
```

4. **Internal navigation:**
- Breadcrumbs: Home > Case Studies > ElsaAI
- Related case studies (bottom)
- CTA: Demo request, contact sales

5. **Output location:**
```
artifacts/marketing/website/{slug}.html
```

---

### Email Distribution

**Target:** Newsletter, announcement, or drip sequence

**Process:**

1. **Determine email type:**
- Newsletter: Include as section in regular newsletter
- Standalone: Dedicated email announcement
- Drip sequence: Add to nurture sequence

**For newsletter section:**

2. **Create email version:**
```markdown
Subject: New case study: 38% return reduction with white-label SDK

Preview text: Learn how ElsaAI (luxury marketplace, $200M GMV) achieved $805K in annual savings

---

Hi {First_Name},

**New case study: ElsaAI reduces returns 38% with white-label SDK**

We just published a detailed case study on how ElsaAI, a luxury fashion marketplace, reduced returns by 38% using our white-label SDK.

Key results:
- 38% return reduction (25% → 18%)
- 94% fit accuracy
- $805K annual savings
- 30-day implementation

What made this work:
1. White-label branding (no third-party logos)
2. AI-powered fit recommendations
3. Fast integration (2 weeks)

The full case study includes metrics, technical implementation details, and ROI analysis.

Read the full case study →
{blog URL with UTM: ?utm_source=email&utm_medium=newsletter&utm_campaign={campaign-slug}}

---

{Other newsletter sections}

---

Best,
{Name}
{Title}, GlamYouUp
```

3. **Email formatting:**
- Subject: 40-50 characters
- Preview text: Extend subject, don't repeat
- Single column, mobile-optimized
- CTA button (not just text link)
- Unsubscribe link (required)

4. **Segmentation (if applicable):**
- Send to: Enterprise segment (matches case study ICP)
- Exclude: Customers already using white-label
- Timing: Tuesday-Thursday, 10am (target timezone)

5. **Output location:**
```
artifacts/marketing/email/{date}-{slug}.md
```

---

## UTM Tracking Strategy

### UTM Parameter Structure

**Format:**
```
?utm_source={source}&utm_medium={medium}&utm_campaign={campaign}&utm_content={content}
```

**Parameters:**

**utm_source (required):**
- Where traffic originates
- Values: `linkedin`, `email`, `twitter`, `organic`

**utm_medium (required):**
- Marketing medium
- Values: `social`, `newsletter`, `email`, `referral`

**utm_campaign (required):**
- Campaign name
- Values: `case-study`, `product-launch`, `thought-leadership`

**utm_content (optional):**
- Differentiate similar links
- Values: `cta-button`, `inline-link`, `footer`

### UTM Examples by Channel

**Blog post shared on LinkedIn:**
```
https://glamyouup.com/blog/elsaai-white-label-sdk-case-study
?utm_source=linkedin
&utm_medium=social
&utm_campaign={campaign-slug}
&utm_content=company-page
```

**Email newsletter link:**
```
https://glamyouup.com/blog/elsaai-white-label-sdk-case-study
?utm_source=email
&utm_medium=newsletter
&utm_campaign={campaign-slug}
&utm_content=cta-button
```

**LinkedIn first comment (additional resources):**
```
https://glamyouup.com/docs/white-label-sdk
?utm_source=linkedin
&utm_medium=social
&utm_campaign={campaign-slug}
&utm_content=first-comment
```

### Tracking Sheet

**Maintain tracking log:**
```yaml
# tracking-log.yaml

- content_slug: "elsaai-white-label-sdk-case-study"
  publish_date: "2024-11-16"
  urls:
    - channel: "blog"
      url: "https://glamyouup.com/blog/elsaai-white-label-sdk-case-study"
      utm: null  # Organic traffic
    
    - channel: "linkedin"
      url: "https://glamyouup.com/blog/elsaai-white-label-sdk-case-study"
      utm: "?utm_source=linkedin&utm_medium=social&utm_campaign={campaign-slug}"
    
    - channel: "email"
      url: "https://glamyouup.com/blog/elsaai-white-label-sdk-case-study"
      utm: "?utm_source=email&utm_medium=newsletter&utm_campaign={campaign-slug}"
```

---

## Cross-Channel Coordination

### Multi-Channel Publishing Schedule

**Day 1: Blog publication**
- Publish to blog (morning)
- Update sitemap
- Submit to Google Search Console (optional)

**Day 2: LinkedIn promotion**
- Post excerpt to LinkedIn company page (optimal time)
- First comment: Link to technical docs
- Monitor engagement (respond to comments within 1 hour)

**Day 3-5: Email distribution**
- Add to weekly newsletter (next edition)
- Or: Send standalone announcement (if high-priority)

**Day 7: Performance check**
- Monitor analytics (traffic, engagement)
- Flag top performers for follow-up content

### Content Repurposing

**From long-form blog post, create:**

1. **3 LinkedIn posts:**
   - Post 1: Key stat or insight (Day 2)
   - Post 2: Customer quote or result (Day 9)
   - Post 3: Technical approach or learning (Day 16)

2. **1 Email section:**
   - Newsletter feature (Week 1)

3. **Website update:**
   - Add to case studies page
   - Reference in product page ("See how ElsaAI...")

4. **Social graphics:**
   - Key stat image (1200x627px)
   - Customer quote graphic
   - Process infographic (optional)

**Repurposing schedule:**
```
Day 1: Publish blog
Day 2: LinkedIn post #1 (excerpt)
Day 3: Email newsletter
Day 9: LinkedIn post #2 (quote)
Day 16: LinkedIn post #3 (technical)
```

---

## Quality Validation

**Before publishing to each channel:**

### Blog

- [ ] **URL correct:** Matches slug, no typos
- [ ] **Images load:** All images display correctly
- [ ] **Links work:** Internal and external links functional
- [ ] **Mobile responsive:** Readable on mobile
- [ ] **Meta tags present:** Title, description, OG tags
- [ ] **Sitemap updated:** New URL in sitemap.xml

### LinkedIn

- [ ] **Formatting correct:** Line breaks, bold, no weird characters
- [ ] **Link works:** Blog URL with UTM functional
- [ ] **Image attached:** 1200x627px, loads correctly
- [ ] **Hashtags appropriate:** 3-5 relevant hashtags
- [ ] **Length appropriate:** 300-600 words (not too long)
- [ ] **No typos:** Proofread carefully

### Website

- [ ] **Page renders correctly:** No broken layouts
- [ ] **Navigation works:** Breadcrumbs, related links
- [ ] **CTA functional:** Demo request, contact links work
- [ ] **Structured data valid:** JSON-LD validates
- [ ] **Mobile responsive:** Readable on all devices

### Email

- [ ] **Subject line compelling:** 40-50 chars, no spam triggers
- [ ] **Preview text set:** Extends subject line
- [ ] **Links tracked:** UTM parameters applied
- [ ] **Images load:** All images display (with fallback)
- [ ] **Unsubscribe link:** Required, functional
- [ ] **Mobile responsive:** Single column, readable
- [ ] **Spam score low:** Test with mail-tester.com

---

## Output Format

### Distribution Record
```yaml
# distribution-record-{date}-{slug}.yaml

content_slug: "elsaai-white-label-sdk-case-study"
content_title: "White-Label SDK Case Study: ElsaAI Reduces Returns 38%"
publish_date: "2024-11-16"

channels:
  - name: "blog"
    url: "https://glamyouup.com/blog/elsaai-white-label-sdk-case-study"
    status: "published"
    published_at: "2024-11-16T09:00:00Z"
    
  - name: "linkedin"
    url: "https://www.linkedin.com/company/glamyouup/posts/..."
    status: "published"
    published_at: "2024-11-17T10:00:00Z"
    engagement:
      impressions: null  # Updated by performance-tracking
      clicks: null
      likes: null
      comments: null
    
  - name: "email"
    campaign: "Weekly Newsletter - Nov 16"
    status: "scheduled"
    send_date: "2024-11-19T10:00:00Z"
    segment: "enterprise-segment"
    recipients: 1250

utm_tracking:
  linkedin: "?utm_source=linkedin&utm_medium=social&utm_campaign={campaign-slug}"
  email: "?utm_source=email&utm_medium=newsletter&utm_campaign={campaign-slug}"

files_created:
  - "artifacts/marketing/blog/elsaai-white-label-sdk-case-study.md"
  - "artifacts/marketing/linkedin/posts/2024-11-17-elsaai-case-study.md"
  - "artifacts/marketing/email/2024-11-19-newsletter.md"

next_steps:
  - "Monitor blog performance (Day 1-7)"
  - "Engage with LinkedIn comments (Day 2)"
  - "Track email open/click rates (Day 19-21)"
  - "Performance review (Day 30)"
```

### Publication Checklist
```markdown
## Publication Checklist: elsaai-white-label-sdk-case-study

**Content:** White-Label SDK Case Study: ElsaAI Reduces Returns 38%
**Date:** 2024-11-16
**Channels:** Blog, LinkedIn, Email

### Pre-Publication

- [x] Content optimized (SEO complete)
- [x] Human approval received
- [x] Customer approval (ElsaAI signed off)
- [x] Images compressed (<200KB each)
- [x] Internal links validated
- [x] No confidential information

### Blog Publication

- [x] Published to: https://glamyouup.com/blog/elsaai-white-label-sdk-case-study
- [x] Sitemap updated
- [x] Meta tags verified
- [x] Mobile responsive checked
- [x] Images loading correctly
- [x] Internal links functional

### LinkedIn Publication

- [x] Excerpt created (480 words)
- [x] Image attached (1200x627px)
- [x] UTM link: ?utm_source=linkedin&utm_medium=social&utm_campaign={campaign-slug}
- [x] Hashtags: #B2BSaaS #FashionTech #EnterpriseSDK
- [x] Scheduled: 2024-11-17 10:00am PST
- [x] First comment prepared (link to technical docs)

### Email Publication

- [x] Added to newsletter (Nov 19 edition)
- [x] Subject: "New case study: 38% return reduction"
- [x] Preview text set
- [x] UTM link: ?utm_source=email&utm_medium=newsletter&utm_campaign={campaign-slug}
- [x] Segment: Enterprise (1,250 recipients)
- [x] Scheduled: 2024-11-19 10:00am PST
- [x] Unsubscribe link functional

### Post-Publication

- [ ] Monitor blog traffic (Day 1-7)
- [ ] Respond to LinkedIn comments (Day 2)
- [ ] Track email metrics (Day 19-21)
- [ ] Update distribution record with metrics
- [ ] Performance review (Day 30)
```

---

## Automation Capabilities

### Automated Tasks

**Can be automated:**
- Blog publishing (deploy markdown to website)
- Sitemap generation
- UTM parameter creation
- Tracking log updates
- File organization (move to published/)

**Requires human action:**
- LinkedIn posting (API limitations, human voice)
- Email sending (final approval before send)
- Customer tagging/mentions (judgment call)
- Engagement responses (community management)

### Human Approval Gates

**Required human approval:**
1. **Before first publication:** Final content review
2. **Before LinkedIn post:** Tone/voice check
3. **Before email send:** Segment and timing validation

**Optional human approval:**
- Cross-channel promotion schedule
- Hashtag selection
- Social image design

---

## Error Handling

### Publication Failures

**If blog publish fails:**
- Keep draft in `threads/marketing/campaigns/{campaign-slug}/5-actions/drafts/`
- Flag in ops/today.md: "Blog publish failed - {error}"
- Retry or request human assistance

**If LinkedIn post fails:**
- Keep draft in `threads/marketing/campaigns/{campaign-slug}/5-actions/drafts/`
- Alert in ops/today.md
- Human posts manually with saved draft

**If email send fails:**
- Abort send (don't partial-send)
- Alert in ops/today.md: "Email send failed - {error}"
- Reschedule after troubleshooting

### Broken Links

**If internal link broken:**
- Flag in publication checklist
- Request human to update or remove link
- Do not publish with broken links

**If external link broken:**
- Replace with archive.org link (if critical)
- Or remove link and note in content
- Flag for human review

### Customer Approval Missing

**If using customer name without approval:**
- Block publication
- Flag: "Customer approval required for {customer}"
- Wait for explicit approval before proceeding

---

## Success Metrics

**Distribution efficiency:**
- Time from optimization to publication: <24 hours
- Multi-channel coordination: Same-day blog + next-day LinkedIn
- Error rate: <5% (publication failures)

**Channel coverage:**
- Blog: 100% of content
- LinkedIn: 80% of content (high-value only)
- Email: 50% of content (newsletter-worthy)
- Website: 30% of content (case studies, resources)

**Tracking accuracy:**
- UTM parameters applied: 100%
- Tracking log updated: 100%
- Attribution captured: >95%

---

## Usage Example

**Input:**
```
Campaign: threads/marketing/campaigns/luxury-validation-nov-2024/
Optimized content: 5-actions/drafts/elsaai-case-study-optimized.md
Channels: ["blog", "linkedin", "email"]
Priority: high
```

**Process:**
```
1. Validate ready for publication:
   - ✓ SEO optimized
   - ✓ Human approved
   - ✓ Customer approved (ElsaAI signed off)
   - ✓ No confidential info

2. Blog distribution:
   - Convert to blog format
   - Add author bio, related articles
   - Set URL: /blog/elsaai-white-label-sdk-case-study
   - Publish: 2024-11-16 09:00am
   - Update sitemap
   - Output: artifacts/marketing/blog/elsaai-white-label-sdk-case-study.md

3. LinkedIn distribution:
   - Create excerpt (480 words)
   - Add UTM: ?utm_source=linkedin&utm_medium=social&utm_campaign={campaign-slug}
   - Schedule: 2024-11-17 10:00am
   - Prepare first comment (technical docs link)
   - Output: artifacts/marketing/linkedin/posts/2024-11-17-elsaai-case-study.md

4. Email distribution:
   - Add to Nov 19 newsletter
   - Subject: "New case study: 38% return reduction"
   - Add UTM: ?utm_source=email&utm_medium=newsletter&utm_campaign={campaign-slug}
   - Segment: Enterprise (1,250 recipients)
   - Schedule: 2024-11-19 10:00am
   - Output: artifacts/marketing/email/2024-11-19-newsletter.md

5. Create tracking record:
   - Save: distribution-record-2024-11-16-elsaai-white-label.yaml
   - Log all URLs with UTM parameters

6. Update ops/today.md:
   - "Published: ElsaAI case study (blog, LinkedIn scheduled, email scheduled)"

7. Set performance tracking:
   - Monitor blog: Days 1-7
   - Monitor LinkedIn: Day 2 (engagement)
   - Monitor email: Days 19-21 (open/click)
```

---

## Remember

**Content distribution is:**
- Publishing optimized content to appropriate channels
- Adapting format per channel (same message, different execution)
- Tracking attribution with UTM parameters
- Coordinating cross-channel promotion

**Content distribution is NOT:**
- Blasting same content to all channels unchanged
- Publishing without tracking
- Auto-posting without human approval (LinkedIn, email)
- Sacrificing quality for speed

**Success = Consistent positioning across channels with full attribution tracking.**
```


<!-- FILE: content-generation/SKILL.md -->

# content-generation/SKILL.md

```markdown
---
name: content-generation
description: Generate content from campaign decisions. Creates drafts in threads (planning), generates final versions in artifacts (publishing). Reads Stage 4 Decision, applies brand voice, follows content patterns.
allowed-tools: "Read,Write"
---

# Content Generation

Generate educational content drafts from campaign decisions.

## Purpose

**Stage 4 Decision → Drafts (threads) → Approval → Final content (artifacts)**

---

## Two-Phase Generation

### Phase 1: Draft Creation (threads)

**Input:** Stage 4 Decision (content plan)
**Output:** Drafts in `threads/marketing/campaigns/{slug}/5-actions/drafts/`
**Purpose:** Plan what to cover, get Bella's feedback

### Phase 2: Final Generation (artifacts)

**Input:** Approved drafts + feedback
**Output:** Published content in `artifacts/marketing/campaigns/{slug}/`
**Purpose:** Polished versions that go live

---

## Phase 1: Draft Creation

### Step 1: Read Stage 4 Decision

**Load content plan:**
```
threads/marketing/campaigns/{slug}/4-decision.md
```

**Extract:**
- Content outline (structure already defined)
- SEO requirements (keywords, meta description)
- Target audience
- Success criteria
- Distribution channels

**The Decision IS your content brief.**

---

### Step 2: Load Context

**Brand voice:**
```
artifacts/marketing/narrative/brand-voice.md
```

**Content patterns:**
```
{baseDir}/content-generation/references/substack-article-pattern.md
{baseDir}/content-generation/references/linkedin-post-pattern.md
{baseDir}/content-generation/references/twitter-thread-pattern.md
```

**Source threads (if Decision references them):**
```
{source_thread}/6-learning.md
```

**Canvas (if needed):**
```
strategy/canvas/07-uvp.md
strategy/canvas/05-problem.md
```

---

### Step 3: Generate Drafts

**Generate ALL formats in parallel:**
- Substack article draft
- LinkedIn post draft
- Twitter thread draft

**Save to threads:**
```
threads/marketing/campaigns/{slug}/5-actions/drafts/{piece-name}-article.md
threads/marketing/campaigns/{slug}/5-actions/drafts/{piece-name}-linkedin.md
threads/marketing/campaigns/{slug}/5-actions/drafts/{piece-name}-twitter.md
```

**Drafts are planning documents:**
- 70-80% complete
- Structure follows patterns
- Content needs refinement
- Awaiting Bella's feedback

---

### Step 4: Flag for Review

**Update ops/today.md:**
```
## Drafts Ready for Review

**{Article Title}**
- Location: threads/marketing/campaigns/{slug}/5-actions/drafts/
- Formats: Article + LinkedIn + Twitter
- Action: Review and approve for final generation
```

---

## Phase 2: Final Generation

### After Bella Approves Drafts

**Input:**
- Approved drafts from threads
- Bella's batch feedback

**Process:**
1. Read approved drafts
2. Apply feedback
3. Polish content (final 20%)
4. Apply content patterns precisely:
   - Substack: Include "About me" section (per pattern)
   - LinkedIn: NO "About me" (per pattern)
   - Twitter: NO "About me" (per pattern)

**Save to artifacts:**
```
artifacts/marketing/campaigns/{slug}/{piece-name}.md           # Substack article
artifacts/marketing/campaigns/{slug}/distribution/{piece-name}-linkedin.md
artifacts/marketing/campaigns/{slug}/distribution/{piece-name}-twitter.md
```

**These are published versions:**
- 100% complete
- Ready to go live
- Final formatting applied
- SEO optimized

---

## Content Requirements

### Brand Voice (from brand-voice.md)

**Apply:**
- BUILD + RUN positioning
- Reality over hype
- Technical depth
- GCC awareness (if applicable)
- Educational, not promotional
- Honest about limitations
- ICP-aligned examples (no circular self-references)

### Pattern Compliance

**Substack article:**
- Follow substack-article-pattern.md
- Include "About me" section (before metadata)
- 5,000-7,500 words
- SEO requirements from Decision

**LinkedIn post:**
- Follow linkedin-post-pattern.md
- NO "About me" section (platform-inappropriate)
- 200-300 words max
- Link to full article

**Twitter thread:**
- Follow twitter-thread-pattern.md
- NO "About me" tweets (bio visible)
- 10-15 tweets max
- Hook → Insights → Proof → CTA

---

## Process Rules

### Always Generate in Parallel

**Correct:**
```
Decision → Generate (article + LinkedIn + Twitter) drafts → Save all → Review
```

**Wrong (sequential takes 5 hours):**
```
Generate article → Review → Generate LinkedIn → Review → Generate Twitter
```

### Stage 4 Decision = Content Brief

**Don't:**
- Ask Bella for separate brief
- Guess requirements

**Do:**
- Read Decision first
- Use outline already defined
- Apply SEO requirements specified

### Single-Pass Review

**Draft → Review → Feedback → Final → Done**

Not: Draft → Review → Revise → Review → Revise → Review...

---

## File Structure

```
threads/marketing/campaigns/{slug}/
├── 4-decision.md              # Content plan (what to cover)
└── 5-actions/
    └── drafts/
        ├── {piece}-article.md       # Draft article (planning)
        ├── {piece}-linkedin.md      # Draft LinkedIn (planning)
        └── {piece}-twitter.md       # Draft Twitter (planning)

artifacts/marketing/campaigns/{slug}/
├── {piece}.md                       # Published article (final)
└── distribution/
    ├── {piece}-linkedin.md          # Published LinkedIn (final)
    └── {piece}-twitter.md           # Published Twitter (final)
```

---

## Example: Part 2 Fix

**What happened (5 hours):**
- Sequential generation (article, then LinkedIn, then Twitter)
- Multiple revision rounds
- Forgot "About me" rules
- Manual fixes

**What should happen (2 hours):**

**Phase 1 (Drafts):**
```
Read: threads/marketing/campaigns/leanos-launch-nov-2025/4-decision.md
Generate in parallel:
  - part-2-ten-ai-agents-article.md (draft)
  - part-2-ten-ai-agents-linkedin.md (draft)
  - part-2-ten-ai-agents-twitter.md (draft)
Save to: threads/.../5-actions/drafts/
Flag in ops/today.md
```

**Phase 2 (Final):**
```
Bella reviews drafts (30 min)
Bella approves with feedback
Generate final versions:
  - part-2-ten-ai-agents.md (Substack, "About me" included)
  - distribution/part-2-linkedin.md (NO "About me")
  - distribution/part-2-twitter.md (NO "About me")
Save to: artifacts/marketing/campaigns/leanos-launch-nov-2025/
```

**Time: 2 hours total (vs 5)**

---

## Success Metrics

**Efficiency:**
- Draft generation: <1 hour (all formats)
- Review time: <45 min (batch review)
- Final generation: <30 min
- Total: <2 hours (draft → final)

**Quality:**
- Approval rate: >80% (drafts accepted with minor edits)
- Revision rounds: <2
- Factual errors: 0

---

## Remember

**Drafts = Planning (threads)**
- What we'll cover
- Get feedback
- 70-80% complete

**Final = Publishing (artifacts)**
- What actually goes live
- Polished, ready
- 100% complete

**Root problem solved:**
- Parallel generation (not sequential)
- Pattern files enforce rules ("About me" placement)
- Stage 4 Decision = content brief
- Two-phase: draft → final

**Today's 5-hour problem → 2-hour solution.**

---

**Last updated:** 2025-11-21
**Pattern files:** references/substack-article-pattern.md, linkedin-post-pattern.md, twitter-thread-pattern.md
```


<!-- FILE: content-generation/references/linkedin-post-pattern.md -->

# content-generation/references/linkedin-post-pattern.md

```markdown
# LinkedIn Post Pattern

**Format:** Short-form professional content (200-300 words max)
**Tone:** Professional, educational, proof-driven
**Purpose:** Amplify main content, drive traffic to detailed articles

---

## Structure Template

```markdown
[Hook - 1 compelling sentence that makes them stop scrolling]

[Context - 2-3 sentences explaining what this is about]

[Key Insight - 3-5 bullet points, scannable format]

[Proof/Example - 1-2 sentences with real numbers or outcomes]

[CTA - 1 sentence with link to full content]

---

Read the full breakdown: [Link to Substack/blog article] (if applicable)

Repository: https://lnkd.in/d4HbgBjG (if applicable)

---

[Optional: Preview of next piece or related topic]

[Optional: Engagement question - only if natural, NO forced "What do you think? 👇"]
```

---

## Content Requirements

**NO "About me" section:**
- LinkedIn profile already shows bio
- Keep post focused on content
- Platform-inappropriate to duplicate bio

**Scannable format:**
- Short paragraphs (2-3 sentences max)
- Bullet points for key insights
- White space for readability

**Professional tone:**
- BUILD + RUN positioning maintained
- Technical credibility signals
- No hype or buzzwords

**Clear CTA:**
- Link to full article (primary)
- Repository link (secondary)
- No hard sell ("Book a demo now!")

---

## Hook Patterns (Choose based on content)

**Data-driven hook:**
```
Built LeanOS in 2 weeks. Uses it to operate 2 companies simultaneously.

Here's the architecture that makes it possible:
```

**Contrarian hook:**
```
5-10x AI productivity claims aren't validated.

Here's what actually works:
```

**Proof-first hook:**
```
$200/month AI costs vs $200k team.

How 2 people operate like 10:
```

**Reality-check hook:**
```
Most fractional CTOs advise-only. Development agencies build-only.

You need BUILD + RUN.
```

---

## Key Insights Format

**Use bullets or short numbered list:**

```
The 10 agents in 5 layers:

**Strategy & Foundation (4 agents):**
- Canvas population, ICPs, sales narratives, marketing narratives

**Sales Execution (1 orchestrator):**
- Prospecting, contact finding, outreach, qualification

**Marketing Execution (1 orchestrator):**
- Content strategy, generation, SEO, distribution, tracking
```

**Or condensed paragraphs:**

```
Why specialized agents vs one generalized AI?

Context-shaping beats generalization. Each agent optimized for specific decision types. Event-driven coordination (agents invoke each other based on state changes).
```

---

## Proof Points (Always Include)

**Real numbers from production:**
- "$200/month AI costs, operates 2 companies"
- "2-person → 10-person velocity"
- "Built in 2 weeks, refined 18 months"

**Customer metrics (if applicable):**
- "47 loans funded, $2.8M volume, 90 days"
- "38% return rate reduction, $805k annual savings"

**Technical validation:**
- "Category-theoretic system design"
- "11 Skills orchestrating autonomously"
- "Open-source: github.com/BellaBe/lean-os"

---

## Voice Guidelines

**DO:**
- Lead with BUILD + RUN proof
- Include technical depth signals
- Challenge industry hype
- Use specific numbers

**DON'T:**
- Add "About me" section (platform-inappropriate)
- Use engagement bait ("Agree? 👍 Comment below!")
- Include marketing buzzwords
- Make unvalidated claims

---

## CTA Guidelines

**Soft CTA (prefer):**
```
Read the full breakdown: [Substack link]

Repository: https://lnkd.in/d4HbgBjG
```

**Series navigation CTA:**
```
Part 2 of the LeanOS series is live.

Full breakdown: [Link to Substack article]

Part 3 coming soon: 6-stage causal flow deep dive
```

**NO hard CTAs:**
- ❌ "Book a demo now!"
- ❌ "Limited slots available!"
- ❌ "DM me for implementation!"

---

## Optional Engagement (Use Sparingly)

**Only if natural to content:**
```
Building with AI agents? This might show you different patterns.

Questions? 👇
```

**Reality-check engagement:**
```
What's your experience with [specific technical topic]?

Curious if this resonates with others.
```

**Never forced:**
- ❌ "What do you think?"
- ❌ "Agree or disagree?"
- ❌ "Tag someone who needs this!"

---

## Distribution Timing

**Publish alongside main article:**
- Same day as Substack article
- Link drives traffic to detailed content
- LinkedIn amplifies reach

**Don't publish standalone:**
- LinkedIn posts should reference longer content
- Avoid "tips" or "hot takes" without substance
- Always link to proof (repository, article, metrics)

---

## Success Metrics

**Engagement:**
- ≥20 reactions (baseline engagement)
- ≥2 substantive comments (qualified discussion)
- Click-through rate to main article

**Lead quality:**
- Substantive DMs (technical questions, implementation inquiries)
- Profile views from target segments (technical founders, investors)

---

## Example: Part 2 LinkedIn Post

```markdown
Part 2 of the LeanOS series is live.

The 10 specialized AI agents explained through one example: FastCapital (digital lending platform).

Full breakdown: [Link to Substack article]

---

**Why 10 specialized agents instead of one generalized AI?**

Context-shaping beats generalization.

Each agent optimized for specific decision types. Event-driven coordination (agents invoke each other based on state changes).

---

**FastCapital example (2-person team):**

Sarah (fintech PM, non-developer) + Chris (engineer) build lending platform:

Week 1: Chris onboards in 4 hours via Canvas
Week 2: Platform built (Chris directs Agent #9)
Week 3: First loan funded
90 days: 47 loans, $2.8M volume, $60k revenue

2 people operate like 8-person team.

---

**Reality check included:**

Claude might hallucinate.
Your co-founder might not get it.
The market might not cooperate.

LeanOS doesn't guarantee success.
It guarantees fast learning.

---

Full article covers:
- All 10 agents with FastCapital examples
- How Sarah + Chris divide responsibilities
- What can go wrong
- Validation-driven approach

Read here: [Link to Substack article]

Repository: https://lnkd.in/d4HbgBjG

---

Part 3 coming soon: 6-stage causal flow deep dive, evaluation guide, implementation options.

---

Building with AI agents? This might show you different patterns.

Questions? 👇
```

---

**Last updated:** 2025-11-21
**Used by:** content-generation skill
```


<!-- FILE: content-generation/references/substack-article-pattern.md -->

# content-generation/references/substack-article-pattern.md

```markdown
# Substack Article Pattern

**Format:** Long-form educational content (5,000-7,500 words)
**Tone:** Educational, technical depth, honest about limitations
**Purpose:** Build authority through deep knowledge sharing

---

## Structure Template

```markdown
# Title: [Main Title]
## Subtitle: [Engaging Subtitle]

**Series:** [← Part X: Title](#) | Part Y of Z (you are here) | [Part Z: Title →](#)

---

## Introduction (300-500 words)
- Hook: Compelling opening that shows why this matters
- Context: What problem/topic we're addressing
- Preview: What reader will learn (3-5 key takeaways)

---

## Main Content (4,000-6,000 words)

### Section 1: [Core Concept/Problem]
- Deep dive into the main topic
- Technical details with examples
- Real data/metrics from production

### Section 2: [Solution/Approach]
- How to address the problem
- Step-by-step breakdown
- Architecture/methodology details

### Section 3: [Implementation/Case Study]
- Real example with complete context
- Metrics (before/after)
- What worked, what didn't

### Section 4: [Reality Check]
- What can go wrong
- Limitations acknowledged
- When this approach doesn't apply

---

## Key Takeaways (200-300 words)
- Summarize main learnings (3-5 bullet points)
- Actionable insights
- What reader should remember

---

## Continue the Series (if applicable)

**[← Part X: Title](#)** - Brief description

**Part Y (you just read):** Brief description

**[Part Z: Title →](#)** - Brief description

---

**About me:**

Built LeanOS in 2 weeks, refined continuously in production. Uses it to operate GlamYouUp + PersonalOS simultaneously. Currently implementing for Detekta (AI breach report generator for GCC financial institutions). Offers fractional CTO services implementing the same methodology for funded founders. Based in UAE, serving GCC + global markets.

---

## About This Article

**Campaign:** [Campaign name]
**Part:** [X of Y]
**Generated:** [Skill/method used]
**Series navigation:** [← Part X](#) | Part Y (you are here) | [Part Z →](#)

---

**Word count:** ~[X,XXX] words
**Read time:** ~[X] minutes
**Next:** [Part Z: Title →](#)

**Open Source:** [LeanOS Repository](https://github.com/BellaBe/lean-os) (GitHub)
```

---

## Content Requirements

**Educational focus:**
- Teach concepts, don't sell services
- Share methodology openly
- Reader learns regardless of hiring

**Technical depth:**
- Include architecture details
- Show code/diagrams where relevant
- Don't oversimplify for mass appeal

**Proof-driven:**
- Real metrics from production
- Specific numbers (not vague claims)
- Customer names (if approved) or realistic examples

**Honest:**
- Acknowledge limitations
- Include "Reality Check" section
- Discuss what can go wrong

**BUILD + RUN positioning:**
- Distinguish engineering (BUILD) from operations (RUN)
- Show both layers in examples
- Position as methodology, not product

**ICP-aligned examples:**
- Use examples from ICP domains (B2B SaaS, creator tools, fintech)
- Avoid circular self-references
- Multiple examples across different industries

---

## Voice Guidelines

**DO:**
- Use specific BUILD + RUN terminology
- Challenge industry hype (5-10x AI claims)
- Include GCC market context where relevant
- Lead with demonstrable proof

**DON'T:**
- Use marketing buzzwords
- Include hard CTAs ("Book a demo now!")
- Add engagement bait ("What do you think? Comment below!")
- Oversimplify technical concepts

---

## SEO Requirements (if primary publication)

- **H1:** Primary keyword naturally integrated
- **H2s:** Include keyword variations
- **First 100 words:** Mention primary keyword organically
- **Internal links:** 3-5 to related content (when exists)
- **Meta description:** 160 chars with keyword + value prop
- **Images:** Architecture diagrams with descriptive alt text

---

## Success Metrics

**Engagement:**
- >3 min average time on page (depth, not clickbait)
- High scroll depth (readers finish article)

**Conversions:**
- 3-5% demo requests from organic traffic
- Qualified inquiries (technical founders, budget-qualified)

**Attribution:**
- Which articles drive pipeline
- Which examples resonate most

---

**Last updated:** 2025-11-21
**Used by:** content-generation skill
```


<!-- FILE: content-generation/references/twitter-thread-pattern.md -->

# content-generation/references/twitter-thread-pattern.md

```markdown
# Twitter Thread Pattern

**Format:** Short-form thread (10-15 tweets max)
**Tone:** Punchy, direct, proof-driven
**Purpose:** Drive traffic to detailed content, build technical credibility

---

## Structure Template

```
🧵 Tweet 1 (Hook):
[Compelling claim or question that makes them stop scrolling]

[Key stat or insight that makes them want to read more]

2/ [Context - what problem are we solving?]

3/ [Key Insight #1 - most important takeaway]

4/ [Key Insight #2 - second most important]

5/ [Key Insight #3 - third most important]

6/ [Proof point - real numbers, real example]

7/ [Reality check - what can go wrong]

8/ [Actionable takeaway - what reader should do]

9/ [CTA - link to full article]

Full breakdown (7,000 words):
[Substack/blog link]

Repository:
[GitHub link]

10/ [Engagement prompt - only if natural]

What's your experience with [topic]?

Reply below 👇
```

---

## Content Requirements

**NO "About me" section:**
- Twitter bio already shows background
- Keep thread focused on content
- Platform-inappropriate to duplicate bio

**One idea per tweet:**
- Each tweet stands alone
- 280 characters max
- Clear, punchy statements

**Thread flow:**
- Hook → Context → Insights → Proof → Reality → Action → CTA
- Natural progression (each tweet leads to next)
- No forced engagement bait

---

## Hook Patterns (Tweet 1)

**Data-driven hook:**
```
🧵 Built LeanOS in 2 weeks.

Uses it to operate 2 companies simultaneously.

Here's the architecture:
```

**Contrarian hook:**
```
🧵 5-10x AI productivity claims aren't validated.

Here's what actually works (with proof):
```

**Proof-first hook:**
```
🧵 $200/month AI costs vs $200k team.

How 2 people operate like 10:
```

**Problem-focused hook:**
```
🧵 Most fractional CTOs advise-only.
Development agencies build-only.

You need BUILD + RUN.

Here's how:
```

---

## Tweet Length Guidelines

**Tweet 1 (Hook):**
- 2-3 short sentences
- Include thread emoji (🧵)
- End with intrigue (makes them read tweet 2)

**Tweets 2-8 (Body):**
- Start with number (2/, 3/, 4/)
- 1-2 sentences per tweet
- Scannable, punchy

**Tweet 9 (CTA):**
- Link to full content
- Repository link if applicable
- Clear action

**Tweet 10 (Engagement - optional):**
- Natural question
- Relates to thread topic
- Not forced

---

## Voice Guidelines

**DO:**
- Use BUILD + RUN terminology
- Include technical depth signals
- Challenge industry hype
- Real numbers from production

**DON'T:**
- Add "About me" tweets (bio already visible)
- Use buzzwords or hype language
- Force engagement ("Agree? RT!")
- Make unvalidated claims

---

## Proof Points (Always Include)

**Real metrics:**
- "$200/month AI costs, operates 2 companies"
- "2-person → 10-person velocity"
- "Built in 2 weeks, refined 18 months in production"

**Customer examples (if applicable):**
- "47 loans funded, $2.8M volume, 90 days"
- "Sarah + Chris (2 people) operate like 8-person team"

**Technical validation:**
- "Category-theoretic system design"
- "11 Skills orchestrating autonomously"
- "Open-source: github.com/BellaBe/lean-os"

---

## CTA Guidelines (Tweet 9)

**Simple CTA (prefer):**
```
9/ Full breakdown (7,000 words):
[Link]

Repository:
[GitHub link]
```

**Series navigation CTA:**
```
9/ Part 2 of LeanOS series:
[Link to full article]

Part 3 coming: 6-stage causal flow deep dive
```

**NO hard CTAs:**
- ❌ "Book a demo now!"
- ❌ "Limited slots DM me!"
- ❌ "Click here to learn more!"

---

## Engagement Tweet (Tweet 10 - Optional)

**Only if natural:**
```
10/ Building with AI agents?

Curious if this approach resonates.

What's your experience?
```

**Technical discussion:**
```
10/ Engineers: how do you approach AI orchestration?

Interested in different patterns.
```

**Never forced:**
- ❌ "Agree or disagree?"
- ❌ "What do you think? 👇"
- ❌ "RT if this helped!"

---

## Example Thread: Part 2 LeanOS

```
🧵 Part 2 of the LeanOS series is live.

10 specialized AI agents explained through one example: FastCapital (digital lending).

Why specialized > generalized:

2/ Context-shaping beats generalization.

Each agent optimized for specific decision types.

Event-driven coordination (agents invoke each other based on state changes).

3/ FastCapital: Sarah (fintech PM, non-dev) + Chris (engineer)

Week 1: Chris onboards in 4 hours via Canvas
Week 2: Platform built
Week 3: First loan funded

90 days: 47 loans, $2.8M volume, $60k revenue

4/ 2 people operate like 8-person team.

Sarah: 8 hrs/week (business ops)
Chris: 10 hrs/week (engineering)

Not theory. Production metrics.

5/ The 10 agents in 5 layers:

- Strategy & Foundation (4 agents)
- Sales Execution (1 orchestrator)
- Marketing Execution (1 orchestrator)
- Orchestration & Operations (2 agents)
- Engineering (2 agents)

6/ Reality check:

Claude might hallucinate.
Your co-founder might not get it.
The market might not cooperate.

LeanOS doesn't guarantee success.
It guarantees fast learning.

7/ Full article covers:

- All 10 agents with FastCapital examples
- How Sarah + Chris divide responsibilities
- What can go wrong
- Validation-driven approach

8/ You control orchestration.

Skills require learning (not plug-and-play).
Direct access enables shaping.
Few layers = less noise.
Open-source = no vendor lock-in.

9/ Full breakdown (7,000 words):
[Link to Substack article]

Repository:
https://github.com/BellaBe/lean-os

Part 3 coming soon: 6-stage causal flow deep dive

10/ Building with AI agents?

This might show you different patterns.

Questions? Reply below 👇
```

---

## Threading Best Practices

**Number every tweet after the first:**
- Tweet 1: Hook (with 🧵)
- Tweets 2-10: Numbered (2/, 3/, 4/)
- Makes thread easy to follow

**One tweet = one idea:**
- Don't cram multiple points
- Each tweet should be quotable standalone
- Natural breaks between concepts

**Link in final CTA tweet:**
- Don't include links mid-thread (breaks flow)
- Save links for tweet 9 (CTA)
- Repository + article links together

---

## Timing & Distribution

**Publish alongside main article:**
- Same day as Substack/blog
- Thread summarizes key insights
- Drives traffic to detailed content

**Don't publish standalone:**
- Always link to longer content
- Thread = teaser, article = depth
- Twitter amplifies, article converts

---

## Success Metrics

**Engagement:**
- ≥50 likes on thread starter (baseline)
- ≥5 retweets (resonates enough to amplify)
- ≥3 replies with substantive questions

**Click-through:**
- Click-through rate to main article
- Repository visits from Twitter traffic

**Lead quality:**
- Technical DMs (implementation questions)
- Profile clicks from target segments

---

**Last updated:** 2025-11-21
**Used by:** content-generation skill
```


<!-- FILE: content-strategy/SKILL.md -->

# content-strategy/SKILL.md

```markdown
---
name: content-strategy
description: Identify marketing campaign opportunities by scanning completed business/sales threads for learning worth sharing. Suggests campaign goals, content plans, and expected impact for human approval to create campaign threads.
allowed-tools: "Read,Write"
---

# Content Strategy: Campaign Opportunity Identification

**Campaign Framework:** `{skillDir}/references/campaign-framework.md`

You scan completed threads to identify opportunities for marketing campaigns based on the campaign types and triggers defined in the framework above.

## Purpose

Thread learning → Campaign opportunities → Human creates campaign thread

**Core principle:** Campaign opportunities emerge from business events (sales readiness, product launches, strategic shifts), not arbitrary calendars.

---

## Input Sources

### Threads to Scan

**Sales threads (threads/sales/):**
- `6-learning.md` - Hypothesis validation, customer insights
- **Campaign trigger:** Segment ready for outreach (need awareness campaign)
- Look for: ICP validated, common objections, success patterns

**Business threads (threads/business/):**
- `6-learning.md` - Strategic insights, Canvas updates
- **Campaign trigger:** Strategic shift, market trend, competitive move
- Look for: Positioning changes, market insights, thought leadership opportunities

**Sales campaigns (threads/sales/campaigns/):**
- **Campaign trigger:** Segment complete (package learnings into content)
- Look for: Deal patterns, case study opportunities, validated messaging

### Marketing Context

**Content pillars (artifacts/marketing/narrative/content-pillars.md):**
- What themes to focus on
- Which segments to target

**SEO strategy (artifacts/marketing/narrative/seo-strategy.md):**
- Priority keywords
- Content gaps to fill

---

## Campaign Opportunity Detection

### Step 1: Scan for Business Events

**Scan criteria:**
- Sales threads: ICP validated, segment ready, deals closing
- Business threads: Strategic decisions, Canvas updates, market shifts
- Sales campaigns: Completed campaigns with learnings

**Read:**
```bash
threads/sales/*/6-learning.md
threads/business/*/6-learning.md
threads/sales/campaigns/*/6-learning.md
```

### Step 2: Identify Campaign Triggers

**Strong triggers (always suggest campaign):**
- **Segment ready:** ICP validated, prospects identified, need awareness
- **Product launch:** New feature/capability worth announcing
- **Strategic pivot:** Canvas positioning changed, market needs education
- **Deal patterns:** ≥3 deals closed with similar learnings (case study opportunity)
- **Market event:** Competitor move, industry trend, regulatory change

**Moderate triggers (suggest if multiple present):**
- Single deal success (wait for pattern)
- Partial ICP validation (wait for more data)
- Internal improvement (not customer-facing)

**Not campaign-worthy:**
- Failed experiments without insights
- Proprietary/confidential information
- Process improvements (internal only)

### Step 3: Determine Campaign Type

**Reference:** See `{skillDir}/references/campaign-framework.md` for complete campaign type definitions, workflows, and examples.

**Match business event to campaign type (quick reference):**

**1. Awareness Campaign** (segment ready):
- Trigger: Sales segment validated, prospects identified
- Goal: Generate inbound demos (organic discovery)
- Content: Educational articles on problems (SEO-focused)
- Example: "DTC segment ready → Awareness campaign on fit problems"

**2. Education Campaign** (thought leadership):
- Trigger: Strategic insight, market trend, competitive gap
- Goal: Build authority, shift market thinking
- Content: Deep technical analysis, original research
- Example: "Body shape > measurements insight → Education campaign"

**3. Launch Campaign** (product announcement):
- Trigger: New feature, capability, integration
- Goal: Existing customer adoption + new customer awareness
- Content: Feature announcement, use cases, migration guides
- Example: "White-label SDK launched → Launch campaign"

**4. Validation Campaign** (case studies):
- Trigger: ≥3 deals closed with quantified results
- Goal: Prove value, overcome objections, close pipeline
- Content: Customer success stories, metrics, testimonials
- Example: "5 luxury brands → 38% return reduction → Case study campaign"

### Step 4: Calculate Campaign Impact

**Formula:**
```
Impact Score = (Reach × Conversion × Revenue) / 3

Reach (estimated traffic):
- 1.0: >5,000 sessions/month (high-volume SEO keywords)
- 0.7: 1,000-5,000 sessions/month
- 0.5: 500-1,000 sessions/month
- 0.3: <500 sessions/month

Conversion (demos/signups):
- 1.0: >2% conversion expected (strong buying intent keywords)
- 0.7: 1-2% conversion (education + buying intent)
- 0.5: 0.5-1% conversion (pure education)
- 0.3: <0.5% conversion (awareness only)

Revenue Impact:
- 1.0: Directly supports active sales campaign (immediate pipeline)
- 0.7: Supports segment with ready prospects (near-term pipeline)
- 0.5: Evergreen (continuous pipeline)
- 0.3: Speculative (future pipeline)
```

**Impact thresholds:**
- ≥ 0.75: High (flag immediately)
- 0.60-0.75: Medium (suggest if resources available)
- < 0.60: Low (defer unless strategic)

### Step 5: Plan Campaign Content

**Based on campaign type, suggest content pieces:**

**Awareness Campaign:**
- 3-5 blog articles (800-1,200w each)
- 6-10 LinkedIn posts (excerpts, amplification)
- SEO focus: Problem keywords (top-of-funnel)
- Timeline: 2-3 weeks

**Education Campaign:**
- 2-3 deep-dive articles (1,500-2,500w)
- 4-6 LinkedIn posts (technical audience)
- SEO focus: Solution keywords (mid-funnel)
- Timeline: 3-4 weeks

**Launch Campaign:**
- 1 announcement post (website + blog)
- 3-5 LinkedIn posts (feature highlights)
- 1 email (existing customers)
- Timeline: 1 week

**Validation Campaign:**
- 1-2 case studies (1,200-1,800w)
- 2-4 LinkedIn posts (results-focused)
- 1 email (pipeline nurture)
- Timeline: 2 weeks

**Implementation guide** (if):
- Technical how-to
- Step-by-step process
- Tactical advice

**Industry analysis** (if):
- Market trend observation
- Data across multiple sources
- Strategic implications

**Product announcement** (if):
- New feature launch
- Capability expansion
- Technical innovation

**Thought leadership** (if):
- Contrarian insight
- Original research
- Non-obvious conclusion

---

## Output Format

### Campaign Opportunity Record

**Internal file (for tracking):**
```yaml
# campaign-opportunity-{date}-{slug}.yaml

campaign_name: "Luxury White-Label Validation Campaign"
campaign_slug: "luxury-validation-nov-2024"
campaign_type: "validation"  # awareness, education, launch, validation

trigger_event: "5 luxury brands chose white-label (100% pattern)"
source_threads:
  - "threads/sales/elsa-white-label/6-learning.md"
  - "threads/sales/luxury-brand-2/6-learning.md"
  - "threads/sales/luxury-brand-3/6-learning.md"

business_goal: "Generate 20 qualified demos from organic discovery"
target_segment: "luxury-brands"

campaign_hypothesis: "Validation campaigns (case studies) convert better than awareness content"
canvas_link: "10-assumptions.md → H1 (campaign performance)"

impact_score: 0.85
impact_breakdown:
  reach: 0.8           # 1,000-5,000 sessions/month
  conversion: 0.9      # 1-2% conversion (strong proof)
  revenue: 1.0         # Directly supports active luxury segment

estimated_results:
  target_sessions: "2,000/month"
  target_demos: "20/month"
  target_pipeline: "$10M influenced"
  timeline: "2 weeks to create, 30 days to measure"

content_plan:
  - type: "case study"
    title: "ElsaAI Reduces Returns 38% with White-Label SDK"
    keyword: "white-label SDK"
    channel: ["blog", "linkedin"]
  - type: "case study"
    title: "How Luxury Brands Achieve Fit Accuracy"
    keyword: "luxury fashion fit"
    channel: ["blog"]
  - type: "linkedin post"
    title: "Key stat: 38% return reduction"
    channel: ["linkedin"]
  - type: "linkedin post"
    title: "Customer quote from ElsaAI"
    channel: ["linkedin"]

next_steps:
  - "Flag in ops/today.md for human approval"
  - "If approved: Human creates campaign thread at threads/marketing/campaigns/luxury-validation-nov-2024/"
  - "Then: marketing-execution executes Stage 5"

created: "2024-11-16"
status: "pending_approval"
```

### Human-Facing Output (ops/today.md)

**Format for flagging in ops/today.md:**
```markdown
## Campaign Opportunities (Detected This Week)

### High Impact (≥0.75)

1. **[Impact: 0.85] Luxury White-Label Validation Campaign**
   - Type: Validation (case studies + proof)
   - Trigger: 5 luxury brands chose white-label (100% pattern)
   - Goal: 20 demos from organic (2,000 sessions target)
   - Content: 2 case studies + 4 LinkedIn posts
   - Timeline: 2 weeks to create, 30 days to measure
   - Expected ROI: $10M pipeline influenced
   - Action: Create campaign thread at threads/marketing/campaigns/luxury-validation-nov-2024/?

2. **[Impact: 0.78] DTC Awareness Campaign**
   - Type: Awareness (educational content)
   - Trigger: DTC segment ready (ICP validated, 191 prospects identified)
   - Goal: 25 demos from organic (3,000 sessions target)
   - Content: 3 blog articles + 6 LinkedIn posts
   - Timeline: 3 weeks to create, 60 days to measure
   - Expected ROI: $12.5M pipeline influenced
   - Action: Create campaign thread at threads/marketing/campaigns/dtc-awareness-nov-2024/?

### Medium Impact (0.60-0.75)

3. **[Impact: 0.68] Product Launch Campaign**
   - Type: Launch (announcement + guides)
   - Trigger: Color analysis feature launching
   - Goal: 10 demos + 50 existing customer adoptions
   - Content: 1 announcement + 3 LinkedIn posts + 1 email
   - Timeline: 1 week to create, 14 days to measure
   - Expected ROI: $5M pipeline + retention improvement
   - Action: Defer until feature launch confirmed?

### Low Priority (<0.60)

4. **[0.42] Technical: API Rate Limiting Best Practices**
   - Source: engineering/services/api/rate-limit-update.md
   - Pillar: None (orphan)
   - Keyword: Low search volume
   - Impact: Minimal
   - Action: Skip or create as technical doc (not marketing)
```

---

## Role in Execution Flow

**content-strategy is a DETECTION tool, not an EXECUTION tool.**

### What content-strategy DOES:

✅ **Daily automated scan**
   - Scans: `threads/*/6-learning.md` files
   - Looks for: Business events triggering campaign opportunities
   - Matches: Learning to campaign types (awareness, education, launch, validation)

✅ **Calculate campaign impact**
   - Score: Reach × Conversion × Revenue
   - Threshold: ≥0.75 for high impact

✅ **Generate campaign suggestions**
   - Suggests: Campaign name, type, goal, content plan
   - Saves: `campaign-opportunity-{date}-{slug}.yaml` (internal tracking)
   - Flags: High-impact opportunities in `ops/today.md`

✅ **Wait for human decision**
   - Human reviews in `ops/today.md`
   - Human decides: Create campaign or defer

### What content-strategy DOES NOT DO:

❌ **Does NOT create campaign threads** - Human creates thread manually
❌ **Does NOT execute campaigns** - marketing-execution handles execution
❌ **Does NOT create content** - content-generation handles drafts
❌ **Does NOT publish content** - content-distribution handles publishing

### Execution Flow:

```
content-strategy (daily scan)
    ↓
Detects business event → Suggests campaign
    ↓
Flags in ops/today.md: "Create campaign thread at threads/marketing/campaigns/{slug}/?"
    ↓
Human reviews → Approves
    ↓
Human manually creates campaign thread (Stages 1-4)
    ↓
marketing-execution reads Stage 4 decision
    ↓
marketing-execution orchestrates execution (Stage 5)
    ↓
content-generation → seo-optimization → content-distribution
    ↓
performance-tracking monitors (Stage 6 support)
    ↓
Human completes Stage 6 (Learning)
```

### Key Principle:

**content-strategy suggests campaigns, humans create threads, marketing-execution executes.**

This separation ensures:
- Human approves campaign strategy (Stages 1-4)
- AI executes tactical work (Stage 5)
- Human validates results (Stage 6)

---

## Automation Rules

### Auto-Scan Triggers

**Daily scan (automated):**
- Check threads updated in last 24 hours
- Generate new opportunities
- Update ops/today.md

**On-demand scan:**
- Human requests: "Scan for content opportunities"
- Check all threads updated in last 30 days
- Generate comprehensive report

### Auto-Flagging Rules

**Flag in ops/today.md if:**
- Priority ≥ 0.7 (high priority)
- OR keyword is top 10 priority from seo-strategy.md
- OR thread explicitly mentions "worth sharing publicly"

**Add to backlog if:**
- Priority 0.5-0.7 (medium)
- Keyword has SEO potential
- Content aligns with pillar

**Skip if:**
- Priority < 0.5 (low)
- Confidential/proprietary learning
- No pillar match and no strategic value

---

## Quality Checks

**Before flagging opportunity:**

- [ ] Learning is validated (not hypothesis)
- [ ] Maps to content pillar (or flags orphan)
- [ ] Priority score calculated with reasoning
- [ ] Target keyword identified
- [ ] Content type appropriate for learning
- [ ] Estimated impact has reasoning
- [ ] No confidential information included

---

## Edge Cases

**Multiple threads with same learning:**
- Combine into single opportunity
- Note: "Pattern across N threads"
- Higher confidence score

**Orphan learning (no pillar match):**
- Flag separately
- Recommend: Add pillar or skip content

**Confidential customer data:**
- Anonymize before content creation
- Or: Skip if cannot anonymize

**Learning contradicts previous content:**
- Flag for review
- May need to update existing content
- Higher priority (correct misinformation)

---

## Success Metrics

**Opportunity identification:**
- Opportunities flagged: {count} per week
- High-priority hit rate: {percent} approved by human
- Conversion rate: {percent} flagged → published

**Content-pillar coverage:**
- Pillar 1: {count} opportunities
- Pillar 2: {count} opportunities
- Pillar 3: {count} opportunities
- Orphans: {count} (indicates pillar gaps)

**Business impact:**
- Content from opportunities: {percent} of total traffic
- Demo requests from opportunity-driven content: {count}

---

## Usage Example

**Scenario:** ElsaAI deal closes
```
1. Thread completes: threads/sales/elsa-white-label/6-learning.md
   
2. content-strategy scans learning:
   - Validated: "Luxury brands prefer white-label (N=5)"
   - Impact: 0.9 (affects enterprise segment)
   - Confidence: 1.0 (5 data points)
   - Timeliness: 0.8 (recent, relevant)
   - SEO: 0.7 ("white-label SDK" medium priority)
   - Priority: 0.85 (HIGH)

3. Match to pillar:
   - Pillar: "Product capabilities"
   - Content type: Case study

4. Generate opportunity record:
   - Save: content-opportunity-2024-11-16-white-label-case-study.yaml

5. Flag in ops/today.md:
   "[0.85] Case Study: Enterprise White-Label Success"

6. Wait for human approval

7. If approved:
   - Pass opportunity to content-generation subskill
   - Generate draft case study
```

---

## Remember

**Content strategy is:**
- Detecting valuable learning in completed threads
- Matching insights to content pillars and keywords
- Calculating objective priority scores
- Flagging high-value opportunities for human decision

**Content strategy is NOT:**
- Creating arbitrary "content calendar" quotas
- Forcing content when no learning exists
- Publishing every minor insight
- Deciding to publish (human approves)

**Success = Right opportunities flagged at right time.**
```


<!-- FILE: content-strategy/references/campaign-framework.md -->

# content-strategy/references/campaign-framework.md

```markdown
# Marketing Campaign Workflow

## Overview

All marketing content is created as part of campaigns. Campaigns follow 6-stage causal-flow and are decision threads in `threads/marketing/campaigns/`.

## Directory Structure

```
threads/marketing/campaigns/{campaign-slug}/
├── metadata.yaml
├── 1-input.md        # Business event triggering campaign
├── 2-hypothesis.md   # What we believe (Canvas link)
├── 3-implication.md  # Business impact (sessions → demos → revenue)
├── 4-decision.md     # Content plan (what to produce)
├── 5-actions/
│   ├── execution-log.md  # Track content creation/publishing
│   └── drafts/  (temp, deleted after publishing)
└── 6-learning.md     # Results + Canvas updates

artifacts/marketing/campaigns/{campaign-slug}/
├── blog/
├── linkedin/
├── email/
└── distribution-record.yaml
```

## Campaign Types

### 1. Awareness Campaign
**Trigger:** Sales segment validated, prospects identified
**Goal:** Generate inbound demos via organic discovery
**Content:** 3-5 educational blog articles + 6-10 LinkedIn posts
**Timeline:** 2-3 weeks
**Example:** DTC segment ready → Create awareness campaign on fit problems

### 2. Education Campaign
**Trigger:** Strategic insight, market trend, thought leadership opportunity
**Goal:** Build authority, shift market thinking
**Content:** 2-3 deep-dive articles + 4-6 LinkedIn posts
**Timeline:** 3-4 weeks
**Example:** Body shape insight → Education campaign challenging conventional wisdom

### 3. Launch Campaign
**Trigger:** New feature, capability, integration
**Goal:** Customer adoption + new customer awareness
**Content:** 1 announcement + 3-5 LinkedIn posts + 1 email
**Timeline:** 1 week
**Example:** White-label SDK launched → Launch campaign

### 4. Validation Campaign
**Trigger:** ≥3 deals closed with quantified results
**Goal:** Prove value, overcome objections
**Content:** 1-2 case studies + 2-4 LinkedIn posts + 1 email
**Timeline:** 2 weeks
**Example:** 5 luxury brands achieved 38% return reduction → Case study campaign

## Workflow

### Stage 1-4: Planning (Human)

1. **content-strategy scans threads** → Detects campaign opportunity → Flags in ops/today.md
2. **Human reviews** → Decides to create campaign
3. **Human creates campaign thread** → Completes Stages 1-4
   - Stage 1: Document trigger event
   - Stage 2: Link to Canvas hypothesis
   - Stage 3: Calculate impact (sessions → demos → revenue)
   - Stage 4: Define content plan (specific articles, posts, emails)

### Stage 5: Execution (AI-Assisted)

1. **marketing-execution orchestrator** reads Stage 4 decision
2. For each content piece:
   - **content-generation:** Create draft → Save to `5-actions/drafts/`
   - **Human review:** Approve or request changes
   - **seo-optimization:** Apply keywords, structure
   - **Human approve:** Final check
   - **content-distribution:** Publish to `artifacts/marketing/campaigns/{slug}/`
   - **Update execution-log.md:** Track progress
3. After all published: Delete `drafts/` (content now in artifacts)

### Stage 6: Learning (AI + Human)

1. **performance-tracking** monitors campaign metrics
2. **Human writes learning:**
   - What worked, what didn't
   - Canvas updates (validate/invalidate hypothesis)
   - Next campaign opportunities
3. Campaign complete

## Campaign Naming

Use descriptive format: `{segment}-{purpose}-{month-year}`

**Examples:**
- `dtc-awareness-nov-2024`
- `luxury-validation-dec-2024`
- `tech-education-jan-2025`

## Opportunity Detection

**content-strategy** scans daily:
- `threads/business/*/6-learning.md` - Strategic decisions, market shifts
- `threads/sales/*/6-learning.md` - Segment ready, deal patterns
- `threads/sales/campaigns/*/6-learning.md` - Outreach learnings

**Flags in ops/today.md:**
```markdown
## Campaign Opportunities

1. [Impact: 0.85] DTC Product Awareness Campaign
   - Trigger: DTC segment ready (ICP validated, 191 prospects)
   - Type: Awareness
   - Content: 3 articles on fit problems + 6 LinkedIn posts
   - Goal: 20 demos from organic (1% conversion)
   - Timeline: 2-3 weeks
   - Action: Create campaign thread?
```

## Key Principles

✅ **All content is part of a campaign** - No standalone content
✅ **Campaigns are decision threads** - Follow 6-stage causal-flow
✅ **Stage 4 decides content** - List specific pieces to produce
✅ **Stage 5 tracks execution** - execution-log.md shows progress
✅ **Stage 6 measures impact** - Validate hypothesis, update Canvas
✅ **Drafts are temporary** - Live in thread during execution, deleted after publishing
✅ **Artifacts are permanent** - Published content grouped by campaign

## Current State

**Existing content** (created before campaign structure):
- artifacts/marketing/blog/ (3 posts)
- artifacts/marketing/linkedin/posts/ (11 posts)
- artifacts/marketing/email/ (3 emails)
- artifacts/marketing/narrative/ (strategy files)

**Next step:** Create first campaign, reposition existing content into campaign structure.

## Related Skills

- **marketing-execution** - Orchestrates campaign execution (Stage 5)
- **content-strategy** - Detects campaign opportunities
- **content-generation** - Creates content drafts
- **seo-optimization** - Applies SEO to content
- **content-distribution** - Publishes to channels
- **performance-tracking** - Measures campaign results
```


<!-- FILE: performance-tracking/SKILL.md -->

# performance-tracking/SKILL.md

```markdown
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
```


<!-- FILE: seo-optimization/SKILL.md -->

# seo-optimization/SKILL.md

```markdown
---
name: seo-optimization
description: Optimize content drafts for search engines while maintaining educational quality. Applies target keywords naturally, structures content with proper H1/H2 hierarchy, adds meta descriptions, suggests internal links, and ensures technical SEO requirements met without keyword stuffing.
allowed-tools: "Read,Write"
---

# SEO Optimization

You optimize content for organic discovery without sacrificing quality.

## Purpose

Draft content + Target keyword → SEO-optimized content

**Core principle:** Optimize for discovery, not at the expense of educational value.

---

## Input Requirements

### Required Inputs

**1. Draft content:**
```
threads/marketing/campaigns/{campaign-slug}/5-actions/drafts/{piece}-draft.md
```

**2. SEO strategy:**
```
artifacts/marketing/narrative/seo-strategy.md
```

**3. Target keyword (from content opportunity):**
```
Primary: "white-label SDK"
Secondary: ["enterprise fashion SDK", "branded fit recommendation"]
```

---

## Optimization Process

### Step 1: Analyze Current State

**Read draft content:**
- Extract title, headings (H1, H2, H3)
- Count word length
- Identify keyword mentions (current)
- Note structure and sections

**Load SEO strategy:**
- Primary keyword details
- Secondary keyword opportunities
- Funnel stage (TOFU/MOFU/BOFU)
- Competitive content (if available)

### Step 2: Title Optimization

**Current title analysis:**
- Does it contain primary keyword?
- Is it 50-60 characters (optimal for SERP)?
- Is it compelling (not just keyword stuffed)?

**Optimization rules:**
```
✓ Include primary keyword naturally
✓ 50-60 characters (SERP display limit)
✓ Front-load keyword if possible
✓ Remain compelling and specific
✗ Don't keyword stuff
✗ Don't sacrifice clarity for SEO
```

**Examples:**

**Before (not optimized):**
```
"Our Customer Success Story with ElsaAI"
```

**After (optimized):**
```
"White-Label SDK Case Study: ElsaAI Reduces Returns 38%"
- Keyword: ✓ (white-label SDK)
- Length: ✓ (55 characters)
- Compelling: ✓ (specific result)
```

**Before (keyword stuffed):**
```
"White-Label SDK for White-Label Fashion White-Label Solutions"
```

**After (natural):**
```
"How Enterprise Fashion Brands Use White-Label SDKs"
- Keyword: ✓ (white-label SDK)
- Natural: ✓ (readable, not spammy)
- Secondary keyword: ✓ (enterprise fashion)
```

### Step 3: Meta Description

**Create meta description (150-160 characters):**

**Rules:**
```
✓ 150-160 characters (SERP display)
✓ Include primary keyword
✓ Compelling summary (drives clicks)
✓ Include benefit or result
✗ Don't repeat title exactly
✗ Don't keyword stuff
```

**Template:**
```
"{Specific result or benefit} {with/using} {keyword}. {Supporting detail or proof point}."
```

**Example:**
```
Draft title: "White-Label SDK Case Study: ElsaAI Reduces Returns 38%"

Meta description:
"Learn how ElsaAI reduced fashion returns by 38% using a white-label SDK. Implementation guide, metrics, and ROI analysis from a $200M luxury marketplace."

- Length: 158 characters ✓
- Keyword: ✓ (white-label SDK)
- Compelling: ✓ (specific metrics, actionable)
```

### Step 4: Heading Structure (H1, H2, H3)

**H1 (Title):**
- Should be title (already optimized in Step 2)
- One H1 per page
- Contains primary keyword

**H2 (Main sections):**
- Descriptive, not clever
- Include keyword variations naturally
- 3-7 H2s per article (depends on length)

**H3 (Subsections):**
- Support H2s
- Use related terms (LSI keywords)
- Optional: Include long-tail keywords

**Example structure:**

**Before (generic):**
```
H1: ElsaAI Case Study
H2: The Problem
H2: The Solution
H2: The Results
```

**After (SEO-optimized):**
```
H1: White-Label SDK Case Study: ElsaAI Reduces Returns 38%
H2: Why Luxury Fashion Brands Need White-Label Fit Recommendations
H2: Implementing a White-Label SDK: Technical Approach
H2: Results: 38% Return Reduction in 30 Days
H2: White-Label vs Co-Branded: Enterprise SDK Comparison
```

**Keyword distribution:**
- H1: Primary keyword ✓
- H2 #1: Keyword variation (white-label fit recommendations) ✓
- H2 #2: Primary keyword (white-label SDK) ✓
- H2 #4: Keyword variation (white-label vs co-branded) ✓

### Step 5: Keyword Integration

**Primary keyword placement:**

**Required:**
- [ ] H1 (title)
- [ ] First 100 words (natural mention)
- [ ] At least 2 H2 subheadings
- [ ] Meta description
- [ ] URL slug

**Optional (if natural):**
- Body paragraphs (2-4 times per 1,000 words)
- Image alt text
- Conclusion

**Keyword density target:**
- 0.5-2% of total words
- Example: 1,500-word article = 7-30 mentions
- Natural distribution (not clustered)

**Example integration:**

**First 100 words:**
```
When we launched our fit recommendation SDK, we assumed enterprise 
brands would prefer co-branded widgets. After 5 enterprise deals, 
we learned we were wrong.

100% of luxury brands chose white-label SDK integration. This wasn't 
about hiding technology—it was about brand consistency being 
non-negotiable in luxury e-commerce.

Here's what we learned from $5.5M in enterprise contracts about 
white-label SDKs and brand positioning.
```

**Keyword mentions:**
- "white-label SDK" (sentence 2) ✓
- "white-label SDK integration" (sentence 2) ✓
- "white-label SDKs" (sentence 3) ✓
- Density: 3 mentions / 85 words = 3.5% (acceptable for intro)

**Secondary keywords:**
- "enterprise brands" ✓
- "luxury brands" ✓
- "fit recommendation" ✓

### Step 6: Internal Linking

**Strategy:**
- 3-5 internal links per article
- Link to related content (same pillar or related pillars)
- Use descriptive anchor text (not "click here")
- Link to high-value pages (product pages, popular articles)

**Internal link opportunities:**

**Identify linkable phrases:**
```
In draft:
"Luxury fashion brands face 25-30% return rates due to fit issues."

Link opportunity:
"Luxury fashion brands face 25-30% return rates due to [fit issues](link-to-article-on-fit-problems)."
```

**Anchor text rules:**
```
✓ Descriptive (tells reader what they'll find)
✓ Natural in context
✓ Keyword-relevant (helps SEO)
✗ Generic ("click here", "learn more")
✗ Overly optimized ("best white-label SDK solutions")
```

**Example internal links:**
```markdown
## Why Luxury Fashion Brands Need White-Label Fit Recommendations

Luxury customers expect seamless brand experiences. When ElsaAI 
first implemented [co-branded fit widgets](/blog/co-branded-vs-white-label), 
customer feedback was negative:

Their previous approach to [reducing fashion returns](/blog/reduce-returns-guide) 
used generic size charts with 68% accuracy...

For more on [enterprise SDK pricing](/pricing/enterprise), see our 
technical documentation.
```

**Links added:**
1. `/blog/co-branded-vs-white-label` (related topic, same pillar)
2. `/blog/reduce-returns-guide` (different pillar, high-value content)
3. `/pricing/enterprise` (product page, conversion-focused)

### Step 7: Image Optimization

**For each image in content:**

**Alt text:**
- Descriptive (what's in the image)
- Include keyword if natural
- 125 characters max
- Not keyword-stuffed

**Example:**
```
Image: Screenshot of white-label SDK integration

✗ Bad alt text: "image1.png"
✗ Bad alt text: "white-label SDK white-label integration white-label"
✓ Good alt text: "White-label SDK integration showing branded fit recommendation widget in ElsaAI's checkout flow"
```

**File naming:**
```
✗ IMG_1234.jpg
✓ white-label-sdk-integration-screenshot.jpg
```

**File size:**
- Compress images <200KB
- Use WebP format if possible
- Lazy loading for below-fold images

### Step 8: URL Slug

**Create SEO-friendly URL:**

**Rules:**
```
✓ Include primary keyword
✓ Use hyphens (not underscores)
✓ Lowercase only
✓ Short (3-5 words ideal)
✓ Descriptive of content
✗ No stop words (a, the, and, or)
✗ No special characters
✗ No dates (unless time-sensitive)
```

**Examples:**

**From title:** "White-Label SDK Case Study: ElsaAI Reduces Returns 38%"
```
✗ white-label-sdk-case-study-elsaai-reduces-returns-38-percent
   (too long, includes stop words)

✓ white-label-sdk-case-study
   (concise, keyword-focused)

✓ elsaai-white-label-sdk
   (customer name + keyword)
```

### Step 9: Structured Data (Optional)

**For case studies and articles:**

**Add JSON-LD schema markup:**
```json
{
  "@context": "https://schema.org",
  "@type": "Article",
  "headline": "White-Label SDK Case Study: ElsaAI Reduces Returns 38%",
  "description": "Learn how ElsaAI reduced fashion returns by 38%...",
  "author": {
    "@type": "Organization",
    "name": "GlamYouUp"
  },
  "datePublished": "2024-11-16",
  "dateModified": "2024-11-16"
}
```

**For case studies specifically:**
```json
{
  "@context": "https://schema.org",
  "@type": "CaseStudy",
  "name": "ElsaAI White-Label SDK Implementation",
  "description": "How ElsaAI reduced returns by 38%...",
  "result": "38% reduction in return rate, $805K annual savings"
}
```

---

## Quality Validation

**Before outputting optimized content:**

### Keyword Optimization

- [ ] **Primary keyword in title:** Natural integration
- [ ] **Primary keyword in first 100 words:** Organic mention
- [ ] **Primary keyword in 2+ H2s:** Natural distribution
- [ ] **Keyword density 0.5-2%:** Not over-optimized
- [ ] **Secondary keywords included:** Natural variations

### Technical SEO

- [ ] **Title length 50-60 chars:** SERP-friendly
- [ ] **Meta description 150-160 chars:** Compelling, includes keyword
- [ ] **H1 unique:** Only one H1 (title)
- [ ] **H2 structure logical:** 3-7 main sections
- [ ] **URL slug optimized:** Keyword-focused, concise

### Content Quality

- [ ] **Readability maintained:** No keyword stuffing
- [ ] **Natural language:** SEO doesn't hurt readability
- [ ] **Educational value preserved:** Optimization adds, doesn't subtract
- [ ] **Internal links relevant:** 3-5 links, natural anchor text

### Image SEO

- [ ] **Alt text descriptive:** Includes keyword if natural
- [ ] **File names optimized:** Descriptive, keyword-relevant
- [ ] **File size <200KB:** Compressed for performance

---

## Output Format

### Optimized Content File
```markdown
---
# SEO Metadata
title: "White-Label SDK Case Study: ElsaAI Reduces Returns 38%"
meta_description: "Learn how ElsaAI reduced fashion returns by 38% using a white-label SDK. Implementation guide, metrics, and ROI analysis from a $200M luxury marketplace."
url_slug: "elsaai-white-label-sdk-case-study"
target_keyword: "white-label SDK"
secondary_keywords: ["enterprise fashion SDK", "white-label fit recommendation", "luxury fashion returns"]
canonical_url: "https://glamyouup.com/blog/elsaai-white-label-sdk-case-study"

# Content metadata
content_type: "case study"
pillar: "Product capabilities"
word_count: 1450
readability_score: "Grade 10"
keyword_density: "1.2%"

# SEO scores
title_score: "95/100"
meta_score: "90/100"
heading_score: "85/100"
keyword_score: "88/100"
internal_link_score: "90/100"

# Optimization notes
optimizations_applied:
  - "Added primary keyword to title"
  - "Optimized H2 headings with keyword variations"
  - "Added 4 internal links to related content"
  - "Created meta description with keyword and result"
  - "Optimized image alt text"

created: "2024-11-16"
status: "optimized"
---

# White-Label SDK Case Study: ElsaAI Reduces Returns 38%

{Optimized content with all SEO improvements applied}

---

## Internal Links Added

1. [co-branded vs white-label comparison](/blog/co-branded-vs-white-label)
   - Anchor: "co-branded fit widgets"
   - Context: Explaining ElsaAI's previous approach

2. [reducing fashion returns guide](/blog/reduce-returns-guide)
   - Anchor: "reducing fashion returns"
   - Context: Broader problem context

3. [enterprise SDK pricing](/pricing/enterprise)
   - Anchor: "enterprise SDK pricing"
   - Context: Call-out to product page

4. [luxury fashion e-commerce trends](/blog/luxury-ecommerce-trends)
   - Anchor: "luxury fashion brands"
   - Context: Industry background
```

### SEO Checklist Report
```markdown
## SEO Optimization Report

**Content:** elsaai-white-label-sdk-case-study.md
**Date:** 2024-11-16
**Target keyword:** white-label SDK

### Optimization Summary

**Title Optimization:**
- Original: "Our Customer Success Story with ElsaAI"
- Optimized: "White-Label SDK Case Study: ElsaAI Reduces Returns 38%"
- Score: 95/100 (keyword included, 55 chars, compelling)

**Meta Description:**
- Created: "Learn how ElsaAI reduced fashion returns by 38% using a white-label SDK. Implementation guide, metrics, and ROI analysis from a $200M luxury marketplace."
- Score: 90/100 (158 chars, keyword included, actionable)

**Heading Structure:**
- H1: 1 (title with keyword) ✓
- H2: 5 (3 include keyword variations) ✓
- H3: 8 (support H2s) ✓

**Keyword Integration:**
- Primary keyword mentions: 18 (1.2% density) ✓
- First 100 words: ✓
- H1: ✓
- H2s: 3/5 ✓
- Meta description: ✓

**Internal Links:**
- Total: 4 ✓
- Anchor text optimized: ✓
- Relevant targets: ✓

**Image Optimization:**
- Images: 3
- Alt text added: 3/3 ✓
- File names optimized: 3/3 ✓

**URL Slug:**
- Created: "elsaai-white-label-sdk-case-study"
- Keyword included: ✓
- Length: 4 words ✓

### Recommendations

1. **Consider adding:**
   - FAQ schema for common questions
   - Breadcrumb navigation
   - Related articles section

2. **Monitor performance:**
   - Track ranking for "white-label SDK"
   - Monitor click-through rate from SERP
   - Adjust if needed after 30 days

### Overall SEO Score: 89/100

**Ready for publication.**
```

---

## Edge Cases

### Low Keyword Opportunity

**If keyword search volume is low:**
- Optimize anyway (long-tail can convert well)
- Focus on related keywords
- Prioritize internal linking for authority

### Keyword Doesn't Fit Naturally

**If forcing keyword hurts readability:**
- Use keyword variations instead
- Prioritize quality over keyword placement
- Include keyword in meta/title only

### Existing Content Update

**If optimizing published content:**
- Preserve existing URL (avoid 301 redirects)
- Update modified date
- Add redirect if URL must change
- Monitor rankings after update

### Competitive Keyword

**If keyword highly competitive:**
- Focus on long-tail variations
- Build authority with internal links
- Create comprehensive content (longer, deeper)
- Consider secondary keywords

---

## Success Metrics

**Optimization quality:**
- SEO score: >85/100 (technical compliance)
- Readability maintained: No keyword stuffing
- Natural integration: Keywords flow organically

**Search performance (post-publication):**
- Ranking: Position 1-10 for target keyword (within 90 days)
- Click-through rate: >3% from SERP
- Organic traffic: {target sessions/month}

**Conversion performance:**
- Time on page: >3 minutes (engaging content)
- Scroll depth: >75% (readers finish article)
- Conversion rate: {demos/downloads per 100 visitors}

---

## Usage Example

**Input:**
```
Draft: threads/marketing/campaigns/luxury-validation-nov-2024/5-actions/drafts/elsaai-case-study/draft.md
Keyword: "white-label SDK"
Secondary: ["enterprise fashion SDK", "luxury fashion returns"]
```

**Process:**
```
1. Read draft:
   - Title: "Our Customer Success Story with ElsaAI"
   - Word count: 1,450
   - Current keyword mentions: 5 (sparse)

2. Optimize title:
   - New: "White-Label SDK Case Study: ElsaAI Reduces Returns 38%"
   - Keyword: ✓
   - Length: 55 chars ✓

3. Create meta description:
   - "Learn how ElsaAI reduced fashion returns by 38% using a white-label SDK..."
   - 158 chars ✓

4. Optimize headings:
   - H2: "Why Luxury Fashion Brands Need White-Label Fit Recommendations"
   - H2: "Implementing a White-Label SDK: Technical Approach"
   - Added keyword variations ✓

5. Add keywords naturally:
   - First 100 words: Added "white-label SDK" ✓
   - Body: 18 total mentions (1.2% density) ✓

6. Internal linking:
   - Added 4 links to related content ✓
   - Descriptive anchor text ✓

7. Image optimization:
   - Alt text: "White-label SDK integration showing branded fit widget"
   - File: white-label-sdk-screenshot.jpg ✓

8. URL slug:
   - Created: "elsaai-white-label-sdk-case-study" ✓

9. Validate:
   - SEO score: 89/100 ✓
   - Readability: Maintained ✓
   - Ready for publication ✓

10. Output:
    - Save: threads/marketing/campaigns/luxury-validation-nov-2024/5-actions/drafts/elsaai-case-study/optimized.md
    - Flag: ops/today.md for final approval
```

---

## Remember

**SEO optimization is:**
- Making great content discoverable
- Integrating keywords naturally
- Structuring content for search engines AND readers
- Building authority through internal linking

**SEO optimization is NOT:**
- Keyword stuffing
- Sacrificing readability for rankings
- Gaming search algorithms
- Over-optimizing at expense of quality

**Success = Content that ranks AND educates effectively.**
```

