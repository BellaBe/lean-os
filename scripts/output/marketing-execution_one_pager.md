================================================================================
Markdown Tree for: /home/bellabe/lean-os/.claude/skills/marketing-execution
================================================================================
marketing-execution/
├── content-distribution/
│   └── SKILL.md
├── content-generation/
│   ├── references/
│   │   ├── announcement-linkedin-pattern.md
│   │   ├── blog-patterns.md
│   │   ├── case-study-pattern.md
│   │   ├── email-patterns.md
│   │   └── pattern-principles.md
│   └── SKILL.md
├── performance-tracking/
│   └── SKILL.md
├── seo-optimization/
│   └── SKILL.md
└── SKILL.md

================================================================================
Concatenated Markdown From: /home/bellabe/lean-os/.claude/skills/marketing-execution
Total files: 10
================================================================================


<!-- FILE: SKILL.md -->

# SKILL.md

```markdown
---
name: marketing-execution
description: Orchestrates marketing campaign execution (Stage 5) following 6-stage causal-flow. Coordinates content-generation (drafts), seo-optimization (keywords), content-distribution (publishing), and performance-tracking (metrics) to execute approved campaign decisions.
allowed-tools: "Read,Write,Bash"
---

# Marketing Execution Orchestrator

You are a pure orchestrator. You coordinate subskills but do NOT generate, optimize, or publish content directly.

## Purpose

Execute Stage 5 of approved campaigns by orchestrating subskills to produce, publish, and measure content.

**Core principle:** You READ decisions, INVOKE subskills, TRACK progress. You do NOT do the work yourself.

---

## Available Subskills

**Execution pipeline (you orchestrate these):**
- `marketing-execution/content-generation` - Generate content drafts
- `marketing-execution/seo-optimization` - Apply SEO to content
- `marketing-execution/content-distribution` - Publish to channels
- `marketing-execution/performance-tracking` - Measure impact

**You coordinate these subskills. You do NOT perform their functions.**

---

## Your Orchestration Role

### What You DO:
✅ Read Stage 4 Decision (content plan)
✅ Invoke content-generation subskill
✅ Flag drafts for human review
✅ Invoke seo-optimization subskill
✅ Flag optimized content for human approval
✅ Invoke content-distribution subskill
✅ Update execution-log.md
✅ Invoke performance-tracking subskill
✅ Report progress in ops/today.md

### What You DON'T DO:
❌ Generate content yourself (content-generation does this)
❌ Optimize SEO yourself (seo-optimization does this)
❌ Publish content yourself (content-distribution does this)
❌ Track metrics yourself (performance-tracking does this)

---

## Campaign Structure

```
threads/marketing/campaigns/{campaign-slug}/
├── metadata.yaml
├── 1-input.md        # Trigger
├── 2-hypothesis.md   # Canvas link
├── 3-implication.md  # Business impact
├── 4-decision.md     # Content plan (YOU READ THIS)
├── 5-actions/
│   ├── execution-log.md  # YOU UPDATE THIS
│   └── drafts/           # Temporary (YOU MANAGE DELETION)
└── 6-learning.md     # Human writes (with metrics from performance-tracking)

artifacts/marketing/campaigns/{campaign-slug}/
├── {piece}.md                    # Published article
└── distribution/
    ├── {piece}-linkedin.md       # Published LinkedIn
    ├── {piece}-twitter.md        # Published Twitter
    └── {piece}-substack.md       # Published Substack
```

---

## Stage 5 Execution Workflow

**Your orchestration sequence:**

### Step 1: Read Stage 4 Decision

```
Read: threads/marketing/campaigns/{slug}/4-decision.md

Extract:
- Content pieces to create (titles, formats)
- Target keywords (for SEO)
- Distribution channels (blog, LinkedIn, Twitter, Substack, email)
- Success criteria (sessions, demos)
- Timeline
```

### Step 2: For Each Content Piece, Orchestrate Pipeline

**Step 2a: Invoke content-generation**

```
Invoke: marketing-execution/content-generation

Input:
  - campaign_slug: "{slug}"
  - decision_path: "threads/marketing/campaigns/{slug}/4-decision.md"
  - piece_name: "{piece-name}"

Expected output:
  - threads/marketing/campaigns/{slug}/5-actions/drafts/{piece}-article.md
  - threads/marketing/campaigns/{slug}/5-actions/drafts/{piece}-linkedin.md
  - threads/marketing/campaigns/{slug}/5-actions/drafts/{piece}-twitter.md
  - threads/marketing/campaigns/{slug}/5-actions/drafts/{piece}-substack.md

Wait for: Subskill completes (files exist)
```

**Step 2b: Flag for human review**

```
Update: ops/today.md

Add:
## Content Drafts Ready

**{Article Title}**
- Formats: Article + LinkedIn + Twitter + Substack
- Location: threads/marketing/campaigns/{slug}/5-actions/drafts/
- Action: Review and approve for SEO optimization

Wait for: Human approval
```

**Step 2c: Invoke seo-optimization**

```
Invoke: marketing-execution/seo-optimization

Input:
  - draft_path: "threads/marketing/campaigns/{slug}/5-actions/drafts/{piece}-article.md"
  - target_keyword: "{keyword from Stage 4 Decision}"
  - secondary_keywords: ["{list from Stage 4 Decision}"]

Expected output:
  - Overwrites drafts with optimized versions
  - threads/marketing/campaigns/{slug}/5-actions/drafts/{piece}-article.md (optimized)
  - threads/marketing/campaigns/{slug}/5-actions/drafts/{piece}-linkedin.md (optimized)
  - threads/marketing/campaigns/{slug}/5-actions/drafts/{piece}-twitter.md (optimized)
  - threads/marketing/campaigns/{slug}/5-actions/drafts/{piece}-substack.md (optimized)

Wait for: Subskill completes
```

**Step 2d: Flag for human approval**

```
Update: ops/today.md

Add:
## Optimized Content Ready

**{Article Title}**
- SEO: Keyword "{keyword}" applied
- Location: threads/marketing/campaigns/{slug}/5-actions/drafts/
- Action: Final approval before publishing

Wait for: Human approval
```

**Step 2e: Invoke content-distribution**

```
Invoke: marketing-execution/content-distribution

Input:
  - optimized_drafts_path: "threads/marketing/campaigns/{slug}/5-actions/drafts/"
  - campaign_slug: "{slug}"
  - channels: ["{from Stage 4 Decision}"]
  - piece_name: "{piece-name}"

Expected output:
  - artifacts/marketing/campaigns/{slug}/{piece}.md
  - artifacts/marketing/campaigns/{slug}/distribution/{piece}-linkedin.md
  - artifacts/marketing/campaigns/{slug}/distribution/{piece}-twitter.md
  - artifacts/marketing/campaigns/{slug}/distribution/{piece}-substack.md
  - artifacts/marketing/campaigns/{slug}/distribution-record.yaml

Wait for: Subskill completes
```

**Step 2f: Delete drafts**

```
Action: Delete temporary drafts

Delete:
  - threads/marketing/campaigns/{slug}/5-actions/drafts/

Reason: Content now published in artifacts/
```

**Step 2g: Update execution log**

```
Update: threads/marketing/campaigns/{slug}/5-actions/execution-log.md

Mark:
- [x] Article 1: "{Title}"
  - Draft created: {date}
  - Human reviewed: {date}
  - SEO optimized: {date}
  - Human approved: {date}
  - Published: {date}
  - URLs:
    - Blog: {url}
    - LinkedIn: {url}
    - Twitter: {url}
    - Substack: {url}
```

### Step 3: Report Progress

```
Update: ops/today.md

Add:
## Campaign Execution Progress

**{Campaign Name}:**
- [x] Article 1: Published ({blog URL})
- [x] LinkedIn post 1: Scheduled ({date})
- [ ] Article 2: Human review pending
```

### Step 4: Invoke Performance Tracking (After Publishing)

```
Invoke: marketing-execution/performance-tracking

Input:
  - campaign_slug: "{slug}"
  - distribution_record: "artifacts/marketing/campaigns/{slug}/distribution-record.yaml"
  - tracking_period: "30 days"

Expected output:
  - Weekly reports in ops/today.md
  - Performance data for Stage 6 learning

Wait for: Tracking period completes
```

---

## Subskill Invocation Details

### Invoking content-generation

**When:** After reading Stage 4 Decision, for each content piece

**How to invoke:**
```
Call subskill: marketing-execution/content-generation

Parameters:
  - campaign_slug: String (e.g., "luxury-validation-nov-2024")
  - decision_path: String (path to 4-decision.md)
  - piece_name: String (e.g., "elsaai-case-study")

Subskill will:
  1. Read Stage 4 Decision
  2. Load brand voice, patterns, source threads
  3. Generate ALL formats in parallel (article + LinkedIn + Twitter + Substack)
  4. Save to: threads/marketing/campaigns/{slug}/5-actions/drafts/

You wait for: Files to exist in drafts/
```

### Invoking seo-optimization

**When:** After human reviews and approves drafts

**How to invoke:**
```
Call subskill: marketing-execution/seo-optimization

Parameters:
  - draft_path: String (path to draft article)
  - target_keyword: String (e.g., "white-label SDK")
  - secondary_keywords: Array of Strings

Subskill will:
  1. Read draft content
  2. Optimize title, meta description, headings
  3. Apply keywords naturally
  4. Add internal links
  5. Optimize images (alt text, file names)
  6. Overwrite drafts with optimized versions

You wait for: Optimization complete (files updated)
```

### Invoking content-distribution

**When:** After human approves optimized content

**How to invoke:**
```
Call subskill: marketing-execution/content-distribution

Parameters:
  - optimized_drafts_path: String (path to drafts directory)
  - campaign_slug: String
  - channels: Array of Strings (e.g., ["blog", "linkedin", "twitter", "substack"])
  - piece_name: String

Subskill will:
  1. Read optimized drafts
  2. Prepare channel-specific versions
  3. Add UTM tracking
  4. Publish to: artifacts/marketing/campaigns/{slug}/
  5. Create distribution-record.yaml

You wait for: Publishing complete (files in artifacts/)
```

### Invoking performance-tracking

**When:** After content published, throughout tracking period

**How to invoke:**
```
Call subskill: marketing-execution/performance-tracking

Parameters:
  - campaign_slug: String
  - distribution_record: String (path to distribution-record.yaml)
  - tracking_period: String (e.g., "30 days")

Subskill will:
  1. Read distribution record (URLs, UTM parameters)
  2. Monitor metrics (traffic, engagement, conversions)
  3. Report weekly in ops/today.md
  4. Provide final data for Stage 6 learning

You wait for: Reports appear in ops/today.md
```

---

## Execution Log Format

**You maintain this file:**

```markdown
# Execution Log - {Campaign Name}

**Campaign:** {campaign-slug}
**Created:** {date}
**Status:** in-progress | completed

---

## Content Piece 1: "{Title}"

**Stage 4 Decision:**
- Type: {case study | blog article | announcement}
- Target keyword: "{keyword}"
- Channels: {blog, LinkedIn, Twitter, Substack}

**Execution Timeline:**
- [x] Drafts created: 2024-11-16 (content-generation invoked)
- [x] Human review: 2024-11-16 (approved with minor edits)
- [x] SEO optimized: 2024-11-16 (seo-optimization invoked)
- [x] Human approved: 2024-11-16 (final check passed)
- [x] Published: 2024-11-17 (content-distribution invoked)
- [x] Tracking started: 2024-11-17 (performance-tracking invoked)

**Published URLs:**
- Blog: https://glamyouup.com/blog/elsaai-white-label-sdk (UTM: ?utm_campaign={slug})
- LinkedIn: https://linkedin.com/company/glamyouup/posts/... (UTM: ?utm_source=linkedin&utm_campaign={slug})
- Twitter: https://twitter.com/glamyouup/status/... (UTM: ?utm_source=twitter&utm_campaign={slug})
- Substack: https://glamyouup.substack.com/p/elsaai-white-label (UTM: ?utm_source=substack&utm_campaign={slug})

**Performance (Days 1-7):**
- Sessions: 650 (performance-tracking monitoring)
- Demos: 8
- Conversion: 1.23%

---

## Content Piece 2: "{Title}"

**Stage 4 Decision:**
- Type: {type}
- Target keyword: "{keyword}"
- Channels: {channels}

**Execution Timeline:**
- [x] Drafts created: 2024-11-18 (content-generation invoked)
- [ ] Human review: Pending
```

---

## Quality Gates

**You enforce these by flagging for human review:**

### After content-generation (Before SEO)
- [ ] Drafts exist in threads/.../5-actions/drafts/
- [ ] ALL formats generated (article + LinkedIn + Twitter + Substack)
- [ ] Flag in ops/today.md for human review
- [ ] Wait for human approval

### After seo-optimization (Before Distribution)
- [ ] Drafts updated with SEO (keywords, meta, links)
- [ ] Flag in ops/today.md for human approval
- [ ] Wait for human approval

### After content-distribution (Before Tracking)
- [ ] Content published to artifacts/marketing/campaigns/{slug}/
- [ ] distribution-record.yaml created
- [ ] Drafts deleted from threads/.../5-actions/drafts/
- [ ] execution-log.md updated

---

## Human Touchpoints (You Flag These)

### Required Human Actions

**1. Review drafts** (after content-generation)
```
Update ops/today.md:

## Content Drafts Ready

**{Title}**
- Location: threads/marketing/campaigns/{slug}/5-actions/drafts/
- Formats: Article + LinkedIn + Twitter + Substack
- Action: Review and approve for SEO optimization
```

**2. Approve optimized content** (after seo-optimization)
```
Update ops/today.md:

## Optimized Content Ready

**{Title}**
- SEO: Keyword "{keyword}" applied
- Location: threads/marketing/campaigns/{slug}/5-actions/drafts/
- Action: Final approval before publishing
```

### Optional Human Actions

**Request revisions:**
- If human rejects draft, flag: "Revisions requested"
- Re-invoke content-generation with feedback
- Update execution-log.md: "Revision round {n}"

**Manual distribution:**
- If human wants manual control, flag: "Manual distribution"
- Skip content-distribution invocation
- Human publishes manually

---

## Error Handling

### If Stage 4 Incomplete
```
Check: threads/marketing/campaigns/{slug}/4-decision.md exists

If missing:
  - Flag: "Stage 4 decision missing, cannot execute"
  - Wait for human to complete Stages 1-4
  - Do NOT proceed
```

### If content-generation Fails
```
Check: Drafts exist after invocation

If missing:
  - Flag: "content-generation failed, check logs"
  - Alert in ops/today.md
  - Do NOT proceed to SEO
```

### If Human Rejects Draft
```
Action:
  - Log rejection in execution-log.md
  - Re-invoke content-generation with feedback
  - Update: "Revision round {n}"
  - Flag for review again
```

### If content-distribution Fails
```
Check: Files exist in artifacts/ after invocation

If missing:
  - Flag: "Publishing failed, content in drafts/"
  - Alert in ops/today.md
  - Keep drafts/ (do NOT delete)
  - Retry with human assistance
```

---

## Success Metrics

**Orchestration efficiency:**
- Time from Stage 4 to published: <7 days
- Subskill invocation success rate: >95%
- Human intervention required: Only at quality gates

**Execution tracking:**
- execution-log.md always up-to-date
- ops/today.md reflects current status
- All subskills invoked in correct order

---

## Usage Example

**Scenario:** Execute luxury validation campaign

```
1. Read Stage 4 Decision:
   Campaign: threads/marketing/campaigns/luxury-validation-nov-2024/
   Content: 2 case studies + 4 LinkedIn posts
   Keywords: "white-label SDK", "luxury fashion fit"
   Channels: blog, LinkedIn, Twitter, Substack

2. Execute Content Piece 1: "ElsaAI Case Study"

   Step 1: Invoke content-generation
   ↓
   Parameters:
     - campaign_slug: "luxury-validation-nov-2024"
     - decision_path: "threads/marketing/campaigns/luxury-validation-nov-2024/4-decision.md"
     - piece_name: "elsaai-case-study"
   ↓
   Wait for: Drafts created
   ✓ Files exist: article.md, linkedin.md, twitter.md, substack.md
   ↓
   Update execution-log.md: [x] Drafts created
   
   Step 2: Flag for human review
   ↓
   Update ops/today.md: "Drafts ready: ElsaAI Case Study"
   ↓
   Wait for: Human approval
   ✓ Human approved with minor edits
   ↓
   Update execution-log.md: [x] Human reviewed
   
   Step 3: Invoke seo-optimization
   ↓
   Parameters:
     - draft_path: "threads/.../drafts/elsaai-case-study-article.md"
     - target_keyword: "white-label SDK"
     - secondary_keywords: ["enterprise fashion SDK", "luxury fashion returns"]
   ↓
   Wait for: Optimization complete
   ✓ Drafts updated with SEO
   ↓
   Update execution-log.md: [x] SEO optimized
   
   Step 4: Flag for human approval
   ↓
   Update ops/today.md: "Optimized content ready: ElsaAI Case Study"
   ↓
   Wait for: Human approval
   ✓ Human approved
   ↓
   Update execution-log.md: [x] Human approved
   
   Step 5: Invoke content-distribution
   ↓
   Parameters:
     - optimized_drafts_path: "threads/.../drafts/"
     - campaign_slug: "luxury-validation-nov-2024"
     - channels: ["blog", "linkedin", "twitter", "substack"]
     - piece_name: "elsaai-case-study"
   ↓
   Wait for: Publishing complete
   ✓ Files created in artifacts/marketing/campaigns/luxury-validation-nov-2024/
   ↓
   Update execution-log.md: [x] Published (URLs added)
   
   Step 6: Delete drafts
   ↓
   Action: rm -rf threads/.../5-actions/drafts/
   ✓ Temporary files removed
   
   Step 7: Invoke performance-tracking
   ↓
   Parameters:
     - campaign_slug: "luxury-validation-nov-2024"
     - distribution_record: "artifacts/.../distribution-record.yaml"
     - tracking_period: "30 days"
   ↓
   Wait for: Weekly reports in ops/today.md
   ✓ Tracking started

3. Execute Content Piece 2: (Repeat Steps 1-7)

4. Report Progress:
   Update ops/today.md:
   "Campaign execution: 1/2 pieces published, 1 in review"

Total orchestration time: <2 hours (AI invocations)
Total human time: <45 minutes (reviews + approvals)
```

---

## Remember

**You are an orchestrator:**
- Read decisions
- Invoke subskills
- Track progress
- Flag for human review

**You are NOT a worker:**
- Don't generate content (invoke content-generation)
- Don't optimize SEO (invoke seo-optimization)
- Don't publish content (invoke content-distribution)
- Don't track metrics (invoke performance-tracking)

**Success = Smooth coordination of subskills from decision to published content.**

---

**Last updated:** 2025-11-21
**Subskills:** content-generation, seo-optimization, content-distribution, performance-tracking
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
description: Generate educational content drafts from thread learning. Transforms business insights into 80% complete content following brand voice (educational, technical, non-promotional) and content patterns. Human reviews for accuracy and depth.
allowed-tools: "Read,Write,Bash"
---

# Content Generation

Transform thread learning into educational content drafts.

## Purpose

**Input:** Content opportunity (from content-strategy) + Thread learning  
**Output:** 80% complete draft following brand voice and content patterns  
**Human role:** Review for accuracy, refine last 20%

**Core principle:** Share knowledge, not sales pitches. Build authority through depth.

---

## Process

### Step 1: Load Context

**Read opportunity:**
```bash
threads/marketing/campaigns/{campaign-slug}/4-decision.md  # Content plan with opportunities
```

Extract from opportunity:
- `topic` - What to write about
- `content_type` - blog|case-study|announcement|linkedin|email
- `target_keyword` - Primary SEO keyword
- `source_thread` - Where the learning came from
- `pillar` - Which content pillar this supports

**Read source material:**
```bash
# Source thread context
{source_thread}/1-input.md          # What triggered this
{source_thread}/2-hypothesis.md     # What was tested
{source_thread}/6-learning.md       # What was learned

# Strategic positioning
strategy/canvas/{product}/07-uvp.md     # Value proposition
strategy/canvas/{product}/05-problem.md # Problem definition

# Brand voice
artifacts/marketing/narrative/brand-voice.md
```

If `source_thread` includes sales narratives:
```bash
artifacts/sales/{segment}/narratives/{persona}-narrative.md
```

### Step 2: Select Pattern

**Load pattern guide for content type:**
```bash
{baseDir}/references/{content_type}-pattern.md
```

Available patterns:
- `blog-patterns.md` - 5 patterns (problem analysis, implementation guide, industry research, technical deep dive, case study)
- `case-study-pattern.md` - Customer success stories
- `announcement-pattern.md` - Product/feature launches
- `linkedin-patterns.md` - Company page posts
- `email-patterns.md` - Newsletters, announcements

**Pattern guides provide:**
- Structure principles (not rigid templates)
- Example openings/transitions
- Common pitfalls to avoid
- Length guidelines (ranges, not exact)

### Step 3: Generate Draft

**Apply pattern:**
- Follow structure from pattern guide
- Use source thread for facts/data
- Apply brand voice from `brand-voice.md`
- Include technical depth

**Brand voice essentials:**
- Educational focus (teach, don't sell)
- Data-driven (specific metrics from threads)
- Technical depth (architecture, methodology)
- Honest (include uncertainties, limitations)
- No CTAs (no "Book a demo", "Sign up now")

**Critical rules:**
- All metrics must come from threads (no invented numbers)
- Customer names require public approval (check thread for confirmation)
- No confidential information (remove proprietary details)
- Technical details must match thread/Canvas exactly

### Step 4: Validate Quality

**Run validation script:**
```bash
python {baseDir}/scripts/validate_draft.py --draft {draft_path}
```

Checks:
- Brand voice compliance (tone, depth, honesty)
- Factual accuracy (all claims sourced)
- Pattern adherence (structure, length)
- SEO readiness (if blog: keyword placement, H2s)

**Manual review flags:**
```markdown
## Editor Notes

**For human review:**
- [ ] {Specific items needing verification}
- [ ] {Potential improvements}
- [ ] {Missing context or data}
```

---

## Output Format

**Draft file:**
```markdown
---
title: "{Draft title}"
content_type: "{type}"
target_keyword: "{keyword}"
source_thread: "{path}"
pillar: "{pillar}"
created: "{date}"
status: "draft"
word_count: {count}
---

# {Title}

{Full content following pattern}

---

## Editor Notes

**For human review:**
- [ ] {Verification items}

**Potential improvements:**
- {Suggestions}
```

**Save location:**
```
threads/marketing/campaigns/{campaign-slug}/5-actions/drafts/{slug}-draft.md
```

**Update ops dashboard:**
```markdown
## Content Drafts Ready for Review

1. **{Title}**
   - Type: {content_type} ({word_count} words)
   - Location: {file_path}
   - Keyword: "{keyword}"
   - Action: Review for accuracy, approve for SEO optimization
```

---

## Edge Cases

### Insufficient Source Material
**If thread lacks details:**
- Flag: "Insufficient data for {content_type}"
- Request human provides additional context
- Or suggest alternative content type

### Confidential Information
**If thread contains confidential data:**
- Anonymize customer names, specific metrics
- Generalize: "A luxury brand" vs "BrandName"
- Flag for human review before proceeding

### Customer Approval Required
**If using customer name/data:**
- Flag: "Customer approval needed for public use"
- Mark draft as "pending approval"
- Don't proceed without confirmation

### Multiple Source Threads
**If opportunity combines multiple threads:**
- Read all source threads
- Synthesize learnings
- Note pattern: "Based on {N} deals across {timeframe}"

---

## Quality Standards

**Draft acceptance criteria:**
- 80% complete (human refines last 20%)
- All metrics sourced from threads
- Brand voice applied consistently
- Pattern structure followed
- Technical depth included
- No sales language

**Success = Educational content that builds authority and converts organically.**

---

## Usage Example

**Input opportunity:**
```yaml
topic: "How Enterprise Fashion Brands Use White-Label SDKs"
content_type: "case-study"
target_keyword: "white-label SDK"
source_thread: "threads/sales/elsa-white-label/"
pillar: "Product capabilities"
```

**Process:**
1. Read campaign: `threads/marketing/campaigns/luxury-validation-nov-2024/4-decision.md`
2. Read source: `threads/sales/elsa-white-label/6-learning.md`
3. Read positioning: `strategy/canvas/07-uvp.md`
4. Read voice: `artifacts/marketing/narrative/brand-voice.md`
5. Load pattern: `{baseDir}/references/case-study-pattern.md`
6. Generate draft following pattern structure
7. Validate with `validate_draft.py`
8. Save to `drafts/elsaai-case-study-draft.md`
9. Flag in `ops/today.md` for human review

**Output:** 1,450-word case study with metrics from thread, technical details, educational tone, ready for human review.
```


<!-- FILE: content-generation/references/announcement-linkedin-pattern.md -->

# content-generation/references/announcement-linkedin-pattern.md

```markdown
# Announcement & LinkedIn Patterns

Short-form content patterns for product launches and company insights.

---

## Announcement Pattern

**Use when:** Launching product/feature, announcing milestone, major update

**Structure:** What → Why → How → Who → When

**Length:** 400-700 words

**Tone:** Informative, not promotional

### Structure Guide

**What (100-150 words):**
- Feature/product name
- One-sentence summary
- Primary benefit (specific, not vague)

**Why (150-200 words):**
- Problem this solves (from threads)
- Customer demand (data from sales/support)
- Strategic context (how it fits product vision)

**How (200-300 words):**
- Technical approach (architecture, methodology)
- Key capabilities (what it does)
- Differentiation (why not alternatives)

**Who (100-150 words):**
- Target customers (specific segments)
- Use cases (concrete examples)
- Requirements (technical, business)

**When & Pricing (50-100 words):**
- Availability (now, beta, Q1 2025)
- Pricing tier (if applicable)
- How to access (link to docs, not hard CTA)

### Example: White-Label SDK Launch

```markdown
# White-Label Fit Recommendations Now Available for Enterprise

## What

White-label SDK for fit recommendations is now available for enterprise 
fashion brands ($100M+ GMV). Deploy AI-powered size recommendations under 
your brand—no third-party logos, co-branding, or external attribution.

Primary benefit: 94% fit accuracy without compromising brand consistency.

## Why

After 5 enterprise deals in Q4, we learned 100% of luxury brands chose 
white-label over co-branded widgets. The pattern was clear:

**Customer feedback:**
- "Our customers don't care who powers fit tech. They care it looks like us."
- "Co-branded widgets break our visual aesthetic. Non-negotiable for luxury."
- "At $200+ AOV, every detail matters. Third-party branding reduces trust."

**Business case:**
- Luxury brands: 31% return rates vs 22% mid-market
- Higher expectations: >90% fit accuracy threshold
- ROI matters: $805K annual savings (ElsaAI case study)

Strategic context: This completes our product offering—co-branded for 
growth stage ($50K tier), white-label for enterprise ($400K+ tier).

## How

**Architecture:**
- React SDK with full custom styling
- Deploy on your subdomain (fit.yourbrand.com)
- Zero external branding or attribution
- Same 94% accuracy as co-branded version

**Key capabilities:**
- Body measurement API (<200ms latency)
- Personalized fit recommendations
- Real-time analytics dashboard
- GDPR-compliant data residency

**Why not alternatives:**

*Co-branded widgets:*
- Pro: Lower cost ($50K/year)
- Con: Third-party branding breaks luxury aesthetic

*Custom ML model:*
- Pro: Full control
- Con: 3-6 month build, $200K+ development, ongoing maintenance

*White-label SDK:*
- Pro: 94% accuracy + brand consistency + 2-week integration
- Con: Higher tier ($400K+/year)

## Who

**Target customers:**
- Luxury fashion brands ($100M+ GMV)
- Premium e-commerce (AOV >$100)
- Strong brand identity (visual consistency critical)
- Technical team for integration (5-10 hours engineering)

**Use cases:**
- Reduce return rates (fit issues = 73% of returns)
- Maintain brand consistency (no co-branding)
- Scale fit recommendations (10K+ requests/hour)

**Requirements:**
- React or vanilla JS frontend
- REST API integration capability
- HTTPS domain for widget hosting
- Analytics integration (optional)

## When & Pricing

**Availability:** Available now

**Pricing:**
- White-label tier: $400K+/year (enterprise)
- Includes: Custom branding, dedicated support, SLA, EU data residency

**How to access:**
- Technical docs: [link]
- Integration guide: [link]
- Contact for enterprise tier: [email]

---

## Technical Details (Optional)

**Implementation:**
```javascript
// Your site
<script src="https://fit.yourbrand.com/widget.js"></script>

// Configuration
FitWidget.init({
  apiKey: 'your-key',
  theme: 'custom', // Inherits your CSS
  subdomain: 'fit.yourbrand.com'
});
```

**Performance:**
- Load time: <50ms (async)
- API latency: <200ms (p95)
- Uptime: 99.9% SLA

**Integration time:** 2 weeks (typical)
```

---

## LinkedIn Pattern

**Use when:** Sharing business learning, industry insight, company milestone

**Structure:** Insight → Analysis → Implication

**Length:** 300-600 words

**Tone:** Thoughtful, data-driven, educational

### Pattern 1: Business Learning

**Structure:**
1. Opening observation (surprising data point)
2. Analysis (why this happened, what it means)
3. Implication (lesson learned, actionable insight)
4. Soft link (if relevant, no hard CTA)

**Example:**
```
We closed 5 enterprise fashion deals in Q4. All 5 chose white-label 
SDK over co-branded.

This wasn't about hiding our technology. It was about brand consistency 
being non-negotiable.

**What we learned:**

Luxury brands ($100M+ GMV) prioritize brand consistency over vendor 
recognition. They'll pay 3x more for white-label because:
- Co-branded widgets break visual aesthetic
- Customers question legitimacy of third-party branding
- Mobile experience needs seamless integration

One customer (luxury marketplace, $200M GMV) told us: "Our customers 
don't care who powers fit recommendations. They care that it looks 
like ElsaAI."

**Fast fashion brands ($10M-$50M GMV) prefer co-branded.**

Opposite behavior:
- Third-party branding adds credibility ("powered by AI")
- Lower technical resources (easier implementation)
- Price-sensitive (white-label costs 3x)

**Takeaway:**
Customer segment dictates product packaging. Same technology, different 
positioning.

We're now offering both:
- White-label: Enterprise tier ($400K+)
- Co-branded: Growth tier ($50K+)

Technical docs: [link]
```

### Pattern 2: Industry Insight

**Structure:**
1. Industry observation (trend, pattern, data)
2. Analysis (breakdown, implications)
3. Non-obvious conclusion
4. Related content (if applicable)

**Example:**
```
Fashion e-commerce return rates: 25% average.
Everyone talks about reducing returns.
Few ask: what's causing them?

We analyzed 10,000 returns across 5 brands:
- Fit issues: 73%
- Color/style mismatch: 18%
- Quality issues: 6%
- Price regret: 3%

**The insight: Returns aren't buyer's remorse. They're fit prediction 
failures.**

Breakdown of fit issues:
- Too small: 42%
- Too large: 31%
- Wrong proportions: 27%

Here's the interesting part: 68% of customers who return for fit issues 
reorder the same item in a different size. They want the product. Size 
charts failed them.

**Implication:**
The $743B reverse logistics problem isn't about returns. It's about fit 
accuracy. Generic size charts: 68% accurate. Luxury customers need >90%.

At 25% return rates, $120 AOV, a $10M brand loses $2.5M annually. 
Fix fit prediction → capture 68% of that revenue.

Related: [How Body Scanning Achieves 94% Fit Accuracy]
```

### Pattern 3: Company Milestone

**Structure:**
1. Milestone announcement (specific achievement)
2. Context (what this means, why it matters)
3. Learning (what we discovered along the way)
4. Next step (where we're headed)

**Example:**
```
1 year ago we launched with 0 customers.
Today: $5.5M in enterprise contracts.

Not overnight success—5 pivots, 12 failed deals, 3 product rebuilds.

**What changed:**

Initially: AI-powered fit recommendations (generic positioning)
Now: White-label SDK for luxury brands (specific segment)

The shift happened after deal #3. Customer said: "We need this, but 
co-branded widgets break our luxury aesthetic."

That's when we realized: Problem wasn't fit accuracy. Problem was brand 
consistency at high price points.

**Rebuilt the product:**
- White-label architecture (your brand, not ours)
- 94% fit accuracy (luxury threshold: >90%)
- 2-week integration (vs 3-month custom build)

**Results:**
- 100% of luxury brands chose white-label
- 0% of growth-stage brands chose white-label
- Same technology, different packaging

**Learning:**
Product-market fit isn't just what you build. It's how you package it 
for specific segments.

Next: Expanding to footwear vertical. Same architecture, different 
category. [Link to technical approach]
```

---

## LinkedIn Quality Standards

**Good LinkedIn post:**
- Specific data (5 deals, $5.5M, 100%)
- Clear insight (luxury prefers white-label)
- Honest (5 pivots, 12 failed deals)
- Educational (others can apply this)
- Soft link (relevant content, not sales pitch)

**Bad LinkedIn post:**
- Vague claims ("significant growth")
- Self-promotional ("we're amazing")
- Engagement bait ("agree? comment below!")
- Hard CTA ("book a demo")
- Generic lessons ("persistence pays off")

---

## Announcement Quality Standards

**Good announcement:**
- Clear what/why/how/who/when
- Technical depth (architecture, performance)
- Data-driven (customer feedback, metrics)
- Differentiation (why not alternatives)
- Soft link (docs, not sales page)

**Bad announcement:**
- Buzzwords ("revolutionary", "game-changing")
- Vague benefits ("improve efficiency")
- No technical details
- Hard CTA throughout
- No target customer defined

---

## Common Mistakes

### ❌ Announcement as Sales Pitch

**Wrong:**
```
Introducing our revolutionary AI-powered SDK! Transform your business 
with cutting-edge technology! Book a demo now!
```

**Right:**
```
White-label fit recommendations now available. 94% accuracy, 2-week 
integration, zero co-branding. Technical docs: [link]
```

### ❌ LinkedIn Engagement Bait

**Wrong:**
```
Agree that AI is changing everything? 🚀 Comment your thoughts below! 
#AI #Innovation #FashionTech
```

**Right:**
```
5 enterprise deals. All chose white-label over co-branded. Luxury 
brands prioritize brand consistency over vendor recognition. Data: [thread]
```

### ❌ Vague Milestone

**Wrong:**
```
Excited to share we've grown significantly this year! Thanks to our 
amazing team! 🎉
```

**Right:**
```
$0 → $5.5M in 12 months. 5 pivots, 12 failed deals, 3 product rebuilds. 
Key learning: Product-market fit = right packaging for specific segment.
```

---

## Remember

**Announcements:**
- Informative, not promotional
- Technical depth included
- Specific target customer
- Soft link to docs, not sales

**LinkedIn:**
- Data-driven insights
- Honest about challenges
- Educational (others can apply)
- Soft link if relevant

Success = Share knowledge that builds authority organically
```


<!-- FILE: content-generation/references/blog-patterns.md -->

# content-generation/references/blog-patterns.md

```markdown
# Blog Article Patterns

Five patterns for educational blog content.

---

## Pattern 1: Problem Analysis

**Use when:** Explaining industry problem, sharing research, analyzing trends

**Structure:** Problem → Data → Analysis → Implication

**Length:** 800-1,200 words

### Opening Approaches

**Data-first:**
```
25% of online fashion purchases get returned. That's $743B in 
reverse logistics annually—more than the GDP of Switzerland.

But the problem isn't returns. It's why they happen.
```

**Surprising insight:**
```
We analyzed 10,000 fashion returns. Expected: price regret. 
Found: 73% were fit issues. The problem isn't buyer's remorse—
it's that size charts don't work.
```

**Industry observation:**
```
Every fashion brand says "reduce returns." Few ask: what's 
causing them? We spent 6 months analyzing 50 enterprise brands. 
Here's what returns actually tell us.
```

### Structure Guide

**Introduction (100-150 words):**
- Open with data or surprising fact
- State what's actually happening
- Preview what reader will learn

**The Problem (200-300 words):**
- Specific pain point (quantified)
- Business impact (revenue, costs)
- Why obvious solutions don't work

**Data Analysis (300-400 words):**
- Original research/data (from threads)
- Methodology (how you know this)
- Findings with specific numbers
- Surprising insights

**Implications (200-300 words):**
- What this means for audience
- Non-obvious conclusions
- Actionable insights (not sales pitch)

**Conclusion (100-150 words):**
- Key takeaways (3-5 points)
- Related topics (internal links)
- Soft link if relevant (no hard CTA)

### Example: ElsaAI Returns Analysis

```markdown
# Why 73% of Fashion Returns Are Actually Fit Issues

## Introduction

25% of online fashion purchases get returned. Brands blame buyer's 
remorse, showrooming, or pricing. We analyzed 10,000 returns across 
5 luxury brands. They were wrong.

73% of returns were fit issues—not price regret. Size charts don't 
work, and virtual try-on isn't accurate enough. The $743B reverse 
logistics problem isn't about returns. It's about fit prediction.

Here's what 6 months of return data taught us about why customers 
send clothes back.

## The Problem

Fashion brands lose $120 per return on average:
- Reverse logistics: $15 (shipping + processing)
- Lost revenue: $90 (can't resell as new)
- Customer service: $15 (15 min @ $60/hr)

At 25% return rates, a $10M/year brand loses $2.5M annually.

Brands try:
- Better size charts → Still 32% wrong
- Virtual try-on → 28% accuracy improvement (not enough)
- Free returns → Increases returns 40%

None address root cause: customers can't predict fit from product pages.

## Data Analysis

We analyzed 10,000 returns across 5 luxury brands ($50M-$200M GMV):

**Return reasons:**
- Fit issues: 73% (7,300 returns)
- Color/style mismatch: 18% (1,800)
- Quality issues: 6% (600)
- Price regret: 3% (300)

**Fit issue breakdown:**
- Too small: 42% (3,066)
- Too large: 31% (2,263)
- Wrong proportions: 27% (1,971)

**Methodology:**
- Analyzed return reason codes (when provided)
- Parsed customer service notes (5,000+ tickets)
- Interviewed 200 customers post-return
- Cross-referenced with reorder patterns

**Key insight:**
Customers who return for fit issues reorder 68% of the time—but in 
different sizes. They want the product. Size charts failed them.

**Surprising finding:**
Luxury brands ($100M+ GMV) have higher fit return rates (31% vs 22% 
mid-market). Why? Higher expectations. Luxury customers expect 
perfect fit, mid-market customers keep "good enough."

## Implications

**Insight 1: Size charts are the problem**

Generic size charts average 68% accuracy. That means 32% of customers 
get wrong sizes—and luxury customers won't accept "close enough."

The fix isn't better charts. It's personalized fit prediction.

**Insight 2: Virtual try-on isn't accurate enough**

Current virtual try-on: 72% accuracy (4% improvement over charts). 
Luxury threshold: >90% to build trust.

Gap between current tech (72%) and customer expectation (90%) explains 
why adoption stays low (<5% of luxury sites).

**Insight 3: Returns signal buying intent**

68% of fit-issue returns lead to reorders. These aren't "I don't want 
this" returns—they're "I want this but in the right size."

Opportunity: Fix fit prediction = capture 68% of return revenue.

## Conclusion

Fashion returns aren't about buyer's remorse. 73% are fit issues, and 
customers reorder 68% of the time when they find the right size.

**Key takeaways:**

1. Size charts are 68% accurate—not good enough for luxury
2. Virtual try-on at 72% accuracy misses the 90% trust threshold
3. Fit returns signal buying intent (68% reorder rate)
4. Luxury brands need >90% fit accuracy to reduce returns meaningfully
5. $743B reverse logistics problem is actually fit prediction problem

Related: [How Body Scanning Achieves 94% Fit Accuracy] [Why Luxury 
Brands Choose White-Label SDK]

Technical approach: [Fit Prediction Architecture Docs]
```

---

## Pattern 2: Implementation Guide

**Use when:** Teaching how to solve problem, technical tutorial, how-to

**Structure:** Challenge → Approach → Implementation → Results

**Length:** 1,200-2,000 words

### Opening Approaches

**Problem statement:**
```
Building real-time fit recommendations sounds simple. Load body 
measurements, run ML model, return size. We shipped in 2 days.

Then we tried to scale. Latency spiked to 3 seconds. Accuracy 
dropped to 61%. Our "simple" system wasn't production-ready.
```

**Challenge framing:**
```
Every fashion SDK faces the same challenge: accurate fit predictions 
under 200ms. Miss that threshold, conversion drops 15%. Here's how 
we got from 3 seconds to 180ms without sacrificing accuracy.
```

**Lesson learned:**
```
We rebuilt our fit recommendation system 3 times. First version: 
too slow. Second: too inaccurate. Third: production-ready at scale.

Here's what we learned about real-time ML in e-commerce.
```

### Structure Guide

**Introduction (150-200 words):**
- Problem to solve
- Why it's challenging  
- What this guide covers

**The Challenge (200-300 words):**
- Specific technical/business problem
- Requirements (performance, accuracy, scale)
- Why obvious approaches fail
- Constraints (latency, cost, accuracy)

**Our Approach (300-500 words):**
- Solution architecture/methodology
- Why this works (technical reasoning)
- Trade-offs considered
- Alternative approaches rejected

**Implementation (400-800 words):**
- Step-by-step process
- Technical details (code, architecture, algorithms)
- Pitfalls to avoid
- Time/resource requirements

**Results (200-300 words):**
- Metrics from implementation
- Performance benchmarks
- Lessons learned
- What we'd do differently

**Conclusion (100-150 words):**
- Key takeaways
- When to use this approach
- Related resources (technical docs)

### Example: Real-Time Fit Recommendations

```markdown
# Building Real-Time Fit Recommendations: 3s → 180ms

## Introduction

Fit recommendation systems need <200ms latency. Above that, conversion 
drops 15%. Our first version took 3 seconds. Accuracy: 61%.

We rebuilt 3 times to get production-ready performance: 180ms latency, 
94% accuracy, 99.9% uptime.

Here's how we architected real-time ML for fashion e-commerce.

## The Challenge

**Requirements:**
- Latency: <200ms (conversion threshold)
- Accuracy: >90% (luxury customer trust threshold)
- Scale: 10,000 requests/hour per brand
- Cost: <$0.001 per prediction (sustainable economics)

**Why it's hard:**
- ML models are slow (500ms-2s for body measurement processing)
- High accuracy requires complex models (more computation)
- Real-time = no batch processing benefits
- Fashion has 100+ body measurement combinations per garment

**Failed approaches:**

*Attempt 1: Real-time ML inference*
- Latency: 3,200ms (16x too slow)
- Accuracy: 87% (good but not luxury threshold)
- Cost: $0.15/prediction (150x budget)

*Attempt 2: Pre-compute all combinations*
- Storage: 50TB per brand (unsustainable)
- Accuracy: 94% (excellent)
- Update latency: 6 hours (stale recommendations)

Neither worked at scale.

## Our Approach

**Hybrid architecture: Real-time measurement + cached predictions**

Core insight: Body measurements change rarely. Garment fit patterns 
change never (once designed). Separate these concerns.

**Architecture:**
```
User → Measurement API (150ms) → Prediction Cache (30ms) → Response
         ↓
      ML Model (background)
         ↓
      Cache warming
```

**Why this works:**
1. Measure body once, cache measurements (99% cache hit rate)
2. Pre-compute fit predictions for popular garments (top 20% = 80% traffic)
3. Real-time ML only for cache misses (<1% of requests)

**Trade-offs:**
- Pro: 180ms average latency (10x faster)
- Pro: $0.0008/prediction (within budget)
- Con: Cache warming takes 2 hours for new garments
- Con: Requires prediction invalidation on garment updates

**Rejected alternatives:**
- Edge compute: 40% faster but 3x cost
- Simpler model: 60ms faster but 85% accuracy (too low)
- Client-side ML: Zero latency but 76% accuracy (insufficient)

## Implementation

**Step 1: Measurement API**

```python
# FastAPI endpoint
@router.post("/measurements")
async def get_measurements(
    user_id: str,
    height: float,
    weight: float,
    body_shape: BodyShape
) -> MeasurementResponse:
    # Check cache (Redis)
    cached = await cache.get(f"user:{user_id}:measurements")
    if cached:
        return MeasurementResponse(**cached)
    
    # Compute if cache miss
    measurements = await ml_model.predict_measurements(
        height, weight, body_shape
    )
    
    # Cache for 30 days (measurements change rarely)
    await cache.set(
        f"user:{user_id}:measurements",
        measurements.dict(),
        ttl=2592000
    )
    
    return MeasurementResponse(**measurements)
```

**Latency breakdown:**
- Cache hit: 15ms (Redis lookup)
- Cache miss: 150ms (ML inference + cache write)
- Cache hit rate: 99.2%
- Average: 16ms

**Step 2: Prediction Cache**

```python
# Pre-compute predictions for popular garments
@task(schedule="@hourly")
async def warm_prediction_cache():
    # Top 20% garments = 80% traffic
    popular_garments = await db.get_popular_garments(
        limit=200,  # Per brand
        time_window="7d"
    )
    
    # For each body type cluster (50 clusters)
    for cluster in BodyCluster.all():
        for garment in popular_garments:
            prediction = await ml_model.predict_fit(
                cluster.representative_measurements,
                garment.fit_data
            )
            
            await cache.set(
                f"fit:{cluster.id}:{garment.id}",
                prediction.dict(),
                ttl=86400  # 24 hours
            )
```

**Cache efficiency:**
- Garments cached: 200 per brand
- Body clusters: 50 (k-means on measurement space)
- Cache size: 10,000 predictions per brand
- Storage: 50MB per brand (sustainable)
- Warming time: 2 hours

**Step 3: Real-Time Prediction**

```python
@router.post("/predict-fit")
async def predict_fit(
    garment_id: str,
    user_id: str
) -> FitPrediction:
    # Get cached measurements
    measurements = await get_measurements(user_id)
    
    # Find body cluster
    cluster = BodyCluster.find_nearest(measurements)
    
    # Check prediction cache
    cache_key = f"fit:{cluster.id}:{garment_id}"
    cached_prediction = await cache.get(cache_key)
    
    if cached_prediction:
        return FitPrediction(**cached_prediction)  # 30ms
    
    # Cache miss: real-time ML
    garment = await db.get_garment(garment_id)
    prediction = await ml_model.predict_fit(
        measurements, garment.fit_data
    )  # 500ms
    
    # Cache result
    await cache.set(cache_key, prediction.dict(), ttl=86400)
    
    return prediction
```

**Latency breakdown:**
- Cache hit: 30ms (measurement + prediction lookup)
- Cache miss: 680ms (measurement + ML + cache write)
- Cache hit rate: 92% (after warm-up)
- Average: 84ms

**Pitfalls avoided:**

1. **Don't cache per-user predictions**
   - Problem: 1M users × 200 garments = 200M cache entries
   - Solution: Cluster users (50 clusters × 200 garments = 10K entries)

2. **Don't real-time compute measurements**
   - Problem: Adds 500ms every request
   - Solution: Cache measurements separately (99% hit rate)

3. **Don't over-cluster body types**
   - Problem: 500 clusters = 5% accuracy gain, 10x cache size
   - Solution: 50 clusters = optimal accuracy/size trade-off

**Time investment:**
- Architecture: 1 week
- Implementation: 2 weeks
- Load testing: 1 week
- Production tuning: 2 weeks
- Total: 6 weeks (2 engineers)

## Results

**Performance:**
- Latency (p50): 84ms (2.4x under threshold)
- Latency (p95): 180ms (still under threshold)
- Latency (p99): 520ms (cache miss penalty)
- Accuracy: 94% (above luxury threshold)

**Economics:**
- Cost per prediction: $0.0008 (within budget)
- Cache hit rate: 92% (after warm-up)
- Infrastructure: $200/month per brand

**Production metrics (30 days):**
- Requests served: 12M
- Cache hits: 11M (92%)
- Cache misses: 1M (8%)
- Uptime: 99.94%

**Lessons learned:**

1. **Separate concerns:** Measurements change rarely, garments never—cache differently
2. **Cluster users:** 50 body type clusters = 92% cache hit rate
3. **Warm strategically:** Top 20% garments = 80% traffic
4. **Real-time fallback:** Cache miss penalty acceptable at 8% frequency

**What we'd do differently:**
- Start with 20 clusters (faster iteration)
- A/B test latency thresholds (maybe 300ms acceptable?)
- Regional caching (reduce latency to <50ms)

## Conclusion

Real-time ML in e-commerce requires hybrid architecture: cache common 
cases, real-time compute edge cases.

**Key takeaways:**

1. Separate concerns: measurements (cache 30d) vs predictions (cache 24h)
2. Cluster users: 50 body types = 92% cache hit rate, 50MB cache
3. Warm strategically: Top 20% garments = 80% traffic
4. Real-time fallback: 8% cache miss rate acceptable
5. Target: <200ms latency, >90% accuracy, <$0.001/prediction

Related: [Fit Prediction ML Architecture] [Body Measurement API Docs]

Technical docs: [API Reference] [Integration Guide]
```

---

## Pattern 3: Industry Research

**Use when:** Analyzing industry trends, competitive landscape, market analysis

**Structure:** Context → Research → Findings → Implications

**Length:** 1,000-1,500 words

### Opening: Start with observation, preview insight

### Sections: Context → Method → Data → Analysis → So What

### Example: "We Analyzed 50 Fashion E-Commerce Sites: Here's What Fit Solutions They Use"

---

## Pattern 4: Technical Deep Dive

**Use when:** Explaining complex system, architecture decision, technical trade-offs

**Structure:** Problem → Constraints → Solution → Trade-offs → Decision

**Length:** 1,500-2,500 words

### Opening: Technical problem, why it's interesting

### Sections: Problem → Requirements → Approaches → Analysis → Choice

### Example: "Why We Chose Category Theory for Microservices Architecture"

---

## Pattern 5: Case Study (Blog Format)

**Use when:** Customer success as educational content (different from sales case study)

**Structure:** Customer → Problem → Solution → Results → Lessons

**Length:** 1,200-1,800 words

### Opening: Result first, then setup

### Sections: Who → What problem → How solved → What happened → What we learned

### Example: "How ElsaAI Reduced Returns 38%: Architecture Lessons"

---

## Pattern Selection

| Goal | Pattern | Best For |
|------|---------|----------|
| Explain problem | Problem Analysis | Industry issues, research |
| Teach solution | Implementation Guide | Technical how-to |
| Analyze landscape | Industry Research | Competitive analysis |
| Explain architecture | Technical Deep Dive | System design decisions |
| Share success | Case Study (Blog) | Educational customer story |

## Remember

- Patterns guide structure, not prescribe content
- Technical depth builds credibility
- Data from threads, not invented
- Educational tone, no sales language

Success = Following pattern structure + Applying brand voice + Including technical depth
```


<!-- FILE: content-generation/references/case-study-pattern.md -->

# content-generation/references/case-study-pattern.md

```markdown
# Case Study Pattern

Customer success stories as educational content.

**Use when:** Sharing customer results, validating approach with real data, demonstrating ROI

**Structure:** Customer → Problem → Solution → Results → Technical Details

**Length:** 1,000-1,500 words

---

## Core Principle

Case studies are **evidence**, not sales pitches. Show what happened, include numbers, explain why it worked.

**Good case study:**
- Specific metrics (25% → 18% return rate)
- Technical details (architecture, implementation)
- Honest about challenges (what didn't work)
- Educational (lessons others can apply)

**Bad case study:**
- Vague claims ("dramatically improved")
- No technical depth (just results)
- Overly promotional (selling, not teaching)
- Cherry-picked success (hiding failures)

---

## Opening Approaches

### Result-First Opening

Start with the outcome, then explain how:

```
# ElsaAI Reduced Returns 38% with White-Label Fit Recommendations

ElsaAI is a luxury marketplace with $200M GMV. They faced 25% return 
rates on dresses, costing $2.1M annually.

After implementing white-label fit recommendations, returns dropped 
to 18%—a 28% reduction. Here's how they did it, what challenges they 
faced, and what we learned.
```

### Problem-First Opening

Start with customer pain, then reveal solution:

```
# How a Luxury Marketplace Fixed 25% Return Rates in 30 Days

ElsaAI had a problem: 1 in 4 dresses got returned. At $120 average 
order value, that's $1.5M in lost revenue annually—plus $600K in 
reverse logistics.

Generic size charts weren't working. Virtual try-on improved accuracy 
from 68% to 72%—not enough for luxury customers who expect perfection.

Here's how they got to 94% fit accuracy and reduced returns 28%.
```

### Challenge-First Opening

Start with what makes this difficult:

```
# The Challenge: Luxury Brand Consistency vs Fit Accuracy

ElsaAI needed 90%+ fit accuracy to reduce returns. But every fit 
solution they evaluated required co-branded widgets—breaking their 
luxury brand aesthetic.

The dilemma: Accept lower accuracy to maintain brand consistency, or 
compromise brand for better fit recommendations?

Here's how they solved both with white-label architecture.
```

---

## Structure Guide

### Customer Overview (100-150 words)

**What to include:**
- Company name, industry, size (GMV, customers)
- Business model (B2C marketplace, D2C brand)
- Initial challenge (quantified)

**Example:**
```
ElsaAI is a luxury fashion marketplace with $200M GMV serving 250K 
monthly customers. Their curated selection emphasizes high-end 
designers and premium pricing—where brand consistency is critical.

They faced a 25% return rate on dresses, costing $3.2M annually in 
reverse logistics and lost revenue.
```

**Don't:**
- Generic company description
- Vague metrics ("large customer base")
- Skip the initial problem

---

### The Problem (250-350 words)

**What to include:**
- Specific pain point (quantified impact)
- Business cost (revenue, operations, customer experience)
- Previous solutions attempted (what failed and why)
- Why change was needed now

**Example:**
```
## The Problem

Luxury customers expect flawless brand experiences. ElsaAI's previous 
fit solution used a co-branded widget that broke their visual aesthetic:

- Widget displayed third-party branding
- Design didn't match site style
- Mobile experience was clunky
- Customers questioned legitimacy

Beyond aesthetics, fit accuracy was insufficient:
- Generic size charts: 68% accuracy
- Virtual try-on competitors: 72% accuracy
- Neither met the 85% threshold ElsaAI needed

At 25% return rates, $120 average order value, and 50K dress orders/year:
- Revenue impact: $1.5M (25% of $6M)
- Reverse logistics: $400K ($8 per return)
- Customer service: $200K (15 min per return @ $40/hr)
- Total annual cost: $2.1M

**What they tried:**

1. **Better size charts** → Still 32% inaccurate
2. **Virtual try-on (competitor)** → 72% accuracy, but co-branded
3. **Custom ML model** → 3-month build, $200K development cost

None solved both accuracy AND brand consistency.
```

**Don't:**
- Skip the cost quantification
- Ignore previous attempts
- Use generic pain points ("needed better solution")

---

### Solution (300-400 words)

**What to include:**
- What they implemented (specific technology/approach)
- Technical approach (architecture, integration)
- Implementation timeline and resources
- Why this approach worked

**Example:**
```
## Solution

ElsaAI implemented our white-label SDK with custom branding:

**Technical approach:**
- React SDK with custom styling
- ElsaAI's fonts, colors, design system
- Hosted on ElsaAI subdomain (fit.elsaai.com)
- Zero external branding

**Integration:**
- 2-week implementation
- 10 hours engineering time (ElsaAI team)
- No infrastructure changes needed
- API integration via REST endpoints

**Fit accuracy:**
- AI trained on 10M+ body scans
- 94% accuracy on luxury dress category
- Personalized per customer (not generic size charts)

**Why white-label mattered:**

ElsaAI customers pay $150-$500 per dress. At this price point:
- Brand consistency is non-negotiable
- Co-branded widgets signal "outsourced" (reduces trust)
- Mobile experience must be seamless

White-label removed trust friction while delivering 94% accuracy—
crossing the luxury credibility threshold (>90%).

**Architecture:**
```
Customer → Product Page → fit.elsaai.com/widget (white-label)
                              ↓
                        Body Measurement API
                              ↓
                        Recommendation Engine (94% accuracy)
                              ↓
                        Size Recommendation
```

**Implementation details:**
- SDK loaded asynchronously (no page speed impact)
- Body measurement API: <200ms latency
- Recommendation cache: 99.9% uptime
- Analytics dashboard: Real-time fit data
```

**Don't:**
- Skip technical details (how it actually works)
- Use buzzwords instead of architecture
- Omit implementation timeline/resources

---

### Results (300-400 words)

**What to include:**
- Metrics (before/after with timeline)
- Business impact (revenue, costs, efficiency)
- Unexpected benefits
- Customer quote (if available)

**Example:**
```
## Results

**30-day pilot (dress category only):**
- Return rate: 25% → 18% (28% reduction)
- Fit accuracy: 94% (vs 68% baseline)
- Customer satisfaction: 3.2 → 4.1 (27% improvement)
- Mobile conversion: +12% (cleaner UI, no third-party branding)

**Annual projection:**
- Returns avoided: 3,500 (7% of 50K orders)
- Revenue retained: $420K
- Logistics saved: $280K
- Customer service saved: $105K
- Total annual savings: $805K

**ROI:**
- Implementation cost: $500K/year (white-label tier)
- Savings: $805K/year
- Net benefit: $305K (61% ROI)
- Payback: 7.4 months

**Unexpected benefits:**

1. **Mobile conversion increased 12%**
   - Cleaner UI without third-party branding
   - Faster load time (SDK optimized for mobile)
   - Higher trust signal (seamless brand experience)

2. **Customer service tickets reduced 15%**
   - Fewer fit-related questions pre-purchase
   - Fewer return requests
   - Higher confidence in recommendations

3. **Marketing asset: White-label as luxury signal**
   - ElsaAI now markets "proprietary fit technology"
   - White-label enables brand storytelling
   - Competitive differentiation in luxury segment

**Customer quote:**

"Our customers don't care who powers fit recommendations. They care 
that it looks like ElsaAI. White-label gave us 94% accuracy without 
compromising our brand." — Sarah Chen, CTO, ElsaAI
```

**Don't:**
- Use vague metrics ("significant improvement")
- Skip the ROI calculation
- Omit unexpected learnings

---

### Technical Details (200-300 words)

**What to include:**
- Architecture/integration approach
- Challenges overcome
- Why it worked (technical reasoning)
- Applicability to others

**Example:**
```
## Technical Details

**Architecture:**
- SDK loaded asynchronously (no page speed impact)
- Body measurement API: <200ms latency
- Recommendation cache: 99.9% uptime
- Analytics dashboard: Real-time fit data

**Challenges overcome:**

1. **Brand consistency:** Custom CSS matching ElsaAI's design system exactly
   - Solution: React SDK with CSS-in-JS, inherits ElsaAI theme
   - Result: Zero visual distinction from native components

2. **Mobile performance:** Lazy loading prevented slowdown
   - Solution: Async script loading, critical path optimization
   - Result: No impact on Lighthouse score (98 → 97)

3. **Data privacy:** GDPR-compliant body measurement storage
   - Solution: EU data residency, 30-day data retention
   - Result: Legal approval in 5 EU markets

**Why it worked:**
- White-label removed trust friction (no third-party branding)
- 94% accuracy exceeded luxury threshold (>90%)
- Fast integration minimized engineering burden (2 weeks vs 3 months custom)

**Applicability:**

This approach works for fashion brands with:
- Strong brand identity (luxury, premium positioning)
- High average order value (>$100)
- Technical team for integration (5-10 hours engineering time)
- Volume to justify cost ($400K+/year white-label tier)
```

**Don't:**
- Skip the challenges (makes success seem easy)
- Use generic architecture descriptions
- Omit applicability criteria

---

### Conclusion (100-150 words)

**What to include:**
- Key success factors (3-5 points)
- Lessons learned
- Applicability to readers
- Soft link to product (if relevant)

**Example:**
```
## Conclusion

ElsaAI's success validates three insights:

1. **Luxury brands won't compromise on brand consistency** - Co-branded 
   solutions are non-starters regardless of accuracy

2. **Fit accuracy >90% is table stakes** - Luxury customers expect 
   near-perfect recommendations

3. **Fast implementation matters** - 2-week integration vs 3-month 
   custom build enabled rapid validation

This approach works for fashion brands with strong brand identity, 
high AOV (>$100), and technical capacity for integration.

White-label SDK technical docs: [link]
```

**Don't:**
- Hard CTA ("Book a demo now!")
- Overgeneralize lessons
- Skip the applicability criteria

---

## Quality Checklist

Before completing case study:

- [ ] **Metrics:** All numbers sourced from thread (no invented data)
- [ ] **Customer approval:** Name and data approved for public use
- [ ] **Technical depth:** Architecture, implementation details included
- [ ] **Honest:** Challenges and failures mentioned
- [ ] **ROI calculated:** Cost vs benefit shown clearly
- [ ] **Applicable:** Who this approach works for (and doesn't)
- [ ] **Educational tone:** Teaching, not selling
- [ ] **No sales language:** No buzzwords, CTAs, promotional phrasing

---

## Common Mistakes

### ❌ Vague Metrics

**Wrong:**
```
ElsaAI saw significant improvements in return rates and customer 
satisfaction after implementing our solution.
```

**Right:**
```
ElsaAI: Return rate 25% → 18% (28% reduction). Customer satisfaction 
3.2 → 4.1 (27% improvement). Annual savings: $805K.
```

### ❌ Skipping Technical Details

**Wrong:**
```
We integrated our AI-powered SDK and it worked great.
```

**Right:**
```
React SDK with custom CSS matching ElsaAI design system. Async loading 
(no page speed impact). API latency <200ms. 94% fit accuracy on 10M+ 
body scan training data.
```

### ❌ Promotional Tone

**Wrong:**
```
Our revolutionary solution transformed their business! Book a demo 
to see the magic yourself!
```

**Right:**
```
White-label SDK gave them 94% accuracy without compromising brand. 
Technical docs: [link]
```

### ❌ Cherry-Picking Success

**Wrong:**
```
Everything went perfectly. Implementation was flawless. Results exceeded 
all expectations.
```

**Right:**
```
Challenges: CSS matching took 3 iterations. Mobile performance required 
lazy loading. GDPR compliance delayed EU launch 2 weeks. But 94% accuracy 
made it worth solving.
```

---

## Remember

Case studies are **evidence-based education**, not sales collateral.

Good case study = Specific metrics + Technical depth + Honest challenges + Applicable lessons

Success = Reader learns what works, why it works, and when to apply it
```


<!-- FILE: content-generation/references/email-patterns.md -->

# content-generation/references/email-patterns.md

```markdown
# Email Pattern

Newsletter and announcement emails that educate, don't sell.

**Use when:** Weekly/monthly newsletter, product announcement email, educational series

**Length:** 400-600 words

**Tone:** Personal, educational, non-promotional

---

## Core Principles

**Good email:**
- Curates knowledge (links to full content)
- Personal voice (from real person)
- Educational focus (teaching, not selling)
- Scannable structure (sections, headers)
- No hard CTAs (soft links at most)

**Bad email:**
- Sales pitch in disguise
- Generic corporate voice
- Walls of text (not scannable)
- Multiple CTAs ("Book now!", "Try free!")
- Engagement tricks ("Click here to learn more!")

---

## Newsletter Pattern

**Use when:** Regular updates (weekly, monthly), curated insights, company news

**Structure:** Personal greeting → 2-3 sections (insight/resource/update) → Closing

### Structure Guide

**Subject Line:**
- Specific value, not clickbait
- 40-60 characters
- Preview extends subject (doesn't repeat)

**Examples:**
```
✅ "Why luxury brands choose white-label SDK" (specific)
❌ "You won't believe this!" (clickbait)

✅ "Q4 learning: 5 deals, 1 pattern" (concrete)
❌ "Our latest insights" (vague)

✅ "How ElsaAI reduced returns 38%" (data-driven)
❌ "Amazing customer success story" (promotional)
```

**Opening (50-75 words):**
- Personal greeting (not generic)
- Context: Why this matters now
- Preview: What they'll learn

**Section 1: Key Insight (150-200 words):**
- Business learning or announcement
- Supporting data/context
- Link to full article (if applicable)

**Section 2: Educational Resource (150-200 words):**
- How-to content, case study, technical guide
- Practical takeaway
- Link to full content

**Section 3: Update (100-150 words):**
- Product update, milestone, industry news
- Brief context
- Link for more (if relevant)

**Closing (25-50 words):**
- Personal sign-off (not corporate)
- Real person signature (name, title)
- No hard CTA

### Newsletter Example

```
Subject: Why luxury brands choose white-label SDK over co-branded
Preview: 5 deals in Q4. All picked white-label. Here's what we learned.

---

Hey [Name],

We closed 5 enterprise fashion deals in Q4. All 5 chose white-label 
SDK over our co-branded option.

Not what we expected. Here's what we learned about luxury brand 
positioning—and a case study showing how one customer reduced returns 38%.

---

**Q4 Learning: Luxury Brands Won't Compromise on Brand Consistency**

100% of luxury brands ($100M+ GMV) chose white-label over co-branded 
widgets—even though white-label costs 3x more.

Why? Brand consistency at $200+ price points is non-negotiable:
- Co-branded widgets break visual aesthetic
- Third-party branding reduces customer trust
- Mobile experience needs seamless integration

One customer (luxury marketplace, $200M GMV) told us: "Our customers 
don't care who powers fit tech. They care it looks like us."

Meanwhile, fast fashion brands ($10M-$50M GMV) prefer co-branded for 
credibility ("powered by AI") and lower cost.

Same technology. Different packaging. Segment matters more than product.

Read the full analysis: [5 Enterprise Deals, 1 Pattern: Brand Over Badge]

---

**Case Study: How ElsaAI Reduced Returns 38% in 30 Days**

ElsaAI (luxury marketplace, $200M GMV) faced 25% return rates on 
dresses—$2.1M annual cost.

After implementing white-label fit recommendations:
- Return rate: 25% → 18% (28% reduction)
- Fit accuracy: 94% (vs 68% generic size charts)
- ROI: $305K net benefit (61% ROI, 7.4-month payback)

Technical details: React SDK, <200ms API latency, custom CSS matching 
their design system exactly. No third-party branding.

Implementation time: 2 weeks (10 hours engineering).

The case study includes architecture diagrams, ROI breakdown, and 
lessons on what didn't work.

Read the full story: [ElsaAI Case Study: Architecture & Results]

---

**Product Update: White-Label SDK Now Generally Available**

Based on Q4 demand, white-label SDK is now available for all enterprise 
fashion brands ($100M+ GMV).

What's included:
- 94% fit accuracy (trained on 10M+ body scans)
- Full custom branding (your fonts, colors, domain)
- 2-week integration (typical timeline)
- Enterprise SLA (99.9% uptime, dedicated support)

Pricing: $400K+/year (enterprise tier)

Technical docs: [Integration Guide]

---

That's it for this month. Next up: Expanding to footwear vertical—
same architecture, different category.

— Bella
Co-founder, GlamYouUp
```

---

## Announcement Email Pattern

**Use when:** Product launch, major feature, company milestone

**Structure:** What happened → Why it matters → What you can do

### Structure Guide

**Subject Line:**
- Clear announcement, not teaser
- 40-60 characters

**Examples:**
```
✅ "White-label SDK now available for enterprise"
❌ "Big news from GlamYouUp!"

✅ "Introducing: Real-time fit recommendations"
❌ "You've been waiting for this"
```

**Opening (50-75 words):**
- Announcement (what's new)
- Why this matters (problem solved)

**Body (300-400 words):**
- What this enables (capabilities)
- Who it's for (target customers)
- How it works (technical overview)
- When available (timeline)

**Closing (25-50 words):**
- Next step (soft link to docs)
- Personal sign-off

### Announcement Example

```
Subject: White-label fit recommendations now available
Preview: Deploy AI-powered size recommendations under your brand.

---

Hey [Name],

White-label SDK is now available for enterprise fashion brands.

After 5 enterprise deals chose white-label over co-branded in Q4, we 
made it generally available. Deploy 94% fit accuracy without third-party 
branding or co-branded widgets.

Here's what you need to know.

---

**What This Enables**

Full brand control:
- Your domain (fit.yourbrand.com)
- Your styling (custom CSS, fonts, colors)
- Zero external attribution or logos
- Seamless mobile experience

Same 94% fit accuracy as co-branded version:
- Trained on 10M+ body scans
- Personalized recommendations per customer
- <200ms API latency
- Real-time analytics dashboard

**Who It's For**

Enterprise fashion brands with:
- Strong brand identity (luxury, premium)
- High AOV (>$100)
- Technical capacity (5-10 hours integration)
- Volume to justify cost ($400K+/year)

**How It Works**

1. Deploy React SDK on your site
2. Host widget on your subdomain
3. Customize styling to match your design system
4. Integrate via REST API

Implementation time: 2 weeks (typical)

Technical architecture:
```
Your site → fit.yourbrand.com (white-label widget)
               ↓
         Body Measurement API
               ↓
         Recommendation Engine
               ↓
         Size Recommendation
```

**When Available**

Now. Technical docs and integration guide ready.

---

**Next Steps**

Technical documentation: [Integration Guide]
Case study: [How ElsaAI Reduced Returns 38%]
Architecture overview: [White-Label SDK Technical Docs]

Questions? Reply to this email (I read every response).

— Bella
Co-founder, GlamYouUp
```

---

## Educational Series Pattern

**Use when:** Multi-part email course, onboarding sequence, how-to series

**Structure:** Lesson intro → Key concept → Example → Practice/next step

### Structure Guide

**Part indicator:**
- Clear position in series (Part 2 of 5)
- Previous/next context

**Lesson structure:**
- Concept introduction (what you'll learn)
- Explanation (how it works)
- Example (real application)
- Practice (what to try)
- Next lesson preview

### Example: Fit Prediction Series (Part 2/5)

```
Subject: Part 2: Why size charts fail (Fit Prediction Series)
Preview: Generic size charts: 68% accurate. Here's why—and what works.

---

Hey [Name],

Part 2 of our fit prediction series. Last time: Why 73% of returns are 
fit issues. Today: Why size charts don't work.

Quick recap: Fashion returns cost $743B annually. 73% are fit issues, 
not buyer's remorse. Problem: Generic size charts are only 68% accurate.

Let's explore why—and what accuracy threshold luxury brands need.

---

**Why Generic Size Charts Fail**

Size charts are based on population averages. Problem: Nobody is average.

**Example: "Medium" dress**

Generic size chart:
- Bust: 36-38"
- Waist: 28-30"
- Hips: 38-40"

Assumes proportions scale together. Reality: They don't.

Customer A (fits "Medium" bust): 37" bust, 26" waist, 41" hips
Customer B (fits "Medium" waist): 39" bust, 29" waist, 37" hips

Both are "Medium" by one measurement. Wrong size by others.

**Accuracy breakdown:**

We analyzed 10,000 purchases:
- Generic size charts: 68% accurate
- Virtual try-on (single-angle): 72% accurate
- Body scanning (multi-point): 94% accurate

Luxury threshold: >90% accuracy to build trust.

**What Works: Personalized Fit Prediction**

Instead of "What size is Medium?", ask: "What size fits this body?"

Approach:
1. Measure customer body (height, weight, shape)
2. Compare to garment fit data (measurements per size)
3. Predict best size (personalized, not generic)

Result: 94% accuracy (trained on 10M+ body scans)

**Try This:**

Next time you shop online, note: Does site use generic size chart or 
personalized recommendations?

Generic: "Size M fits bust 36-38""
Personalized: "Based on your measurements, size M will fit"

Difference: Generic assumes you know your measurements. Personalized 
computes fit for you.

---

**Next: Part 3 - How Body Scanning Achieves 94% Accuracy**

We'll cover:
- Multi-point measurement approach
- ML training on 10M+ body scans
- Why single-angle virtual try-on tops out at 72%

Coming Wednesday.

— Bella
Co-founder, GlamYouUp
```

---

## Email Quality Standards

**Good email:**
- Personal voice (real person, not corporate)
- Educational focus (teaching, not selling)
- Scannable structure (sections, headers, lists)
- Specific value (data, examples, insights)
- Soft link (docs, content, not sales page)

**Bad email:**
- Generic corporate tone
- Sales pitch disguised as content
- Wall of text (no structure)
- Vague claims ("learn more", "discover")
- Multiple CTAs ("Book demo!", "Try now!")

---

## Common Mistakes

### ❌ Subject Line Clickbait

**Wrong:**
```
Subject: You won't believe what we just launched!
```

**Right:**
```
Subject: White-label SDK now available for enterprise
```

### ❌ Sales Pitch Disguised as Content

**Wrong:**
```
Our revolutionary AI-powered solution transforms fashion e-commerce!
Book a demo to see the magic! Limited time offer!
```

**Right:**
```
We analyzed 10,000 returns. 73% were fit issues, not buyer's remorse.
Here's what size chart accuracy tells us: [link to analysis]
```

### ❌ Generic Corporate Voice

**Wrong:**
```
Dear Valued Customer,

We are excited to announce...

Sincerely,
The GlamYouUp Team
```

**Right:**
```
Hey [Name],

We closed 5 deals in Q4. All picked white-label over co-branded.
Not what we expected. Here's what we learned...

— Bella
Co-founder, GlamYouUp
```

### ❌ Multiple CTAs

**Wrong:**
```
Book a demo! Try free trial! Download white paper! Subscribe for updates!
```

**Right:**
```
Technical docs: [Integration Guide]

Questions? Reply to this email.
```

---

## Quality Checklist

Before sending:

- [ ] **Subject:** Specific value (not clickbait)
- [ ] **Opening:** Personal, contextual (not generic greeting)
- [ ] **Tone:** Educational (not promotional)
- [ ] **Structure:** Scannable (sections, headers)
- [ ] **Content:** Specific data/examples (not vague)
- [ ] **Links:** Soft links to content (not hard CTAs)
- [ ] **Signature:** Real person (not "The Team")
- [ ] **Length:** 400-600 words (scannable in 2-3 min)

---

## Remember

Emails are curated knowledge delivery, not sales pitches.

Good email = Personal voice + Educational content + Scannable structure + Soft links

Success = Readers learn something useful every time
```


<!-- FILE: content-generation/references/pattern-principles.md -->

# content-generation/references/pattern-principles.md

```markdown
# Content Pattern Principles

Patterns are structure guides, not rigid templates.

## What Patterns Are

**Patterns provide:**
- Core structure (problem → solution → result)
- Opening approaches (5-7 examples per pattern)
- Transition techniques (how to move between sections)
- Length ranges (guidance, not requirements)
- Common pitfalls (what to avoid)

**Patterns do NOT provide:**
- Exact word counts (flexibility for content)
- Fill-in-the-blank templates (requires thinking)
- Prescribed phrasing (use natural language)
- Step-by-step scripts (adapt to context)

## How to Use Patterns

### 1. Select Pattern Based on Purpose

**Problem Analysis Pattern:**
- Use when: Explaining industry problem, sharing research, analyzing trends
- Structure: Problem → Data → Analysis → Implication
- Example: "Why 70% of Fashion Returns Are Fit Issues"

**Implementation Guide Pattern:**
- Use when: Teaching how to solve problem, technical tutorial
- Structure: Challenge → Approach → Implementation → Results
- Example: "Building Real-Time Fit Recommendations with React SDK"

**Case Study Pattern:**
- Use when: Sharing customer success, validating approach
- Structure: Customer → Problem → Solution → Results
- Example: "How ElsaAI Reduced Returns 38% with White-Label SDK"

**Announcement Pattern:**
- Use when: Launching product/feature, major milestone
- Structure: What → Why → How → Who → When
- Example: "White-Label SDK Now Available for Enterprise"

**LinkedIn Insight Pattern:**
- Use when: Sharing business learning, industry observation
- Structure: Insight → Analysis → Implication
- Example: "100% of Luxury Brands Chose White-Label Over Co-Branded"

### 2. Adapt Structure to Content

**Pattern gives skeleton, not script:**

Pattern says:
```
Introduction (100-150 words)
- Problem context
- Why it matters
- What reader will learn
```

You write:
```
When we launched our SDK, we assumed enterprise brands would prefer 
co-branded widgets. After 5 deals, we learned we were wrong.

100% of luxury brands ($100M+ GMV) chose white-label. This wasn't 
about hiding our technology—it was about brand consistency being 
non-negotiable in luxury e-commerce.

Here's what $5.5M in contracts taught us about brand positioning.
```

**Use pattern as guide, not script.**

### 3. Apply Brand Voice

**Pattern provides structure. Voice provides tone.**

Every pattern follows brand voice:
- **Educational:** Teach, don't sell
- **Data-driven:** Specific metrics, not vague claims
- **Technical:** Include architecture, methodology
- **Honest:** Admit uncertainties, limitations
- **No sales language:** No buzzwords, CTAs, engagement tricks

**Example:**

❌ Template-following (wrong):
```
Our revolutionary AI-powered solution leverages cutting-edge 
machine learning to dramatically improve customer satisfaction.
Book a demo to see the magic!
```

✅ Pattern + Voice (right):
```
We trained our fit model on 10M+ body scans. Accuracy went from 
68% (generic size charts) to 94% (personalized recommendations).

The challenge: luxury customers expect >90% accuracy. At 94%, 
we cross the credibility threshold. Below 90%, returns stay high.
```

### 4. Include Technical Depth

**Patterns guide structure. Depth builds credibility.**

Each pattern requires technical details:
- Architecture approaches
- Methodology explanations
- Performance specifications
- Implementation challenges

**Example from case study:**

Pattern says: "Technical Details (200-300 words)"

You write:
```
## Technical Details

**Architecture:**
- SDK loaded asynchronously (no page speed impact)
- Body measurement API: <200ms latency
- Recommendation cache: 99.9% uptime
- Analytics dashboard: Real-time fit data

**Challenges overcome:**
1. Brand consistency: Custom CSS matching ElsaAI design system
2. Mobile performance: Lazy loading prevented slowdown
3. Data privacy: GDPR-compliant body measurement storage

**Why it worked:**
- White-label removed trust friction
- 94% accuracy exceeded luxury threshold
- Fast integration minimized engineering burden
```

### 5. Use Source Material

**Patterns provide structure. Threads provide content.**

All content comes from:
- Thread learning (facts, metrics, insights)
- Canvas positioning (value proposition, problem)
- Sales narratives (customer language, pain points)
- Brand voice guidelines (tone, style)

**Never invent:**
- Customer names (check thread for approval)
- Metrics (use exact numbers from threads)
- Technical details (match thread specifications)
- Customer quotes (use verbatim or don't include)

## Pattern Selection Matrix

| Content Goal | Pattern | Length | Depth |
|--------------|---------|--------|-------|
| Explain problem | Problem Analysis | 800-1,200 | Medium |
| Teach solution | Implementation Guide | 1,200-2,000 | High |
| Share success | Case Study | 1,000-1,500 | High |
| Launch product | Announcement | 400-700 | Low |
| Quick insight | LinkedIn Post | 300-600 | Medium |
| Curated update | Newsletter | 400-600 | Low |

## Common Mistakes

### ❌ Following Pattern Too Rigidly

**Wrong:**
```
Introduction (exactly 150 words)
The problem with fashion returns is... [fills exactly 150 words 
even if unnatural]
```

**Right:**
```
When we launched, we assumed brands wanted co-branded widgets. 
We were wrong. [Natural length, ~30 words]
```

### ❌ Skipping Technical Depth

**Wrong:**
```
We used AI to improve fit recommendations. It worked well.
```

**Right:**
```
We trained our model on 10M+ body scans. Accuracy: 94% vs 68% 
baseline. Challenge: luxury customers expect >90% accuracy to trust.
```

### ❌ Adding Sales Language

**Wrong:**
```
Our revolutionary solution delivers unprecedented results! 
Book a demo today!
```

**Right:**
```
White-label SDK available for enterprise brands ($400K+ tier). 
Technical docs: [link]
```

### ❌ Inventing Data

**Wrong:**
```
Many customers saw significant improvements in conversion rates.
```

**Right:**
```
ElsaAI: Return rate 25% → 18% (28% reduction). Mobile conversion +12%.
[Sources from threads/sales/elsa-white-label/6-learning.md]
```

## Quality Checklist

Before completing draft:

- [ ] **Structure:** Follows pattern guide (not template)
- [ ] **Voice:** Educational, technical, data-driven (no sales language)
- [ ] **Depth:** Includes architecture, methodology, challenges
- [ ] **Accuracy:** All metrics from threads (no invented data)
- [ ] **Source:** All claims traceable to threads/Canvas
- [ ] **Length:** Within range for pattern (flexible)
- [ ] **Approval:** Customer names checked for public use

## Remember

**Patterns are guides, not scripts.**

Good content = Pattern structure + Brand voice + Technical depth + Thread facts

Success = Educational content that builds authority organically.
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

