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