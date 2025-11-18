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