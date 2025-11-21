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