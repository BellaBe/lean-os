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
