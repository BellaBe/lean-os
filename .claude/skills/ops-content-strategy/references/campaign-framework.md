Marketing Campaign Framework
Overview
All marketing content is created as part of campaigns. Campaigns follow 6-stage causal-flow and are decision threads in threads/marketing/campaigns/.
This framework defines campaign types, triggers, and workflows for content-strategy to detect opportunities.

Campaign Types
1. Awareness Campaign
Trigger: Sales segment validated, prospects identified
Goal: Generate inbound demos via organic discovery
Content: 3-5 educational blog articles + 6-10 LinkedIn posts
Timeline: 2-3 weeks
Example: {Segment} ready → Create awareness campaign on {problem area}
When content-strategy suggests this:

Sales thread shows ICP validated
Prospects identified (qualified list exists)
Need to educate market on {problem area}
SEO keywords identified (top-of-funnel)

2. Education Campaign
Trigger: Strategic insight, market trend, thought leadership opportunity
Goal: Build authority, shift market thinking
Content: 2-3 deep-dive articles + 4-6 LinkedIn posts
Timeline: 3-4 weeks
Example: {Strategic insight} → Education campaign challenging conventional wisdom
When content-strategy suggests this:

Business thread shows non-obvious insight
Market trend detected (competitor move, regulation change)
Contrarian positioning validated
Opportunity for thought leadership

3. Launch Campaign
Trigger: New feature, capability, integration
Goal: Customer adoption + new customer awareness
Content: 1 announcement + 3-5 LinkedIn posts + 1 email
Timeline: 1 week
Example: {New feature} launched → Launch campaign
When content-strategy suggests this:

Product thread shows feature ready for launch
Existing customers need notification
New capability worth announcing publicly
Fast execution needed (1 week timeline)

4. Validation Campaign
Trigger: ≥3 deals closed with quantified results
Goal: Prove value, overcome objections
Content: 1-2 case studies + 2-4 LinkedIn posts + 1 email
Timeline: 2 weeks
Example: 5 {customer segment} achieved {metric}% {outcome} improvement → Case study campaign
When content-strategy suggests this:

Pattern detected: ≥3 deals with similar results
Quantified metrics available (before/after)
Customer approval obtained (or obtainable)
Strong proof for sales enablement


Campaign Workflow
Stage 1-4: Planning (Human)

content-strategy scans threads → Detects campaign opportunity → Flags in ops/today.md
Human reviews → Decides to create campaign
Human creates campaign thread → Completes Stages 1-4

Stage 1: Document trigger event
Stage 2: Link to Canvas hypothesis
Stage 3: Calculate impact (sessions → demos → revenue)
Stage 4: Define content plan (specific articles, posts, emails)



Stage 5: Execution (AI-Assisted)

marketing-execution orchestrator reads Stage 4 decision
For each content piece:

content-generation: Create draft → Save to 5-actions/drafts/
Human review: Approve or request changes
seo-optimization: Apply keywords, structure
Human approve: Final check
content-distribution: Publish to artifacts/marketing/campaigns/{slug}/
Update execution-log.md: Track progress


After all published: Delete drafts/ (content now in artifacts)

Stage 6: Learning (AI + Human)

performance-tracking monitors campaign metrics
Human writes learning:

What worked, what didn't
Canvas updates (validate/invalidate hypothesis)
Next campaign opportunities


Campaign complete


Campaign Naming Convention
Use descriptive format: {segment}-{purpose}-{month-year}
Examples:

dtc-awareness-nov-2024
luxury-validation-dec-2024
tech-education-jan-2025
sdk-launch-nov-2024


Directory Structure
threads/marketing/campaigns/{campaign-slug}/
├── metadata.yaml
├── 1-input.md        # Business event triggering campaign
├── 2-hypothesis.md   # What we believe (Canvas link)
├── 3-implication.md  # Business impact (sessions → demos → revenue)
├── 4-decision.md     # Content plan (what to produce)
├── 5-actions/
│   ├── execution-log.md  # Track content creation/publishing
│   └── drafts/           # Temporary (deleted after publishing)
└── 6-learning.md     # Results + Canvas updates

artifacts/marketing/campaigns/{campaign-slug}/
├── {content-piece}.md              # Published article
├── distribution/
│   ├── {piece}-linkedin.md         # Published LinkedIn
│   └── {piece}-twitter.md          # Published Twitter
└── distribution-record.yaml        # Tracking file

Key Principles
✅ All content is part of a campaign - No standalone content
✅ Campaigns are decision threads - Follow 6-stage causal-flow
✅ Stage 4 decides content - List specific pieces to produce
✅ Stage 5 tracks execution - execution-log.md shows progress
✅ Stage 6 measures impact - Validate hypothesis, update Canvas
✅ Drafts are temporary - Live in thread during execution, deleted after publishing
✅ Artifacts are permanent - Published content grouped by campaign

Trigger Detection Examples
Awareness Campaign Example
Thread: threads/sales/{segment}-validation/6-learning.md
markdown# Learning

**Validated:** {Customer segment} is ready for outreach
- ICP: {Segment description} (${revenue range}), {problem indicator} (>{X}%)
- Prospects: {N} qualified companies identified
- Common objection: "{Problem area} is unsolved, we've tried everything"

**Implication:** Need awareness content to educate on {solution approach}

**Canvas update:** H3 validated ({Segment} matches ICP criteria)
content-strategy detects:

Trigger: Segment ready (ICP validated + prospects identified)
Campaign type: Awareness
Goal: Generate {N} inbound demos from organic
Content: 3 articles on {problem area} (educational, SEO-focused)
Impact score: 0.78 (high reach, medium conversion)

Suggests:
markdown[Impact: 0.78] {Segment} Awareness Campaign
- Type: Awareness (educational content)
- Trigger: {Segment} ready (ICP validated, {N} prospects)
- Goal: {N} demos from organic ({sessions} sessions target)
- Content: 3 blog articles + 6 LinkedIn posts
- Timeline: 3 weeks to create, 60 days to measure
- Action: Create campaign thread at threads/marketing/campaigns/{segment}-awareness-{month-year}/?
Validation Campaign Example
Threads:

threads/sales/{customer-1}/6-learning.md
threads/sales/{customer-2}/6-learning.md
threads/sales/{customer-3}/6-learning.md
threads/sales/{customer-4}/6-learning.md
threads/sales/{customer-5}/6-learning.md

Pattern detected:
markdownAll {N} {customer segment} (${revenue range}) chose {approach A} over {approach B}:
- {Customer 1}: {X}% {metric} reduction, ${savings} savings
- {Customer 2}: {Y}% {metric} reduction, ${savings} savings
- {Customer 3}: {Z}% {metric} reduction, ${savings} savings
- {Customer 4}: {A}% {metric} reduction, ${savings} savings
- {Customer 5}: {B}% {metric} reduction, ${savings} savings

Average: {X}% {metric} reduction, ${avg savings} annual savings
Pattern: 100% chose {approach A} (not {approach B})
content-strategy detects:

Trigger: Deal patterns ({N} deals, 100% pattern)
Campaign type: Validation (case studies)
Goal: Generate {N} inbound demos from proof
Content: {N} case studies + {N} LinkedIn posts
Impact score: 0.85 (medium reach, high conversion)

Suggests:
markdown[Impact: 0.85] {Segment} {Approach} Validation Campaign
- Type: Validation (case studies + proof)
- Trigger: {N} {customer segment} chose {approach A} (100% pattern)
- Goal: {N} demos from organic ({sessions} sessions target)
- Content: {N} case studies + {N} LinkedIn posts
- Timeline: {weeks} weeks to create, {days} days to measure
- Action: Create campaign thread at threads/marketing/campaigns/{segment}-validation-{month-year}/?
Launch Campaign Example
Thread: threads/business/{feature}-launch/6-learning.md
markdown# Learning

**Feature complete:** {Feature description}
- Technical validation: {X}% accuracy on test dataset
- Customer beta: {N} customers testing (positive feedback)
- Ready for public launch: Week of {date}

**Implication:** Launch campaign needed for existing customer adoption + awareness
content-strategy detects:

Trigger: Product launch (new feature ready)
Campaign type: Launch
Goal: {N} demos + {N} existing customer adoptions
Content: 1 announcement + {N} LinkedIn posts + 1 email
Impact score: 0.68 (low reach, but strategic)

Suggests:
markdown[Impact: 0.68] {Feature} Launch
- Type: Launch (announcement + adoption)
- Trigger: {Feature} launching (Week of {date})
- Goal: {N} demos + {N} existing customer adoptions
- Content: 1 announcement + {N} LinkedIn posts + 1 email
- Timeline: 1 week to create, {days} days to measure
- Action: Defer until launch date confirmed?
Education Campaign Example
Thread: threads/business/{insight}-insight/6-learning.md
markdown# Learning

**Insight validated:** {Contrarian insight statement}
- Our data: {X}% accuracy with {approach A} vs {Y}% with {approach B}
- Industry assumption: {Conventional wisdom}
- Non-obvious: {Why it matters}

**Implication:** This challenges industry conventional wisdom
- Opportunity for thought leadership
- Educational content to shift market thinking
content-strategy detects:

Trigger: Strategic insight (non-obvious, contrarian)
Campaign type: Education (thought leadership)
Goal: Build authority, shift market perception
Content: 1 deep-dive article ({words}w) + {N} LinkedIn posts
Impact score: 0.72 (medium reach, medium conversion)

Suggests:
markdown[Impact: 0.72] {Insight Topic} Education Campaign
- Type: Education (thought leadership)
- Trigger: {Insight} validated (challenges industry wisdom)
- Goal: Build authority, {N} demos from technical audience
- Content: 1 deep-dive article ({words}w) + {N} LinkedIn posts
- Timeline: {weeks} weeks to create, {days} days to measure
- Action: Create campaign thread at threads/marketing/campaigns/{topic}-education-{month-year}/?

Impact Score Calculation
Formula:
Impact Score = (Reach × Conversion × Revenue) / 3
Reach (estimated traffic):

1.0: >5,000 sessions/month (high-volume SEO keywords)
0.7: 1,000-5,000 sessions/month
0.5: 500-1,000 sessions/month
0.3: <500 sessions/month

Conversion (demos/signups):

1.0: >2% conversion expected (strong buying intent)
0.7: 1-2% conversion (education + intent)
0.5: 0.5-1% conversion (pure education)
0.3: <0.5% conversion (awareness only)

Revenue Impact:

1.0: Directly supports active sales campaign (immediate pipeline)
0.7: Supports segment with ready prospects (near-term pipeline)
0.5: Evergreen (continuous pipeline)
0.3: Speculative (future pipeline)

Thresholds:

≥0.75: High priority (flag immediately)
0.60-0.75: Medium priority (suggest if resources available)
<0.60: Low priority (defer unless strategic)


Related Skills

content-strategy - Uses this framework to detect opportunities
marketing-execution - Executes campaigns (Stage 5)
content-generation - Creates content drafts
seo-optimization - Applies SEO to content
content-distribution - Publishes to channels
performance-tracking - Measures campaign results


Last updated: 2025-11-21
Used by: content-strategy skill for opportunity detection