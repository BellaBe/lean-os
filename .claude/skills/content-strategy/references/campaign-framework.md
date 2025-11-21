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
Example: DTC segment ready → Create awareness campaign on fit problems
When content-strategy suggests this:

Sales thread shows ICP validated
Prospects identified (qualified list exists)
Need to educate market on problem
SEO keywords identified (top-of-funnel)

2. Education Campaign
Trigger: Strategic insight, market trend, thought leadership opportunity
Goal: Build authority, shift market thinking
Content: 2-3 deep-dive articles + 4-6 LinkedIn posts
Timeline: 3-4 weeks
Example: Body shape insight → Education campaign challenging conventional wisdom
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
Example: White-label SDK launched → Launch campaign
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
Example: 5 luxury brands achieved 38% return reduction → Case study campaign
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
Thread: threads/sales/dtc-segment-validation/6-learning.md
markdown# Learning

**Validated:** DTC fashion segment is ready for outreach
- ICP: DTC brands ($10M-$50M GMV), high return rates (>25%)
- Prospects: 191 qualified companies identified
- Common objection: "Return problem is unsolved, we've tried everything"

**Implication:** Need awareness content to educate on fit technology approach

**Canvas update:** H3 validated (DTC segment matches ICP criteria)
content-strategy detects:

Trigger: Segment ready (ICP validated + prospects identified)
Campaign type: Awareness
Goal: Generate 25 inbound demos from organic
Content: 3 articles on fit problems (educational, SEO-focused)
Impact score: 0.78 (high reach, medium conversion)

Suggests:
markdown[Impact: 0.78] DTC Product Awareness Campaign
- Type: Awareness (educational content)
- Trigger: DTC segment ready (ICP validated, 191 prospects)
- Goal: 25 demos from organic (3,000 sessions target)
- Content: 3 blog articles + 6 LinkedIn posts
- Timeline: 3 weeks to create, 60 days to measure
- Action: Create campaign thread at threads/marketing/campaigns/dtc-awareness-nov-2024/?
Validation Campaign Example
Threads:

threads/sales/elsa-white-label/6-learning.md
threads/sales/luxury-brand-2/6-learning.md
threads/sales/luxury-brand-3/6-learning.md
threads/sales/luxury-brand-4/6-learning.md
threads/sales/luxury-brand-5/6-learning.md

Pattern detected:
markdownAll 5 luxury brands ($100M+ GMV) chose white-label SDK over co-branded:
- ElsaAI: 38% return reduction, $805K savings
- Brand 2: 42% return reduction, $1.2M savings
- Brand 3: 35% return reduction, $650K savings
- Brand 4: 40% return reduction, $900K savings
- Brand 5: 37% return reduction, $750K savings

Average: 38.4% return reduction, $861K annual savings
Pattern: 100% chose white-label (not co-branded)
content-strategy detects:

Trigger: Deal patterns (5 deals, 100% pattern)
Campaign type: Validation (case studies)
Goal: Generate 20 inbound demos from proof
Content: 2 case studies + 4 LinkedIn posts
Impact score: 0.85 (medium reach, high conversion)

Suggests:
markdown[Impact: 0.85] Luxury White-Label Validation Campaign
- Type: Validation (case studies + proof)
- Trigger: 5 luxury brands chose white-label (100% pattern)
- Goal: 20 demos from organic (2,000 sessions target)
- Content: 2 case studies + 4 LinkedIn posts
- Timeline: 2 weeks to create, 30 days to measure
- Action: Create campaign thread at threads/marketing/campaigns/luxury-validation-nov-2024/?
Launch Campaign Example
Thread: threads/business/color-analysis-launch/6-learning.md
markdown# Learning

**Feature complete:** AI color analysis for skin tone matching
- Technical validation: 95% accuracy on test dataset
- Customer beta: 3 customers testing (positive feedback)
- Ready for public launch: Week of Nov 18

**Implication:** Launch campaign needed for existing customer adoption + awareness
content-strategy detects:

Trigger: Product launch (new feature ready)
Campaign type: Launch
Goal: 10 demos + 50 existing customer adoptions
Content: 1 announcement + 3 LinkedIn posts + 1 email
Impact score: 0.68 (low reach, but strategic)

Suggests:
markdown[Impact: 0.68] Color Analysis Feature Launch
- Type: Launch (announcement + adoption)
- Trigger: Color analysis feature launching (Week of Nov 18)
- Goal: 10 demos + 50 existing customer adoptions
- Content: 1 announcement + 3 LinkedIn posts + 1 email
- Timeline: 1 week to create, 14 days to measure
- Action: Defer until launch date confirmed?
Education Campaign Example
Thread: threads/business/body-shape-insight/6-learning.md
markdown# Learning

**Insight validated:** Body shape predicts fit better than measurements
- Our data: 94% accuracy with body shape vs 72% with measurements
- Industry assumption: Measurements are sufficient
- Non-obvious: Shape matters more than size

**Implication:** This challenges industry conventional wisdom
- Opportunity for thought leadership
- Educational content to shift market thinking
content-strategy detects:

Trigger: Strategic insight (non-obvious, contrarian)
Campaign type: Education (thought leadership)
Goal: Build authority, shift market perception
Content: 1 deep-dive article (2,500w) + 4 LinkedIn posts
Impact score: 0.72 (medium reach, medium conversion)

Suggests:
markdown[Impact: 0.72] Body Shape vs Measurements Education Campaign
- Type: Education (thought leadership)
- Trigger: Body shape insight validated (challenges industry wisdom)
- Goal: Build authority, 15 demos from technical audience
- Content: 1 deep-dive article (2,500w) + 4 LinkedIn posts
- Timeline: 3 weeks to create, 60 days to measure
- Action: Create campaign thread at threads/marketing/campaigns/body-shape-education-nov-2024/?

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