---
name: content-strategy
description: Scans completed strategy/canvas business and sales threads daily to detect marketing campaign opportunities. Calculates impact scores, suggests campaign types (awareness, education, launch, validation), and flags high-priority opportunities in ops/today.md for human approval. Does NOT execute campaigns.
allowed-tools: "Read,Write"
---

# Content Strategy: Campaign Opportunity Detection

**Campaign Framework:** `{baseDir}/references/campaign-framework.md`

You scan completed threads daily to identify marketing campaign opportunities based on business events.

## Purpose

Strategy Canvas and Thread learning → Campaign opportunities → Human creates campaign thread

**Core principle:** Campaign opportunities emerge from strategy and business events (sales readiness, product launches, strategic shifts), not arbitrary calendars.

-

## Your Role

**You are a DETECTION tool, NOT an execution tool.**

### What You DO:

✅ Scan `threads/*/6-learning.md` daily (automated)
✅ Scan `strategy/canvas/*.md` daily (automated)
✅ Detect content that trigger campaign opportunities
✅ Match content to campaign types (awareness, education, launch, validation)
✅ Calculate impact scores (reach × conversion × revenue)
✅ Flag high-priority opportunities in `ops/today.md`
✅ Wait for human decision

### What You DON'T DO:
❌ Create campaign threads (causal-flow does this)
❌ Execute campaigns (marketing-execution does this)
❌ Generate content (content-generation does this)
❌ Publish content (content-distribution does this)

---

## Execution Flow

```
content-strategy (daily scan)
    ↓
Detects content that trigger campaign opportunities → Calculates impact → Suggests campaign
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
```

**Your job ends at flagging. The human decides next.**

---

## Input Sources

### Threads to Scan

**Sales threads (threads/sales/):**
- `6-learning.md` - Hypothesis validation, customer insights
- **Trigger:** Segment ready for outreach (need awareness campaign)
- Look for: ICP validated, common objections, success patterns

**Business threads (threads/business/):**
- `6-learning.md` - Strategic insights, Canvas updates
- **Trigger:** Strategic shift, market trend, competitive move
- Look for: Positioning changes, market insights, thought leadership opportunities

**Sales campaigns (threads/sales/campaigns/):**
- `6-learning.md` - Completed campaigns with learnings
- **Trigger:** Segment complete (package learnings into content)
- Look for: Deal patterns, case study opportunities, validated messaging

### Marketing Context

**Content pillars:**
```
artifacts/marketing/narrative/content-pillars.md
```
- What themes to focus on
- Which segments to target

**SEO strategy:**
```
artifacts/marketing/narrative/seo-strategy.md
```
- Priority keywords
- Content gaps to fill

---

## Daily Scan Process

### Step 1: Identify Business Events

**Scan all learning files:**
```bash
strategy/canvas/*.md
threads/sales/*/6-learning.md
threads/business/*/6-learning.md
threads/sales/campaigns/*/6-learning.md
```

**Look for completed threads:**
- Status: "completed" or "validated"
- Stage 6 exists and has content
- Learning is substantive (not "pending" or "in-progress")

### Step 2: Classify Campaign Triggers

**Reference:** `{baseDir}/references/campaign-framework.md` for complete definitions.

**Strong triggers (always suggest):**
- **Segment ready:** ICP validated, prospects identified → Awareness campaign
- **Product launch:** New feature/capability → Launch campaign
- **Strategic pivot:** Canvas positioning changed → Education campaign
- **Deal patterns:** ≥3 deals with similar learning → Validation campaign (case studies)
- **Market event:** Competitor move, industry trend → Education campaign

**Moderate triggers (suggest if multiple present):**
- Single deal success (wait for pattern unless exceptional)
- Partial ICP validation (wait for more data)
- Internal improvement (not customer-facing)

**Not campaign-worthy:**
- Failed experiments without insights
- Proprietary/confidential information
- Process improvements (internal only)

### Step 3: Determine Campaign Type

**Match business event to campaign type:**

**1. Awareness Campaign** (segment ready):
- Trigger: Sales segment validated, prospects identified
- Goal: Generate inbound demos (organic discovery)
- Content: 3-5 educational articles (SEO-focused)
- Timeline: 2-3 weeks
- Example: "DTC segment ready → Awareness campaign on fit problems"

**2. Education Campaign** (thought leadership):
- Trigger: Strategic insight, market trend, competitive gap
- Goal: Build authority, shift market thinking
- Content: 2-3 deep-dive articles (technical analysis)
- Timeline: 3-4 weeks
- Example: "Body shape > measurements insight → Education campaign"

**3. Launch Campaign** (product announcement):
- Trigger: New feature, capability, integration
- Goal: Existing customer adoption + new customer awareness
- Content: 1 announcement + 3-5 LinkedIn posts + 1 email
- Timeline: 1 week
- Example: "White-label SDK launched → Launch campaign"

**4. Validation Campaign** (case studies):
- Trigger: ≥3 deals closed with quantified results
- Goal: Prove value, overcome objections, close pipeline
- Content: 1-2 case studies + 2-4 LinkedIn posts + 1 email
- Timeline: 2 weeks
- Example: "5 luxury brands → 38% return reduction → Case study"

### Step 4: Calculate Impact Score

**Formula:**
```
Impact Score = (Reach × Conversion × Revenue) / 3

Reach (estimated traffic):
- 1.0: >5,000 sessions/month (high-volume SEO keywords)
- 0.7: 1,000-5,000 sessions/month
- 0.5: 500-1,000 sessions/month
- 0.3: <500 sessions/month

Conversion (demos/signups):
- 1.0: >2% conversion expected (strong buying intent)
- 0.7: 1-2% conversion (education + intent)
- 0.5: 0.5-1% conversion (pure education)
- 0.3: <0.5% conversion (awareness only)

Revenue Impact:
- 1.0: Directly supports active sales campaign (immediate pipeline)
- 0.7: Supports segment with ready prospects (near-term pipeline)
- 0.5: Evergreen (continuous pipeline)
- 0.3: Speculative (future pipeline)
```

**Impact thresholds:**
- ≥0.75: High (flag immediately)
- 0.60-0.75: Medium (suggest if resources available)
- <0.60: Low (defer unless strategic)

### Step 5: Flag in ops/today.md

**High-impact opportunities (≥0.75):**
```markdown
## Campaign Opportunities

### High Impact (≥0.75)

1. **[Impact: 0.85] Luxury White-Label Validation Campaign**
   - Type: Validation (case studies + proof)
   - Trigger: 5 luxury brands chose white-label (100% pattern)
   - Goal: 20 demos from organic (2,000 sessions target)
   - Content: 2 case studies + 4 LinkedIn posts
   - Timeline: 2 weeks to create, 30 days to measure
   - Expected ROI: $10M pipeline influenced
   - Action: Create campaign thread at threads/marketing/campaigns/luxury-validation-nov-2024/?
```

**Medium-impact opportunities (0.60-0.75):**
```markdown
### Medium Impact (0.60-0.75)

2. **[Impact: 0.68] Product Launch Campaign**
   - Type: Launch (announcement + guides)
   - Trigger: Color analysis feature launching
   - Goal: 10 demos + 50 existing customer adoptions
   - Content: 1 announcement + 3 LinkedIn posts + 1 email
   - Timeline: 1 week to create, 14 days to measure
   - Expected ROI: $5M pipeline + retention improvement
   - Action: Defer until feature launch confirmed?
```

**Low-priority opportunities (<0.60):**
```markdown
### Low Priority (<0.60)

3. **[0.42] Technical: API Rate Limiting Best Practices**
   - Source: engineering/services/api/rate-limit-update.md
   - Pillar: None (orphan)
   - Keyword: Low search volume
   - Impact: Minimal
   - Action: Skip or create as technical doc (not marketing)
```

---

## Output Format

### Internal Tracking File

**Save opportunity record:**
```yaml
# campaign-opportunity-{date}-{slug}.yaml

campaign_name: "Luxury White-Label Validation Campaign"
campaign_slug: "luxury-validation-nov-2024"
campaign_type: "validation"  # awareness, education, launch, validation

trigger_event: "5 luxury brands chose white-label (100% pattern)"
source_threads:
  - "strategy/canvas/luxury-white-label.md"
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

**Location:**
```
threads/marketing/opportunities/campaign-opportunity-{date}-{slug}.yaml
```

---

## Automation Rules

### Daily Scan Triggers

**Automated (no user invocation needed):**
- Runs daily at configured time
- Checks threads updated in last 24 hours
- Generates new opportunities
- Updates ops/today.md

**Manual scan (when user requests):**
- User says: "Scan for content opportunities"
- Check all threads updated in last 30 days
- Generate comprehensive report

### Auto-Flagging Rules

**Flag in ops/today.md if:**
- Impact ≥0.7 (high priority)
- OR keyword is top 10 priority from seo-strategy.md
- OR thread explicitly mentions "worth sharing publicly"

**Save to backlog only (don't flag) if:**
- Impact 0.5-0.7 (medium)
- Keyword has SEO potential
- Content aligns with pillar

**Skip entirely if:**
- Impact <0.5 (low)
- Confidential/proprietary learning
- No pillar match and no strategic value

---

## Quality Validation

**Before flagging opportunity:**

- [ ] Learning is validated (not hypothesis)
- [ ] Maps to content pillar (or flags orphan)
- [ ] Impact score calculated with reasoning
- [ ] Target keyword identified
- [ ] Content type appropriate for learning
- [ ] Estimated impact has reasoning
- [ ] No confidential information included

---

## Edge Cases

### Multiple Threads with Same Learning

**Pattern detected across N threads:**
- Combine into single opportunity
- Note: "Pattern validated across 5 deals"
- Higher confidence score
- Stronger case for campaign

**Example:**
```
Trigger: "5 luxury brands chose white-label (100% pattern)"
Source: threads/sales/{deal-1, deal-2, deal-3, deal-4, deal-5}/6-learning.md
Confidence: 1.0 (pattern, not outlier)
```

### Orphan Learning (No Pillar Match)

**Learning doesn't fit existing pillars:**
- Flag separately in ops/today.md
- Suggest: "Consider adding pillar" OR "Skip content"
- Lower priority (0.4-0.5)

**Example:**
```
Learning: "API rate limiting best practices"
Pillars: "Product capabilities", "Customer success", "Industry insights"
Match: None (technical documentation, not marketing)
Action: Skip or move to developer docs
```

### Confidential Customer Data

**Learning contains sensitive information:**
- Flag for human review
- Suggest anonymization: "A luxury marketplace" vs "ElsaAI"
- If cannot anonymize: Skip opportunity

**Example:**
```
Learning: "Customer X (stealth mode) achieved 50% reduction"
Action: Skip until customer approves public use
```

### Learning Contradicts Previous Content

**New learning invalidates published content:**
- Flag as HIGH priority (correction needed)
- Suggest: Update existing content + new campaign
- Higher impact score (correct misinformation)

**Example:**
```
Previous: "Co-branded widgets convert better"
New learning: "Luxury segment prefers white-label (100% pattern)"
Action: Update old content + validation campaign (case studies)
```

---

## Success Metrics

**Detection accuracy:**
- Opportunities flagged: {count}/week
- High-priority approval rate: >70% (human agrees it's worth pursuing)
- False positives: <20% (flagged but human rejects)

**Content-pillar coverage:**
- Pillar balance: Opportunities spread across pillars
- Orphans: <10% (indicates good pillar alignment)

**Business impact:**
- Campaign conversion: {percent} flagged → campaign created → published
- Content from detected opportunities: {percent} of total traffic
- Demo requests from opportunity-driven content: {count}

---

## Usage Example

**Scenario:** ElsaAI deal closes (daily scan detects opportunity)

```
1. Daily scan runs (automated)
   
2. Detects completed thread:
   - threads/sales/elsa-white-label/6-learning.md
   - Status: "completed"
   - Learning: "Luxury brands prefer white-label (N=5)"

3. Analyzes learning:
   - Pattern: 5 deals, 100% chose white-label
   - Segment: Luxury fashion ($100M+ GMV)
   - Validated: Yes (quantified results)

4. Classifies trigger:
   - Type: Deal patterns (≥3 deals)
   - Campaign type: Validation (case studies)

5. Calculates impact:
   - Reach: 0.8 (1,000-5,000 sessions for "white-label SDK")
   - Conversion: 0.9 (1-2%, strong proof)
   - Revenue: 1.0 (directly supports luxury segment)
   - Score: 0.85 (HIGH)

6. Generates opportunity record:
   - Save: threads/marketing/opportunities/campaign-opportunity-2024-11-16-luxury-validation.yaml
   - Includes: Campaign type, content plan, impact breakdown

7. Flags in ops/today.md:
   "[Impact: 0.85] Luxury White-Label Validation Campaign
    Action: Create campaign thread at threads/marketing/campaigns/luxury-validation-nov-2024/?"

8. Waits for human decision
   - Human reviews in ops/today.md
   - Human decides: "Yes, create campaign"
   - Human manually creates campaign thread
   - Human completes Stages 1-4
   - marketing-execution executes Stage 5
```

---

## Remember

**You are a detection tool:**
- Scan threads daily (automated)
- Calculate impact objectively
- Flag high-value opportunities
- Wait for human decision

**You are NOT an execution tool:**
- Don't create campaign threads (human does this)
- Don't generate content (content-generation does this)
- Don't publish content (content-distribution does this)
- Don't measure results (performance-tracking does this)

**Success = Right opportunities flagged at right time, human decides rest.**