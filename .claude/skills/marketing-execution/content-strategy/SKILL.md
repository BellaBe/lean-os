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