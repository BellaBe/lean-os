# Marketing Workflow

Marketing is **learning-driven, not calendar-driven**. Content is created when business generates insights worth sharing.

## Phase 1: Strategy (Once Per Product)

### Generate Marketing Narrative

```
Skill: marketing-narrative
Input: Canvas + Sales narratives (all segments)
Output: artifacts/marketing/narrative/
  ├── content-pillars.md (3-5 strategic themes)
  ├── seo-strategy.md (keywords by funnel stage)
  ├── brand-voice.md (educational tone)
  └── channel-guidelines.md (format specs)
```

**Content pillars align with Canvas UVP:**
- Pillar 1: Core value proposition
- Pillar 2: Product capabilities
- Pillar 3: Industry insights

**SEO strategy by funnel:**
- TOFU: Problem-focused keywords
- MOFU: Solution-focused keywords
- BOFU: Product-focused keywords

**Brand voice:**
- Educational, not promotional
- Technical depth included
- Data-driven (specific metrics)
- No sales CTAs in content

**Channel guidelines:**
- Blog: 800-2,500 words, SEO-optimized
- LinkedIn: 300-600 words, professional tone
- Email: 400-600 words, segmented
- Website: Scannable, conversion-focused

---

## Phase 2: Content Execution (Thread-Driven)

### Trigger: Sales Learning

```
Sales thread completes Stage 6 (Learning)
    ↓
marketing-execution/content-strategy scans thread
    ↓
Opportunity detected (if priority ≥0.7)
    ↓
Flag in ops/today.md for approval
    ↓
Human approves
    ↓
Marketing thread created
```

### Marketing Campaign Thread

```
threads/marketing/campaigns/{campaign-slug}/
├── metadata.yaml
├── 1-input.md (business event triggering content)
├── 2-hypothesis.md (content performance hypothesis)
├── 3-implication.md (expected impact)
├── 4-decision.md (content plan)
├── 5-actions/ (execution workflow)
│   ├── execution-log.md
│   └── drafts/ (temp, deleted after publishing)
└── 6-learning.md (campaign results)
```

### Stage 5: ACTIONS (Content Workflow)

For each content piece:

**marketing:create**
- AI generates draft (1,000-2,500 words)
- Saves to 5-actions/drafts/{piece}-draft.md
- Flags in ops/today.md for review

**Human review (30 min)**
- Check technical accuracy
- Verify metrics/case studies
- Approve for publication

**marketing:publish**
- AI optimizes SEO
- AI publishes multi-channel
- AI adds UTM tracking

**marketing:promote**
- AI schedules cross-channel posts
- Days 2, 9, 16 promotion cadence

**marketing:measure**
- Day 7: Initial performance
- Day 30: Campaign results
- Day 90: Long-term impact

### Stage 6: LEARNING (Campaign Results)

Capture performance metrics:
- Total sessions
- Total demos
- Conversion rate
- Top performer analysis
- Pipeline influenced

Validate hypothesis:
- Content type performance (case study vs guide)
- Update Canvas assumptions
- Detect new opportunities

**Example:**
```
Campaign: luxury-validation-nov-2024
Performance (30 days):
- Sessions: 1,800 (90% of target)
- Demos: 15 (75% of target)
- Conversion: 0.83%
- Pipeline: $7.5M attributed

Hypothesis:
H1: Case studies convert better → VALIDATED (0.83% vs 0.6% = 38% lift)
Confidence: 95%

New opportunity:
Follow-up content: "White-label SDK implementation guide"
Priority: 0.72
```

---

## Marketing Execution Subskills

### content-strategy
- **Scans:** All completed threads (daily)
- **Detects:** Validated hypotheses, quantified results, patterns
- **Outputs:** Prioritized content opportunities
- **Triggers:** Flags high-priority (≥0.7) in ops/today.md

### content-generation
- **Input:** Content opportunity + source thread
- **Process:** Creates draft using content patterns
- **Output:** Educational draft (blog, case study, guide)
- **Human review:** Technical accuracy verification

### seo-optimization
- **Input:** Draft content + target keyword
- **Process:** Optimize title, meta, H1/H2, keywords, internal links
- **Output:** SEO-optimized content
- **No human review:** Automated

### content-distribution
- **Input:** Optimized content + distribution plan
- **Process:** Publish to blog/LinkedIn/email
- **Output:** Published content with UTM tracking
- **Human approval:** Final check before publication

### performance-tracking
- **Input:** Published content URLs + analytics data
- **Schedule:** Day 7, Day 30, Day 90
- **Output:** Performance reports, recommendations
- **Triggers:** Top/underperformer flags

---

## Initial Content Creation (Week 2)

Don't wait for sales learning. Create foundational content from Canvas + research:

**Educational content (problem-focused):**
- Use Canvas 05-problem.md
- Industry research data
- Customer interview insights

**Product capabilities:**
- Use Canvas 07-uvp.md, 09-solution.md
- Technical approach
- Differentiators

**Industry insights:**
- Market research
- Competitive analysis
- Trend analysis

**Goal:** 2-3 foundational pieces live when sales outreach begins.

---

## Closed-Loop Attribution

### Content → Sales

```
Marketing publishes case study
    ↓
SEO drives organic traffic
    ↓
Visitor requests demo
    ↓
Sales thread created with attribution
metadata.yaml:
  source: "marketing/content/{topic}/"
  attribution: "Blog article"
    ↓
Stage 6 tracks pipeline influenced
    ↓
Marketing performance updated
```

### Sales → Content

```
Sales closes 5 deals
    ↓
Pattern detected in Stage 6
    ↓
Content opportunity flagged
    ↓
Human approves
    ↓
Marketing thread created
    ↓
Content published
    ↓
Drives demos
    ↓
Loop continues
```

---

## Marketing Performance Metrics

### Content Creation Efficiency
- Time from thread to published: Target <7 days
- Human review time: Target <30 min/piece
- Content pieces per learning: 1-3

### Content Quality
- Technical accuracy: 100% (human-verified)
- SEO optimization: All required elements
- Brand voice compliance: Automated check

### Business Impact
- Organic sessions: Varies by keyword
- Demo conversion: Target 1-3%
- Pipeline influenced: Track attribution
- Top performer hit rate: Target >50%

---

## Integration with Engineering (Optional)

**⚠️ CONDITIONAL:** Only relevant if building technical products with backend systems.

**Engineering validates marketing claims:**

When creating technical content:
- Marketing reads from Canvas `09-solution.md` (engineering keeps this updated)
- Product capabilities already validated (engineering Stage 6 complete)
- Technical accuracy guaranteed (implementation matches description)
- No risk of marketing promising features that don't exist

**Engineering threads trigger content opportunities:**

When engineering completes features:
- Canvas `09-solution.md` updated with new capability + evidence
- content-strategy scans Canvas for product updates
- Technical content opportunities detected (new features worth explaining)
- Content created: Architecture explanations, capability deep-dives, implementation guides

**Example:**
```
Engineering: Implemented category-theoretic composition for services
→ Canvas: 09-solution.md updated "Compositional AI Architecture"
→ Marketing scan: Detects new technical capability
→ Content opportunity: "How We Built Composable Fashion AI" (priority 0.82)
→ Human approves
→ Marketing creates technical article
→ Distribution: Blog (technical founders), LinkedIn (CTOs), HN
→ Result: 45 inbound demos from CTOs building similar systems
```

**Content quality benefits from engineering:**
- **Accurate:** Features described match implementation exactly
- **Credible:** Technical claims backed by actual code
- **Timely:** Content published when feature is production-ready
- **Traceable:** Every claim links to engineering thread validation

**Tracking:**
- Engineering features documented: Count per quarter
- Technical content accuracy: 100% (engineering-validated)
- Demos from technical content: Conversion rate by topic
- Enterprise segment growth: Technical content attribution

---

## Next Steps

- Learn sales workflow: [Sales Workflow](sales-workflow.md)
- Understand 6-stage flow: [Causal Flow](causal-flow.md)
- See daily routine: [Daily Routine](daily-routine.md)
- See three-way integration: [Sales-Marketing-Engineering Loop](../integration/sales-marketing-loop.md)