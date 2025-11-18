# How It Works: Complete Operations Flow

LeanOS operates through a universal 6-stage causal flow that applies to all decisions: business, sales, and marketing.

## The 6-Stage Causal Flow (Universal)

Every decision flows through 6 stages, creating complete decision narratives with evidence-based reasoning.

### Stage 1: INPUT

**Purpose:** Capture factual observation (not opinion)

**Process:**
- Record what happened (not what you think about it)
- Include numbers, dates, names
- Link to source (email, call notes, analytics)

**Example:**
```
ElsaAI deal closed: $1.1M ARR, 38% return reduction achieved
Source: Signed contract + pilot results report
Date: 2024-11-15
```

**Skill:** `causal-flow/stages/causal-flow-input/SKILL.md`

---

### Stage 2: HYPOTHESIS

**Purpose:** Challenge/validate Canvas assumptions

**Process:**
- Identify which Canvas assumption this tests
- Link to `strategy/canvas/10-assumptions.md`
- State confidence level (0-100%)

**Example:**
```
Tests: A4 - Luxury brands prefer white-label SDK
Result: Validated (5/5 luxury brands chose white-label)
Previous confidence: 60% → New confidence: 95%
```

**Skill:** `causal-flow/stages/causal-flow-hypothesis/SKILL.md`

---

### Stage 3: IMPLICATION

**Purpose:** Analyze full cost/benefit with numbers

**Process:**
- Quantify business impact (revenue, cost, time)
- Calculate ROI or priority score
- Identify risks and dependencies

**Example:**
```
Content opportunity: ElsaAI case study
- Target: 500 sessions/month → 25 demos (1% conversion)
- Revenue impact: 10 deals × $500K = $5M pipeline influenced
- Investment: 40 hours (case study + 4 LinkedIn posts)
- Timeline: 2 weeks to publish, 30 days to measure
- Priority: 0.85 (high)
```

**Skill:** `causal-flow/stages/causal-flow-implication/SKILL.md`

---

### Stage 4: DECISION

**Purpose:** Official commitment, document alternatives considered

**Process:**
- State clear decision (CREATE, DEFER, REJECT)
- Document alternatives considered
- Explain reasoning

**Example:**
```
Decision: CREATE - High-priority content validating enterprise hypothesis

Alternatives considered:
1. Wait for more luxury deals → Rejected (5 deals = sufficient validation)
2. Create guide instead → Rejected (case study more credible)
3. Focus on DTC content → Rejected (luxury shows stronger signal)

Rationale: 95% confidence on A4, high SEO value, validates enterprise positioning
```

**Skill:** `causal-flow/stages/causal-flow-decision/SKILL.md`

---

### Stage 5: ACTIONS

**Purpose:** Break into executable tasks (typed for sales/marketing)

**Process:**
- Convert decision into typed actions
- Assign to AI for autonomous execution
- Track completion status

**Example:**
```
marketing:create → Draft case study (1,450 words)
  Status: ✓ Complete
  Output: drafts/elsaai-white-label-draft.md

marketing:publish → SEO optimize + publish multi-channel
  Status: ✓ Complete
  Output: 
    - blog/elsaai-white-label-sdk-case-study.md
    - linkedin/2024-11-17-elsaai-case-study.md
    - email/2024-11-19-newsletter.html

marketing:promote → Schedule cross-channel posts
  Status: ✓ Complete
  Schedule: Days 2, 9, 16

marketing:measure → Track performance (7d, 30d, 90d)
  Status: In progress
  Next check: 2024-11-24 (Day 7)
```

**Action templates:** `causal-flow/actions/templates/`

**Skill:** `causal-flow/stages/causal-flow-actions/SKILL.md`

---

### Stage 6: LEARNING

**Purpose:** Measure outcomes, validate hypothesis, update Canvas automatically

**Process:**
- Compile performance metrics
- Validate or invalidate hypothesis
- Auto-update Canvas assumptions
- Detect new opportunities

**Example:**
```
Campaign performance (30 days):
- Total sessions: 1,800 (90% of target)
- Total demos: 15 (75% of target)
- Conversion rate: 0.83% (below 1% target)
- Top performer: ElsaAI case study (1,200 sessions, 10 demos)
- Pipeline influenced: $7.5M (15 deals attributed)

Hypothesis validation:
- H1: Case studies convert better than guides
  Result: VALIDATED (0.83% vs 0.6% awareness = 38% better)
  Confidence: 95% (was 60%)

Canvas auto-update:
- strategy/canvas/10-assumptions.md
  H1: case-studies-convert-better
    status: validated
    confidence: 95%
    evidence: 15 demos, $7.5M pipeline, 38% lift over baseline

New opportunity detected:
- Follow-up content: "White-label SDK implementation guide"
  Priority: 0.72 (high)
  Rationale: SEO opportunity (keyword ranking #12, can reach top 10)
  → Flag in ops/today.md for approval
```

**Key feature:** Stage 6 automatically updates Canvas AND triggers new content opportunities.

**Skill:** `causal-flow/stages/causal-flow-learning/SKILL.md`

---

## Sales Operations (Complete Flow)

### Phase 1: Strategy (Pre-Thread, Once Per Segment)

**1. Define ICP (Ideal Customer Profile)**

```
Skill: icp-generator
Input: strategy/canvas/04-segments.md
Output: research/customer/icp/{segment}-icp.yaml

Example: research/customer/icp/dtc-fashion-smb-icp.yaml
```

**2. Create Sales Narrative**

```
Skill: sales-narrative
Input: Canvas + ICP
Output: threads/sales/narrative/{segment}/
  ├── problem-narrative.md
  ├── solution-narrative.md
  └── specifics-narrative.md
```

**3. Generate Sales Materials**

```
Skill: sales-execution/materials-generation
Input: Canvas + Narrative + ICP
Output: artifacts/sales/{segment}/materials/
  ├── pitch-deck.md
  ├── one-pager.md
  ├── call-scripts.md
  ├── email-templates.md
  ├── pilot-agreement.md
  └── contract-template.md
```

---

### Phase 2: Execution (Thread-Driven, Per Deal)

**Deal Flow Example: ElsaAI (Luxury Brand)**

**Day 1-5: Discovery and Qualification**
```
Stage 1 (Input): Inbound lead from website
Stage 2 (Hypothesis): Tests A4 (luxury brands prefer white-label)
Stage 3 (Implication): High fit (ICP score: 0.85), $1M+ ARR potential
Stage 4 (Decision): QUALIFY - Schedule discovery call

Stage 5 (Actions):
  sales:lead-intake → Capture contact info, source
  sales:qualify → Discovery call, qualification score: 0.82
```

**Day 6-15: Demo and Proposal**
```
Stage 5 (Actions continued):
  sales:demo → Custom pitch deck, demo delivered
  
Result: ElsaAI interested, requests pilot
```

**Day 16-40: Pilot Execution**
```
Stage 5 (Actions continued):
  sales:pilot → 30-day pilot agreement signed
  
Pilot results: 38% return reduction, 15% conversion lift
```

**Day 41-46: Contract Negotiation**
```
Stage 5 (Actions continued):
  sales:close → Contract signed, $1.1M ARR

Result: Deal closed
```

**Day 46: Learning Capture**
```
Stage 6 (Learning):
  Performance metrics:
    - ARR: $1.1M
    - Cycle time: 46 days
    - Pilot success: 38% return reduction
    - Customer satisfaction: 9/10

  Hypothesis validation:
    - A4: Luxury brands prefer white-label → VALIDATED
    - Confidence: 60% → 95%

  Canvas auto-update:
    - strategy/canvas/10-assumptions.md updated
    - strategy/canvas/13-metrics.md updated (ARR, cycle time)

  Content opportunity triggered:
    - Topic: ElsaAI white-label success case study
    - Priority: 0.85 (high)
    - Flag in ops/today.md for approval
```

---

## Marketing Operations (Learning-Driven Flow)

Marketing is **triggered by business learning**, not arbitrary calendars.

### Phase 1: Strategy (Pre-Content, Once Per Product)

**Generate Marketing Narrative**

```
Skill: marketing-narrative
Input: Canvas + Sales narratives (all segments)
Output: artifacts/marketing/narrative/
  ├── content-pillars.md (3-5 strategic themes)
  ├── seo-strategy.md (keywords by funnel stage)
  ├── brand-voice.md (educational, technical tone)
  └── channel-guidelines.md (format specs)
```

**Example outputs:**

**content-pillars.md:**
- Pillar 1: Return reduction economics
- Pillar 2: Product capabilities (white-label, co-branded)
- Pillar 3: Industry insights (luxury vs fast fashion)

**seo-strategy.md:**
- TOFU: "fashion returns problem", "fit issues ecommerce"
- MOFU: "reduce fashion returns", "virtual try-on SDK"
- BOFU: "white-label SDK", "GlamYouUp vs competitors"

**brand-voice.md:**
- Educational, not promotional
- Technical depth included
- Data-driven (specific metrics)
- No sales CTAs in content

**channel-guidelines.md:**
- Blog: 800-2,500 words, SEO-optimized
- LinkedIn: 300-600 words, professional tone
- Email: 400-600 words, segmented
- Website: Scannable, conversion-focused

---

### Phase 2: Content Execution (Thread-Driven, Per Opportunity)

**Trigger Flow:**

```
Sales thread completes (Stage 6: Learning)
    ↓
Thread: threads/sales/elsa-white-label/6-learning.md
Learning: "Luxury brands prefer white-label (N=5, 100% validation)"
    ↓
marketing-execution/content-strategy scans thread
    ↓
Opportunity detected:
  - Topic: "Enterprise white-label case study"
  - Pillar: Product capabilities
  - Keyword: "white-label SDK"
  - Priority: 0.85 (high)
    ↓
Flag in ops/today.md:
"[Priority: 0.85] Create case study: ElsaAI white-label success?"
    ↓
Bella approves: "Yes, create it"
    ↓
Campaign thread created: threads/marketing/campaigns/luxury-validation-nov-2024/
```

---

**Campaign Thread Execution (6-Stage Flow):**

**Stage 1: INPUT**
```
Business event: "5 luxury brands chose white-label (100% pattern)"
Source: Pattern across threads/sales/*/6-learning.md
```

**Stage 2: HYPOTHESIS**
```
Tests: H1: Validation campaigns convert better than awareness
Canvas link: 10-assumptions.md → H1 (campaign performance)
```

**Stage 3: IMPLICATION**
```
Business impact:
- Target: 2,000 sessions → 20 demos (1% conversion)
- Revenue impact: 10 deals × $500K = $5M pipeline influenced
- Investment: 40 hours (2 case studies + 4 posts)
- Timeline: 2 weeks to publish, 30 days to measure
```

**Stage 4: DECISION**
```
Campaign plan: Launch luxury white-label validation campaign

Content to produce:
1. Case study: "ElsaAI Reduces Returns 38% with White-Label SDK"
2. Case study: "How Luxury Brands Achieve Fit Accuracy"
3. LinkedIn post: Key stat (38% reduction)
4. LinkedIn post: Customer quote
5. LinkedIn post: Technical approach
6. LinkedIn post: White-label benefits

Timeline: Nov 16-30, 2024
Impact score: 0.85 (auto-execute)
```

**Stage 5: ACTIONS (Campaign Execution)**
```
For each content piece in Stage 4:

├─ marketing-execution creates draft
│   └─ Saved to: 5-actions/drafts/{piece}-draft.md
│
├─ Human reviews (30 min per piece)
│   └─ Verifies technical accuracy, approves
│
├─ SEO optimization
│   └─ Saved to: 5-actions/drafts/{piece}-optimized.md
│
├─ Multi-channel distribution
│   └─ Published to: artifacts/marketing/campaigns/luxury-validation-nov-2024/
│       ├─ blog/elsaai-case-study.md
│       ├─ linkedin/2024-11-17-elsaai.md
│       └─ distribution-record.yaml (UTM tracking)
│
└─ Update execution-log.md
    └─ [x] ElsaAI case study: Published (blog + LinkedIn)
```

**Stage 6: LEARNING (30-day campaign results)**
```
Campaign performance:
├─ Total sessions: 1,800 (90% of target)
├─ Total demos: 15 (75% of target)
├─ Conversion rate: 0.83% (below 1% target)
├─ Top performer: ElsaAI case study (1,200 sessions, 10 demos)
├─ Pipeline influenced: $7.5M (15 deals attributed)

Hypothesis validation:
└─ H1: Validation campaigns convert better
    Result: PARTIAL (0.83% vs 0.6% awareness = 38% better, but missed target)
    Confidence: 75%
    Canvas update: 10-assumptions.md → H1 status: partially validated

Strategic insight:
└─ Case studies outperform thought leadership
    Next campaign: Create follow-up luxury campaign (technical depth)
    Refinement: Increase case study allocation in content pillars

New content opportunities triggered:
└─ Follow-up content: "White-label SDK implementation guide"
    Priority: 0.72 (high)
    Rationale: SEO opportunity (keyword ranking #12, can reach top 10)
```

---

## Marketing-Sales Integration (Closed Loop)

### Content Influences Sales

```
Marketing publishes case study
    ↓
SEO drives organic traffic
    ↓
Visitor reads: "ElsaAI reduced returns 38%"
    ↓
Visitor requests demo
    ↓
Sales thread created: threads/sales/{company}-inbound/
    ↓
Stage 1 (Input): "Came from blog article (elsaai-white-label-case-study)"
    ↓
Sales thread references marketing thread:
metadata.yaml:
  source: "marketing/content/elsaai-white-label-case-study/"
  attribution: "Blog article"
    ↓
Stage 6 (Learning - if deal closes):
"Won $500K ARR, attributed to blog article"
    ↓
marketing-execution/performance-tracking updates:
performance.yaml:
  pipeline_influenced: "$550K" (cumulative)
  conversions: 9 demos, 2 closed deals
    ↓
Canvas updated:
10-assumptions.md → H1: Case studies convert better (confidence: 95%)
```

---

### Sales Triggers Marketing

```
Sales closes 5 luxury brand deals
    ↓
Pattern detected: All 5 chose white-label SDK
    ↓
Stage 6 (Learning) in each thread:
"Luxury brands prefer white-label (validated)"
    ↓
Canvas updated:
10-assumptions.md → A4: Luxury prefers white-label (confidence: 95%)
    ↓
marketing-execution/content-strategy detects:
"Strong signal: Luxury white-label preference (N=5, 100% validation)"
"Content opportunity: Case study + implementation guide"
Priority: 0.85 (high)
    ↓
Flag in ops/today.md
    ↓
Bella approves
    ↓
Marketing thread created
    ↓
Content published
    ↓
SEO drives traffic
    ↓
Demos requested
    ↓
Sales threads created
    ↓
... (loop continues)
```

---

## Daily Operations: Bella's 5-Minute Review

**8:00 AM:** Read auto-generated `ops/today.md`

**High-priority items (human approval required):**
1. Content opportunity [Priority: 0.85] → Approve ✓
2. Content draft ready → Review for technical accuracy ✓
3. Demo call scheduled → Review prep materials

**Decisions made by AI (last 24h):**
- Sales: Qualified 3 leads, sent 45 outreach emails
- Marketing: Published ElsaAI case study, tracked 650 sessions
- Canvas: Updated A4 assumption (95% confidence)

**Performance alerts:**
- Top performer: ElsaAI case study (1.23% conversion vs 0.6% avg)
- Underperformer: API rate limiting post (42 sessions, 0 demos)

**Total human time:** 3 minutes

**AI handles autonomously:** Qualification prep, follow-ups, content publication, performance tracking, pipeline updates, next opportunity detection

---

## Next Steps

- Understand Canvas setup: [Canvas Setup](../foundation/canvas-setup.md)
- See timeline breakdown: [Timeline Guide](../foundation/timeline.md)
- Learn sales workflow: [Sales Workflow](../operations/sales-workflow.md)
- Learn marketing workflow: [Marketing Workflow](../operations/marketing-workflow.md)