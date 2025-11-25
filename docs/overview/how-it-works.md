# How It Works: Complete Operations Flow

LeanOS operates through a universal 6-stage causal flow that applies to all decisions: business, sales, marketing, and engineering.

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
{Customer} deal closed: $1.1M ARR, 38% improvement achieved
Source: Signed contract + pilot results report
Date: {date}
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
Tests: A4 - Enterprise customers prefer white-label
Result: Validated (5/5 enterprise customers chose white-label)
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
Content opportunity: {Customer} case study
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
  Output: drafts/{customer}-case-study-draft.md

marketing:publish → SEO optimize + publish multi-channel
  Status: ✓ Complete
  Output:
    - blog/{customer}-case-study.md
    - linkedin/{date}-{customer}-case-study.md
    - email/{date}-newsletter.html

marketing:promote → Schedule cross-channel posts
  Status: ✓ Complete
  Schedule: Days 2, 9, 16

marketing:measure → Track performance (7d, 30d, 90d)
  Status: In progress
  Next check: {date+7} (Day 7)
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
- Top performer: {Customer} case study (1,200 sessions, 10 demos)
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

Example: research/customer/icp/{segment}-icp.yaml
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

**Deal Flow Example: {Customer} (Enterprise)**

**Day 1-5: Discovery and Qualification**
```
Stage 1 (Input): Inbound lead from website
Stage 2 (Hypothesis): Tests A4 (enterprise customers prefer white-label)
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

Result: {Customer} interested, requests pilot
```

**Day 16-40: Pilot Execution**
```
Stage 5 (Actions continued):
  sales:pilot → 30-day pilot agreement signed

Pilot results: 38% improvement, 15% conversion lift
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
    - Pilot success: 38% improvement
    - Customer satisfaction: 9/10

  Hypothesis validation:
    - A4: Enterprise customers prefer white-label → VALIDATED
    - Confidence: 60% → 95%

  Canvas auto-update:
    - strategy/canvas/10-assumptions.md updated
    - strategy/canvas/13-metrics.md updated (ARR, cycle time)

  Content opportunity triggered:
    - Topic: {Customer} success case study
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
- Pillar 1: {Problem} economics
- Pillar 2: Product capabilities (white-label, co-branded)
- Pillar 3: Industry insights ({segment} comparisons)

**seo-strategy.md:**
- TOFU: "{problem keywords}", "{pain point keywords}"
- MOFU: "{solution keywords}", "{product category}"
- BOFU: "white-label SDK", "{your product} vs competitors"

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
Thread: threads/sales/{customer}/6-learning.md
Learning: "Enterprise customers prefer white-label (N=5, 100% validation)"
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
"[Priority: 0.85] Create case study: {Customer} success story?"
    ↓
Founder approves: "Yes, create it"
    ↓
Campaign thread created: threads/marketing/campaigns/{segment}-validation-{month-year}/
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
Campaign plan: Launch enterprise validation campaign

Content to produce:
1. Case study: "{Customer A} Achieves 38% Improvement with White-Label"
2. Case study: "How Enterprise Customers Achieve Success"
3. LinkedIn post: Key stat (38% improvement)
4. LinkedIn post: Customer quote
5. LinkedIn post: Technical approach
6. LinkedIn post: White-label benefits

Timeline: {month} {year}
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
│   └─ Published to: artifacts/marketing/campaigns/{campaign-slug}/
│       ├─ blog/{customer}-case-study.md
│       ├─ linkedin/{date}-{customer}.md
│       └─ distribution-record.yaml (UTM tracking)
│
└─ Update execution-log.md
    └─ [x] {Customer} case study: Published (blog + LinkedIn)
```

**Stage 6: LEARNING (30-day campaign results)**
```
Campaign performance:
├─ Total sessions: 1,800 (90% of target)
├─ Total demos: 15 (75% of target)
├─ Conversion rate: 0.83% (below 1% target)
├─ Top performer: {Customer} case study (1,200 sessions, 10 demos)
├─ Pipeline influenced: $7.5M (15 deals attributed)

Hypothesis validation:
└─ H1: Validation campaigns convert better
    Result: PARTIAL (0.83% vs 0.6% awareness = 38% better, but missed target)
    Confidence: 75%
    Canvas update: 10-assumptions.md → H1 status: partially validated

Strategic insight:
└─ Case studies outperform thought leadership
    Next campaign: Create follow-up enterprise campaign (technical depth)
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
Visitor reads: "{Customer} achieved 38% improvement"
    ↓
Visitor requests demo
    ↓
Sales thread created: threads/sales/{company}-inbound/
    ↓
Stage 1 (Input): "Came from blog article ({customer}-case-study)"
    ↓
Sales thread references marketing thread:
metadata.yaml:
  source: "marketing/content/{customer}-case-study/"
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
Sales closes 5 enterprise deals
    ↓
Pattern detected: All 5 chose white-label SDK
    ↓
Stage 6 (Learning) in each thread:
"Enterprise customers prefer white-label (validated)"
    ↓
Canvas updated:
10-assumptions.md → A4: Enterprise prefers white-label (confidence: 95%)
    ↓
marketing-execution/content-strategy detects:
"Strong signal: Enterprise white-label preference (N=5, 100% validation)"
"Content opportunity: Case study + implementation guide"
Priority: 0.85 (high)
    ↓
Flag in ops/today.md
    ↓
Founder approves
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

## Daily Operations: Founder's 5-Minute Review

**8:00 AM:** Read auto-generated `ops/today.md`

**High-priority items (human approval required):**
1. Content opportunity [Priority: 0.85] → Approve ✓
2. Content draft ready → Review for technical accuracy ✓
3. Demo call scheduled → Review prep materials

**Decisions made by AI (last 24h):**
- Sales: Qualified 3 leads, sent 45 outreach emails
- Marketing: Published {Customer} case study, tracked 650 sessions
- Canvas: Updated A4 assumption (95% confidence)

**Performance alerts:**
- Top performer: {Customer} case study (1.23% conversion vs 0.6% avg)
- Underperformer: API rate limiting post (42 sessions, 0 demos)

**Total human time:** 3 minutes

**AI handles autonomously:** Qualification prep, follow-ups, content publication, performance tracking, pipeline updates, next opportunity detection

---

## Engineering Operations (Verification-Driven Flow)

Engineering is **triggered by business decisions** and produces **mathematically verified systems**.

### Phase 1: Requirements (Thread-Driven)

**Business Decision Triggers Engineering**

```
Business thread decides to build feature
    ↓
Engineering thread created: threads/engineering/{requirement}/
    ↓
Stage 1 (Input): Natural language requirements
Stage 2 (Hypothesis): Technical feasibility assessment
Stage 3 (Implication): Effort estimate, ROI analysis
Stage 4 (Decision): BUILD / DEFER / KILL
```

---

### Phase 2: Architecture (Specification Generation)

**Stage 5 Actions: engineering:architecture**

```
Skill: system-architecture (9 sub-skills)
Input: threads/engineering/{requirement}/1-input.md
Output: artifacts/engineering/specifications/v{X}/

Process:
1. adt-analyzer → Parse requirements into algebraic types
2. algebraic-structure-validator → Validate ADT correctness
3. functor-generator → Generate functors for patterns
4. natural-transformation-engine → Version migrations
5. curry-howard-prover → Type proofs
6. system-optimizer → Apply algebraic laws
7. architecture-validator → Validate categorical laws (10K tests)
8. state-machine-validator → Validate state transitions
9. version-compatibility-prover → Prove migrations

Output files:
├── requirements.adt           # Algebraic expression
├── types.curry-howard         # Type proofs
├── architecture.categorical   # Functors, transformations
├── api.openapi.json          # API contract
├── services.spec.yaml        # Service boundaries
└── state-machines.yaml       # State transitions
```

---

### Phase 3: Code Generation (Two-Phase Architecture)

**Key Innovation:** Generate maps first, verify composition, then generate code.

**Phase 3a: Maps Generation**

```
Skill: standardization-definer
Output: artifacts/engineering/maps/shared/
  └── standards-contract.yaml (auth, validation, responses)

Skill: backend-prover (Phase 1)
Output: artifacts/engineering/maps/backend/
  └── {service}-map.yaml (structural specs)

Verification: composition-map-validator
  └── Verify composition laws on maps (~3 sec)
```

**Phase 3b: Code Generation**

```
Skill: backend-prover (Phase 2)
Output: artifacts/engineering/code/backend/
  └── {service}/ (Python/FastAPI)

Skill: standardization-applier
  └── Inject standards, verify naturality

Skill: frontend-prover
Output: artifacts/engineering/code/frontend/
  └── {app}/ (TypeScript/Remix)
```

---

### Phase 4: Infrastructure & Deployment

**Stage 5 Actions: engineering:infrastructure**

```
Skill: infrastructure-prover (5 sub-skills)
Input: services.spec.yaml
Output: artifacts/engineering/configs/

Process:
1. service-topology-analyzer → Extract dependencies
2. docker-generator → Dockerfiles, compose
3. kubernetes-generator → K8s manifests
4. ci-cd-generator → GitHub Actions
5. topology-prover → Prove deployment isomorphic to spec

Output:
├── docker/
│   ├── Dockerfile.{service}
│   └── docker-compose.yaml
├── kubernetes/
│   ├── deployment.yaml
│   └── service.yaml
└── ci-cd/
    └── .github/workflows/deploy.yaml
```

---

### Phase 5: Proof Composition & Deployment Authorization

**Stage 5 Actions: engineering:validate**

```
Skill: proof-composer
Input: All proofs from all engineering skills
Output: artifacts/engineering/proofs/composed/system-proof.certificate

Validation chain:
├── ADT validation proofs
├── Type proofs (Curry-Howard)
├── Composition proofs (categorical laws)
├── Functor law proofs
├── Natural transformation proofs
├── State machine proofs
└── Version compatibility proofs

Result: Certificate valid → Deployment authorized
        Certificate invalid → Flag in ops/today.md
```

---

### Engineering Thread Example: Multi-Tenant Catalog Sync

**Stage 1: INPUT**
```
Requirement: "Build multi-tenant catalog sync for Shopify + WooCommerce"
Source: Business thread decision (product roadmap)
Date: 2025-01-15
```

**Stage 2: HYPOTHESIS**
```
Tests: T1 - Category-theoretic design scales to multi-platform
Canvas link: 10-assumptions.md → T1
Confidence: 70%
```

**Stage 3: IMPLICATION**
```
Effort: 40 hours (specification) + 20 hours (code gen)
ROI: Enables $2M ARR segment (marketplace customers)
Risk: Medium (new platform integrations)
Timeline: 2 weeks to production
```

**Stage 4: DECISION**
```
Decision: BUILD

Impact Calculation (Bootstrap Mode):
- Revenue Impact: 0.8 ($200K MRR potential)
- Time to Cash: 0.7 (6 weeks)
- Margin: 0.9 (high margin SaaS)
→ Impact: 0.80 (requires human approval)

Alternatives:
- Build without formal verification → Rejected (maintenance burden)
- Use third-party sync → Rejected (poor fit, high cost)

Rationale: High revenue potential, positions for marketplace segment
```

**Stage 5: ACTIONS**
```
engineering:architecture
  Status: ✓ Complete
  Output: artifacts/engineering/specifications/v20250115_143022/

engineering:backend
  Status: ✓ Complete
  Output: artifacts/engineering/code/backend/catalog-sync/

engineering:frontend
  Status: ✓ Complete
  Output: artifacts/engineering/code/frontend/sync-dashboard/

engineering:infrastructure
  Status: ✓ Complete
  Output: artifacts/engineering/configs/

engineering:validate
  Status: ✓ Complete
  Certificate: system-proof.certificate (VALID)
```

**Stage 6: LEARNING**
```
Outcome: Deployed to production

Metrics:
- Specification time: 38 hours (5% under estimate)
- Code generation: 18 hours (10% under estimate)
- Property tests: 10,000/10,000 passed
- Production bugs (30 days): 0

Hypothesis validation:
- T1: Category-theoretic design scales → VALIDATED
- Confidence: 70% → 95%

Canvas update:
- 10-assumptions.md → T1 status: validated
- 08-advantage.md → Added: "Mathematically verified systems"

New opportunity:
- BigCommerce integration (similar architecture)
- Priority: 0.75
```

---

## Next Steps

- Understand Canvas setup: [Canvas Setup](../foundation/canvas-setup.md)
- See timeline breakdown: [Timeline Guide](../foundation/timeline.md)
- Learn sales workflow: [Sales Workflow](../operations/sales-workflow.md)
- Learn marketing workflow: [Marketing Workflow](../operations/marketing-workflow.md)
- Learn engineering workflow: [Engineering Workflow](../operations/engineering-workflow.md)
- See all skills: [All Skills](../skills/all-skills.md)