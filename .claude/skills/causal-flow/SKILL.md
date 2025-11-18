---
name: causal-flow
description: Orchestrate evidence-based decision making through 6 stages - Input, Hypothesis, Implication, Decision, Actions, Learning. Manages business threads, sales pipeline, and marketing campaigns with automatic Canvas updates and hypothesis validation.
allowed-tools: "Read,Write,Bash"
---

# Business Operations Causal Flow Orchestrator

You are an expert at evidence-based decision making and hypothesis-driven business operations. You orchestrate the 6-stage causal flow that transforms observations into validated learnings while maintaining a living Canvas of business assumptions.

## Purpose

Execute evidence-based decision flows that:
- Start with factual observations, not opinions
- Explicitly challenge and validate business assumptions
- Analyze full cost/benefit before commitment
- Maintain complete audit trail from input to learning
- Self-correct through automatic Canvas updates

## When to Use This Skill

**Use this orchestrator when:**
- Starting new business decision thread (strategic decisions)
- Starting new sales pipeline thread (deal management)
- Starting new marketing campaign thread (campaign execution)
- Managing multiple concurrent threads across types

**Use individual stage skills when:**
- Adding observation to existing thread (Stage 1 only)
- Re-analyzing hypothesis with new data (Stage 2 only)
- Updating impact analysis (Stage 3 only)
- Documenting learning from completed actions (Stage 6 only)

## The 6-Stage Flow

```
Input → Hypothesis → Implication → Decision → Actions → Learning
  ↓         ↓            ↓            ↓          ↓          ↓
Observe  Challenge   Analyze     Commit    Execute    Measure &
         Beliefs     Impact                & Track    Validate
                                                      → Canvas
```

### Flow Characteristics

- **Linear progression:** Each stage depends on previous stage
- **Multiple threads:** Different decisions at different stages
- **Built-in tracking:** Actions stage includes progress tracking
- **Automatic updates:** Learning stage measures results and updates Canvas automatically
- **AI-driven:** Agents execute autonomously (95%+ decisions)
- **Human intervention:** Only when flagged for strategic misalignment
- **Unified architecture:** Same flow for business, sales, and marketing

---

## Canvas Integration

### Canvas Location & Structure

**Absolute Path:** `strategy/canvas/`

The Canvas is the single source of truth for all business assumptions. It consists of 15 separate markdown files (one per section):

```
strategy/canvas/
├── 01-context.md                    # KBOS (Known/Believed/Observed/Suspected)
├── 02-constraints.md                # Market influences & constraints
├── 03-opportunity.md                # Opportunity evaluation
├── 04-segments.md                   # Customer segments
├── 05-problem.md                    # Problem definition
├── 06-competitive.md                # Competitive landscape
├── 07-uvp.md                        # UVP & Mission
├── 08-advantage.md                  # Unfair advantage
├── 09-solution.md                   # Solution definition
├── 10-assumptions.md                # Assumptions & Validation ← PRIMARY for hypothesis validation
├── 11-pricing.md                    # Pricing & revenue streams
├── 12-costs.md                      # Cost structure
├── 13-metrics.md                    # Key metrics
├── 14-growth.md                     # Growth plan
└── 15-gtm.md                        # Go-to-market
```

**Key Canvas Section for Causal Flow:**
- **Primary:** `strategy/canvas/10-assumptions.md` - Contains all tracked hypotheses
- **Secondary:** Update other sections as learning validates/invalidates assumptions

### Canvas Content Structure

Each tracked assumption in `10-assumptions.md` follows this format:

```markdown
### A4: Brand Preferences by Segment
**Status:** ✅ VALIDATED | ⏳ TESTING | ❌ INVALIDATED | 📝 DRAFT
**Hypothesis:** Luxury brands prefer white-label solutions over direct API
**Confidence:** 95% (previously: 60%)
**Evidence:** threads/sales/elsa-white-label/6-learning.md
**Last validated:** 2025-12-15
**Related Canvas sections:** 04-segments.md, 07-uvp.md, 11-pricing.md
```

### Canvas Access Pattern

**Reading Canvas:**
```bash
# Read assumptions for hypothesis validation (Stage 2)
Read strategy/canvas/10-assumptions.md

# Read related sections for context
Read strategy/canvas/04-segments.md  # Customer understanding
Read strategy/canvas/07-uvp.md       # Value proposition alignment
```

**Updating Canvas:**
```bash
# After Stage 6 (Learning), update assumptions
str_replace strategy/canvas/10-assumptions.md "old assumption" "updated assumption"

# If learning impacts other sections, update those too
str_replace strategy/canvas/04-segments.md "old segment data" "validated segment data"
```

### Automatic Canvas Updates (Stage 6: Learning)

After Stage 6 (Learning):
1. **Measure outcomes:** Extract quantifiable metrics from action results
2. **Parse learning results:** Extract validation outcome
3. **Update assumption status:** Change status emoji and confidence
4. **Add evidence link:** Reference thread path
5. **Update related sections:** If learning impacts segments/pricing/etc.
6. **Commit with context:** `git commit -m "Canvas: Validated A4 via threads/sales/elsa-white-label"`

**Update Triggers:**
- ✅ Hypothesis validated → Update status, increase confidence, add evidence
- ❌ Hypothesis invalidated → Update status, document why, spawn new thread
- 📊 New data → Add to evidence, adjust confidence
- 🔄 Strategic pivot → Update multiple Canvas sections

---

## Output Storage Structure

### Artifacts Directory

**Path:** `artifacts/`

Thread actions (Stage 5) produce deliverables stored by function:

```
artifacts/
├── fundraising/                     # Investor materials
│   ├── decks/                       # Pitch decks
│   ├── financials/                  # Financial models for investors
│   └── updates/                     # Investor updates
├── marketing/                       # Marketing materials
│   ├── website/                     # Website content
│   │   ├── pages/                   # Published pages
│   │   └── blog/                    # Blog posts
│   └── linkedin/                    # LinkedIn content
│       ├── posts/                   # Published posts
│       └── instructions.md          # Content guidelines
└── sales/                           # Sales materials
    ├── current/                 # Symlinks to latest approved
    │   ├── pitch-deck.md
    │   ├── one-pager.md
    │   ├── call-scripts.md
    │   ├── email-templates.md
    │   ├── pilot-agreement.md
    │   └── contract-template.md
    ├── {date}/                  # Versioned materials
    ├── drafts/                  # High-impact changes awaiting approval
    └── CHANGELOG.md             # Materials change log
```

### Strategy Directory

**Path:** `strategy/`

Strategic planning documents and financial models:

```
strategy/
├── canvas/                          # Lean Canvas (15 files)
│   └── *.md
└── financials/                      # Financial planning
    ├── model.xlsx                   # Financial model
    ├── projections.md               # Revenue/cost projections
    ├── assumptions.md               # Financial assumptions
    └── fundraising.md               # Fundraising strategy
```

### Output Routing by Thread Type

| Thread Type | Stage 5 Actions Produce | Storage Location |
|-------------|-------------------------|------------------|
| **business** | Engineering specs, legal docs, marketing briefs | Thread-specific, may reference artifacts/ |
| **sales** | Contracts, decks, proposals, collateral | `artifacts/sales/` |
| **marketing** | Website pages, blog posts, LinkedIn posts | `artifacts/marketing/website/` or `artifacts/marketing/linkedin/` |
| **fundraising** | Pitch decks, financial models, investor updates | `artifacts/fundraising/` |

**Key Principles:**
- **Artifacts = Deliverables:** Only final, shareable outputs go in artifacts/
- **Threads = Process:** Working documents stay in thread folders
- **Strategy = Source of Truth:** Canvas + financials drive all decisions
- **Cross-references:** Learning (Stage 6) links artifacts back to threads

---

## Thread Types & Architecture

For detailed architecture, workflow patterns, and examples for each thread type, read:

- **Business threads:** `{baseDir}/reference/business-threads.md`
- **Sales threads:** `{baseDir}/reference/sales-threads.md`
- **Marketing threads:** `{baseDir}/reference/marketing-threads.md`

### Quick Reference

| Thread Type | Purpose | Action Types | Human Gates |
|-------------|---------|--------------|-------------|
| **business** | Strategic decisions | Generic (eng, legal, marketing) | High-impact decisions (>0.7) |
| **sales** | Deal pipeline | Typed (lead, qualify, demo, pilot, close) | Calls, demos, negotiations |
| **marketing** | Campaign execution | Typed (research, create, publish, promote, measure) | Content approval, budget |

---

## Sales Execution Skills Integration

### Pre-Thread: Strategy Layer

Sales threads depend on strategy artifacts generated before individual deals begin. These artifacts auto-regenerate when Canvas changes.

#### 1. ICP Definition (Per Segment)

**Skill:** icp-generator
**Trigger:** Canvas customer segments updated
**Output:** `research/customer/icp/{segment}-icp.yaml` (one file per segment)

Example:
- `research/customer/icp/dtc-fashion-smb-icp.yaml`
- `research/customer/icp/marketplaces-resellers-icp.yaml`
- `research/customer/icp/high-end-department-icp.yaml`

Each ICP file contains:
- Observable characteristics (platform, revenue, geography, team size)
- Prospecting filters (tool-specific search patterns)
- Problem signals (where to find evidence of pain points)
- Qualification questions (discovery call framework)
- Buyer personas (economic/technical/end-user)

#### 2. Sales Narrative (Per Segment)

**Skill:** sales-narrative
**Trigger:** ICP updated or Canvas positioning changes
**Output:** `threads/sales/narratives/{segment}-{persona}/`

Example:
- `threads/sales/narratives/dtc-fashion-smb-economic-buyer/`
  - problem-narrative.md
  - solution-narrative.md
  - specifics-narrative.md

Each narrative provides segment-specific messaging:
- Problem articulation (how this segment experiences the pain)
- Solution mapping (features → benefits for this segment)
- Specifics/proof (technical details, case studies relevant to segment)

#### 3. Sales Materials (Per Product)

**Skill:** sales-execution/materials-generation
**Trigger:** Canvas or narrative changes (auto-regenerates)
**Output:** `artifacts/sales/current/` (symlinks to versioned materials)

Generated materials:
- `pitch-deck.md` (10-15 slides, problem-first ordering)
- `one-pager.md` (single page, 30-second skim, B&W printable)
- `call-scripts.md` (discovery 30min, demo 30min, follow-up 15min)
- `email-templates.md` (cold outreach, follow-up sequence, meeting request)
- `pilot-agreement.md` (NEW: standard pilot terms template)
- `contract-template.md` (NEW: standard contract template)

**Impact scoring for regeneration:**
- Impact < 0.8: Auto-deploy to current/, log in CHANGELOG.md
- Impact >= 0.8: Save to drafts/, flag for human review

**Versioning:**
```
artifacts/sales/
├── current/               # Symlinks to latest approved version
│   ├── pitch-deck.md → ../2024-11-14/pitch-deck.md
│   ├── one-pager.md → ../2024-11-14/one-pager.md
│   ├── call-scripts.md → ../2024-11-14/call-scripts.md
│   ├── email-templates.md → ../2024-11-14/email-templates.md
│   ├── pilot-agreement.md → ../2024-11-14/pilot-agreement.md
│   └── contract-template.md → ../2024-11-14/contract-template.md
├── 2024-11-14/           # Versioned materials
├── 2024-10-15/           # Previous version
└── drafts/               # High-impact changes awaiting approval
    └── 2024-11-20/
```

### Thread Execution: Action Layer

During Stage 5 (Actions), sales threads reference strategy artifacts and invoke support subskills.

#### Thread Metadata (Updated)

Sales threads include segment binding:
```json
{
  "thread_id": "elsa-white-label",
  "type": "sales",
  "product": "glamyouup",
  "segment": "high-end-department",
  "icp_file": "research/customer/icp/high-end-department-icp.md",
  "narrative_path": "threads/sales/narratives/high-end-department-economic-buyer/",
  "materials_version": "2025-11-14",
  "status": "active",
  "stage": 5,
  "current_action": "sales:demo",
  "deal_size": 1100000,
  "close_probability": 0.60
}
```

#### Action Integration by Type

**sales:lead-intake**
- **AI auto-executes:** Segment detection
- **Process:** Match lead characteristics against all ICP files for product
- **Output:** Bind thread to best-matching segment (ICP match score)
- **Metadata update:** Set `segment` and `icp_file` fields
- **Template:** `actions/templates/sales-lead-intake.md`

**sales:qualification**
- **AI support:** Invoke qualification-support subskill for call prep
- **References:**
  - ICP: `research/customer/icp/{segment}-icp.md`
  - Call script: `artifacts/sales/current/call-scripts.md` (discovery section)
  - One-pager: `artifacts/sales/current/one-pager.md` (attach to follow-up)
- **Human required:** Discovery call (30-45 min)
- **Template:** `actions/templates/sales-qualify.md`

**sales:demo**
- **AI support:** Demo environment prep, use case customization
- **References:**
  - Pitch deck: `artifacts/sales/current/pitch-deck.md`
  - Call script: `artifacts/sales/current/call-scripts.md` (demo section)
- **Human required:** Demo call (45 min)
- **Template:** `actions/templates/sales-demo.md`

**sales:pilot**
- **AI support:** Generate pilot agreement from template
- **References:**
  - Pilot agreement: `artifacts/sales/current/pilot-agreement.md`
  - Success criteria: From ICP qualification questions
- **Human required:** Pilot negotiation, pilot execution
- **Template:** `actions/templates/sales-pilot.md`

**sales:close**
- **AI support:** Generate contract from template, track negotiation
- **References:**
  - Contract: `artifacts/sales/current/contract-template.md`
  - Pricing: From Canvas (strategy/canvas/11-pricing.md)
- **Human required:** Contract negotiation, signing
- **Template:** `actions/templates/sales-close.md`

### Outbound Prospecting: Campaign Layer

Outbound prospecting creates ONE campaign thread per segment, not individual threads per prospect.

#### Campaign Thread Structure
```
threads/sales/campaigns/{segment}-{date}/
├── meta.json (type: "sales-campaign")
├── 1-input.md (Campaign goal, target segment)
├── 2-hypothesis.md (Messaging hypothesis for segment)
├── 3-implication.md (Expected response rates, pipeline impact)
├── 4-decision.md (Launch campaign yes/no)
├── 5-actions/
│   ├── prospect-research.md (Type: sales-campaign:prospect-research)
│   ├── contact-finding.md (Type: sales-campaign:contact-finding)
│   ├── outreach-sequencing.md (Type: sales-campaign:outreach-sequencing)
│   └── outreach-execution.md (Type: sales-campaign:outreach-execution, includes tracking)
└── 6-learning.md (Response rates, meetings booked, pipeline generated + Canvas updates)
```

#### Campaign Action Types

**sales-campaign:prospect-research**
- **Skill:** sales-execution/prospect-research
- **Input:** ICP segment
- **Output:** `research/customer/icp/{segment}-prospects-{date}.csv` (50-200 companies)
- **Duration:** 1-2 days

**sales-campaign:contact-finding**
- **Skill:** sales-execution/contact-finding
- **Input:** Prospect list
- **Output:** `research/customer/icp/{segment}-contacts-{date}.csv` (decision-makers)
- **Duration:** 2-3 days

**sales-campaign:outreach-sequencing**
- **Skill:** sales-execution/outreach-sequencing
- **Input:** Email templates + segment + prospect list
- **Output:** `threads/sales/outreach/sequence-{segment}-{date}.md`
- **Duration:** 1 day

**sales-campaign:outreach-execution**
- **Human required:** Send emails, make calls per sequence
- **AI support:** Track responses, create individual deal threads for replies
- **Duration:** 14-21 days (sequence duration)

#### Response Handling

When prospect responds to outreach:
1. **AI creates individual deal thread:** `threads/sales/{company-name}/`
2. **Binds to segment:** Same segment as campaign
3. **Starts at Stage 1:** Input = prospect response
4. **Proceeds through standard flow:** Qualification → Demo → Pilot → Close

**Example flow:**
```
Campaign: threads/sales/campaigns/dtc-fashion-smb-2024-11/
├── Researched 100 prospects
├── Found contacts for 85
├── Sent outreach sequence
├── 12 responses
└── Created 12 individual deal threads:
    ├── threads/sales/allbirds-inbound/
    ├── threads/sales/everlane-inbound/
    └── ...
```

---

## Orchestration Workflow

### Step 1: Determine Thread Type

Ask user if unclear:
- Business decision? → `threads/business/{name}/`
- Sales opportunity? → `threads/sales/{name}/`
- Marketing campaign? → `threads/marketing/{name}/`

### Step 2: Create Thread Structure

```bash
threads/{type}/{thread-name}/
├── meta.json
├── 1-input.md
├── 2-hypothesis.md
├── 3-implication.md
├── 4-decision.md
├── 5-actions/
│   ├── action-1.md (includes progress tracking)
│   └── ...
└── 6-learning.md (results measurement + Canvas updates)
```

### Step 3: Execute 6-Stage Flow

Invoke each stage skill sequentially:

1. **Stage 1: Input** → `causal-flow-input`
   - Capture factual observation
   - SLA: 24 hours

2. **Stage 2: Hypothesis** → `causal-flow-hypothesis`
   - Challenge/validate Canvas assumptions
   - SLA: 2 days
   - Gate: Must challenge or validate ≥1 assumption

3. **Stage 3: Implication** → `causal-flow-implication`
   - Analyze business impact with numbers
   - SLA: 3 days
   - Gate: Must be reviewed before decision

4. **Stage 4: Decision** → `causal-flow-decision`
   - Official commitment, document alternatives
   - SLA: 7 days
   - Gate: Must plan ≥1 action

5. **Stage 5: Actions** → `causal-flow-actions`
   - Break into executable tasks (typed for sales/marketing)
   - Includes built-in progress tracking
   - SLA: 2 days to start

6. **Stage 6: Learning** → `causal-flow-learning`
   - Measure outcomes with quantifiable metrics
   - Validate hypothesis, update Canvas
   - SLA: 7 days after action completion
   - Gate: Must update ≥1 Canvas section

### Step 4: Track & Report

Monitor thread state: `draft` → `active` → `in_review` → `completed` → `archived`

---

## Decision Authority

### AI Agent Autonomy (>95% of decisions)

**IMPORTANT:** Impact scoring is MODE-AWARE. Check `strategy/canvas/00-business-model-mode.md` and apply the correct formula:
- **VENTURE Mode:** Impact = (Strategic Value × Market Size × Defensibility) / 3
- **BOOTSTRAP Mode:** Impact = (Revenue Impact × Time to Cash × Margin) / 3

**Autonomous when:**
- Impact score < 0.8
- Within strategic direction (aligned with Canvas)
- Clear evidence and reasoning
- Reversible or low-risk

**Flag for human when:**
- Impact score ≥ 0.8
- Strategic pivot or contradicts Canvas
- Canvas-altering decision
- High uncertainty or risk

### Human Intervention Points

**Human intervention required for:**
- High-impact decisions (≥0.8 impact score)
- Strategic pivots or Canvas changes
- Customer relationship decisions (calls, negotiations, contracts)
- Business model mode switches
- Quarterly Canvas validation

**AI proceeds autonomously for:**
- Operational decisions (<0.8 impact)
- Decisions within established strategy
- Low-risk, reversible actions
- Routine execution tasks

---

## Meta-Learning

The system improves itself by applying the same 6-stage flow to operational patterns.

### Meta-Thread Workflow

When process improvement is identified:

1. **Create meta-thread** → Use standard 6-stage causal-flow
2. **Apply to system improvement** → Update processes/templates/thresholds
3. **Validate improvement** → Track metrics for next N threads
4. **Update baseline** → If validated, new baseline becomes standard

**Meta-thread structure:**
```
threads/business/meta-{pattern-name}/
├── 1-input.md         # Pattern observation
├── 2-hypothesis.md    # Root cause hypothesis
├── 3-implication.md   # ROI analysis (time saved vs invested)
├── 4-decision.md      # Chosen solution approach
├── 5-actions/         # Implementation steps (with tracking)
└── 6-learning.md      # Validation metrics + process improvement validated
```

**ROI Example:** 20 hours invested → 34+ hours saved over next 10 threads = 170% ROI

---

## Best Practices

1. **Start with observation** - Never skip Stage 1
2. **Challenge assumptions** - Stage 2 must link to Canvas
3. **Quantify everything** - Stage 3 needs numbers (revenue, cost, timeline, risk)
4. **Document alternatives** - Stage 4 shows what you rejected
5. **Track progress** - Stage 5 actions include built-in tracking (owners, dates, deliverables)
6. **Measure and validate** - Stage 6 requires quantifiable metrics AND hypothesis validation
7. **Update Canvas automatically** - Stage 6 must update ≥1 Canvas section
8. **Generate new threads** - Stage 6 spawns threads from new opportunities
9. **Use typed actions** - Sales/marketing use action types for visibility

---

## Available Resources

### Stage Skills (6 stages)
- `stages/causal-flow-input/SKILL.md`
- `stages/causal-flow-hypothesis/SKILL.md`
- `stages/causal-flow-implication/SKILL.md`
- `stages/causal-flow-decision/SKILL.md`
- `stages/causal-flow-actions/SKILL.md`
- `stages/causal-flow-learning/SKILL.md` (combines results measurement + hypothesis validation)

### Reference Documentation
Load these when executing specific thread types:

- `{baseDir}/reference/business-threads.md` - Business strategy architecture
- `{baseDir}/reference/sales-threads.md` - Sales pipeline architecture
- `{baseDir}/reference/marketing-threads.md` - Marketing campaign architecture
- `{baseDir}/reference/thread-structure.md` - Thread organization guide
- `{baseDir}/reference/canvas-integration.md` - Canvas update protocols

### Action Templates
- `actions/templates/sales-*.md` - Sales action templates
- `actions/templates/marketing-*.md` - Marketing action templates

---

## Execution Pattern

**When user provides input:**

1. **Load appropriate reference:** Read `{baseDir}/reference/{type}-threads.md` for detailed workflow
2. **Create thread structure:** Follow naming and structure conventions
3. **Execute 6-stage flow:** Invoke stage skills sequentially
4. **Generate output:** Use templates from reference docs
5. **Update Canvas:** Automatic from Stage 6 (Learning)

**Example:**
```
User: "ElsaAI wants white-label SDK, $400K budget"

1. Determine type: sales
2. Read {baseDir}/reference/sales-threads.md
3. Create threads/sales/elsa-white-label/
4. Execute stages 1-7 using sales-specific patterns
5. Output: Deal won, Canvas updated
```

---

## Success Criteria

✓ **Evidence-based:** Starts with factual observation
✓ **Hypothesis-driven:** Challenges/validates assumptions
✓ **Impact-analyzed:** Full cost/benefit before commitment
✓ **Traceable:** Complete audit trail
✓ **Self-correcting:** Learning updates Canvas
✓ **Autonomous:** AI executes >95%
✓ **Strategic:** Human review only when flagged
✓ **Unified:** Same flow across business, sales, marketing

---

## Remember

Every decision—business, sales, or marketing—flows through these **6 stages**. No shortcuts. The discipline prevents biased, opinion-driven decisions and ensures continuous learning across all operations.

**Key architecture:**
- Actions (Stage 5) include built-in progress tracking
- Learning (Stage 6) combines results measurement + Canvas updates
- Each stage is independent and focused on a specific decision aspect

Load reference docs as needed using Read tool with `{baseDir}/reference/{file}.md` paths.