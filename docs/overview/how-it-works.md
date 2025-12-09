# How LeanOS Works

LeanOS operates through a **reasoning gateway** that routes tasks to appropriate modes, with **causal flow** enforced for operational threads.

## Reasoning Gateway (Entry Point)

All non-trivial tasks route through the reasoning gateway:

```
Task arrives
    ↓
Reasoning Gateway
    ↓
┌─────────────────────────────────────────────────────────────────┐
│ Mode Selection (based on context signals)                       │
├─────────────────────────────────────────────────────────────────┤
│ CAUSAL (enforced)  │ Operational execution, known process       │
│ ABDUCTIVE          │ "Why did X happen?" → Root cause           │
│ INDUCTIVE          │ "This keeps happening" → Pattern           │
│ ANALOGICAL         │ "This is like..." → Adapted playbook       │
│ DIALECTICAL        │ "On one hand..." → Synthesis               │
│ COUNTERFACTUAL     │ "What if we had..." → Learning             │
└─────────────────────────────────────────────────────────────────┘
```

**Skill:** `.claude/skills/reasoning-gateway/SKILL.md`

---

## Enforced Flows (Always Causal)

Operational threads are **enforced** to use causal mode:

| Thread Type | Trigger | Causal Flow |
|-------------|---------|-------------|
| Business | Strategic decision, feedback | 6-stage → Canvas update |
| Sales | Lead, referral | 6-stage → Pipeline tracking |
| Marketing | Opportunity detected | 6-stage → Campaign execution |
| Engineering | Build decision | 6-stage → Specifications |

---

## Causal Flow (6 Stages)

**Skill:** `.claude/skills/reasoning-gateway/stages/reasoning-causal/SKILL.md`

### Stage 1: INPUT
Capture factual observation (not opinion).
```
{Customer} deal closed: $1.1M ARR, 38% improvement
Source: Signed contract
Date: {date}
```

### Stage 2: HYPOTHESIS
Link to Canvas assumption being tested.
```
Tests: A4 - Enterprise customers prefer white-label
Result: Validated (5/5 chose white-label)
Confidence: 60% → 95%
```

### Stage 3: IMPLICATION
Quantify business impact.
```
Revenue: $5M pipeline influenced
Investment: 40 hours
Priority: 0.85
```

### Stage 4: DECISION
Official commitment with impact scoring.
```
Decision: CREATE - White-label case study
Impact: 0.85 (requires approval)
Alternatives: [considered and rejected]
```

### Stage 5: ACTIONS
Execute typed tasks.
```
marketing:create → Draft case study
marketing:publish → Multi-channel distribution
marketing:measure → Track 7/30/90 day performance
```

### Stage 6: LEARNING
Validate hypothesis, update Canvas.
```
Hypothesis: VALIDATED
Canvas update: 10-assumptions.md → A4 confidence: 95%
New opportunity: Follow-up implementation guide
```

---

## Analytical Modes (When to Use)

### Abductive: Diagnosis
**Trigger:** Unexpected outcome, anomaly
**Example:** "Conversion dropped 40% - why?"
**Output:** Root cause hypothesis with evidence
**Chain:** Often chains to Causal for fix execution

### Inductive: Pattern Detection
**Trigger:** Repeated observations
**Example:** "Legal delays keep killing deals"
**Output:** Validated pattern with confidence score
**Chain:** May trigger Canvas update or process change

### Analogical: Novel Situations
**Trigger:** New context similar to past experience
**Example:** "This B2B launch is like our marketplace launch"
**Output:** Adapted playbook with context adjustments
**Chain:** Chains to Causal for execution

### Dialectical: Conflict Resolution
**Trigger:** Stakeholder disagreement, trade-offs
**Example:** "Engineering wants stability, Sales wants features"
**Output:** Synthesis that preserves core concerns
**Chain:** Chains to Causal for implementation

### Counterfactual: Decision Evaluation
**Trigger:** Post-mortem, scenario planning
**Example:** "Should we have priced higher?"
**Output:** Comparative analysis with recommendations
**Chain:** Informs future Causal decisions

---

## Operational Flows

### Sales Flow

```
Lead arrives
    ↓
Causal mode (enforced)
    ↓
Stage 1: Lead intake
Stage 2: Tests segment hypothesis
Stage 3: Qualification score
Stage 4: Decision (qualify/reject)
Stage 5: Actions (demo, pilot, close)
Stage 6: Learning → Canvas update
    ↓
If pattern detected → Inductive mode
If unexpected outcome → Abductive mode
```

**Thread:** `threads/sales/{company}/`
**Docs:** [Sales Workflow](../operations/sales-workflow.md)

### Marketing Flow

```
Opportunity detected (from business learning)
    ↓
Causal mode (enforced)
    ↓
Stage 1: Business event source
Stage 2: Tests content hypothesis
Stage 3: Impact analysis
Stage 4: Campaign decision
Stage 5: Create → Publish → Promote → Measure
Stage 6: Learning → Canvas update
    ↓
Performance analysis may trigger other modes
```

**Thread:** `threads/marketing/campaigns/{slug}/`
**Docs:** [Marketing Workflow](../operations/marketing-workflow.md)

### Engineering Flow

```
Business decision to build
    ↓
Causal mode (enforced)
    ↓
Stage 1: Requirements capture
Stage 2: Feasibility hypothesis
Stage 3: Effort/ROI analysis
Stage 4: Build/defer decision
Stage 5: Architecture → Code → Infrastructure
Stage 6: Learning (production metrics)
    ↓
Verification gates at each stage
```

**Thread:** `threads/engineering/{requirement}/`
**Docs:** [Engineering Workflow](../operations/engineering-workflow.md)

---

## Daily Operations

**Morning:** `ops/today.md` auto-generated with:
- High-priority items (impact ≥0.8) requiring approval
- AI decisions (last 24h)
- Performance alerts
- Anomalies detected

**Human review:** 5 minutes
- Approve/defer/reject flagged items
- Review content drafts
- Skim call prep materials

**AI handles autonomously:**
- Lead qualification
- Content generation
- Pipeline updates
- Performance tracking
- Pattern detection

**Docs:** [Daily Routine](../operations/daily-routine.md)

---

## Closed-Loop System

```
Sales thread completes (Stage 6)
    ↓
Learning captured: "Enterprise prefers white-label (N=5, 100%)"
    ↓
Canvas updated: A4 assumption validated
    ↓
Content strategy scans: opportunity detected
    ↓
Marketing thread created (causal mode)
    ↓
Content published → SEO traffic → Demos
    ↓
Sales threads created
    ↓
Loop continues
```

---

## Impact-Based Autonomy

| Impact Score | Action |
|--------------|--------|
| < 0.8 | Auto-execute, log in thread |
| ≥ 0.8 | Flag in `ops/today.md`, wait for approval |
| Customer calls | Always human |
| Canvas-altering | Always require approval |

**Mode-aware formulas:**

**VENTURE:** `(Strategic Value × Market Size × Defensibility) / 3`
**BOOTSTRAP:** `(Revenue Impact × Time to Cash × Margin) / 3`

---

## Next Steps

- [Architecture Overview](architecture.md) - 5-layer system
- [Sales Workflow](../operations/sales-workflow.md) - Deal execution
- [Marketing Workflow](../operations/marketing-workflow.md) - Campaign execution
- [Engineering Workflow](../operations/engineering-workflow.md) - Build verification
- [All Skills](../skills/all-skills.md) - Complete reference
