# Research Workflow

A systematic approach to research with two complementary modes: market analysis and knowledge synthesis.

---

## Two Research Modes

LeanOS supports two distinct research modes that serve different purposes:

### Market Research (market-research agent)

Analyze external market dynamics to evaluate opportunity viability.

**Agent:** `market-research` orchestrates mode selection and reasoning.

| Skill | Mode | Focus |
|-------|------|-------|
| `research-market-venture` | VENTURE | TAM, growth rates, defensibility, 10x potential |
| `research-market-bootstrap` | BOOTSTRAP | Spend flows, budget holders, arbitrage, immediate revenue |

**Process:** Mode detection → Research → Inductive synthesis
**Output:** `research/synthesis/*.md` (analysis reports)
**Use when:** Evaluating markets, competitors, pricing, viability

### Knowledge Synthesis (research-*)

Extract and synthesize knowledge from expert sources into actionable frameworks.

| Skill | Purpose |
|-------|---------|
| `research-source-processing` | Process individual sources into structured insights |
| `research-playbook-generation` | Generate actionable playbooks from insights |

**Synthesis:** Uses `reasoning-inductive` for cross-source pattern extraction
**Input:** Expert content (URLs, videos, podcasts, articles, books)
**Output:** `research/sources/*.md`, `research/playbooks/*.md`, `research/synthesis/*.md`
**Use when:** Building knowledge from expert sources

### knowledge-builder Agent

The `knowledge-builder` agent orchestrates the knowledge synthesis pipeline.

**Task Types:**

| Task | Description | Output |
|------|-------------|--------|
| Single Source | Process one source | `research/sources/{slug}/insights.md` |
| Multi-Source | Process multiple sources | Insights + playbooks per domain |
| Research Sprint | 5 sources, comprehensive | `research-sprint-{topic}/` with executive summary |
| Knowledge Base | 20+ sources, multi-domain | `knowledge-base-{topic}/` with playbooks + synthesis |

**Routing:**
- "Process this source" → Single Source
- "Process these 5 sources" → Multi-Source
- "Run a research sprint on X" → Research Sprint
- "Build a knowledge base on X" → Knowledge Base

### Choosing Between Modes

| Question | Use |
|----------|-----|
| "Is this market viable?" | market-research agent |
| "Who are the competitors?" | market-research agent |
| "What do experts say about X?" | knowledge-builder agent |
| "Build a playbook from these sources" | knowledge-builder agent |
| "Synthesize these talks into a framework" | knowledge-builder agent |

Both modes can be combined: use market research to evaluate opportunity, then knowledge synthesis to learn execution from experts.

### Reasoning Mode

Both agents use `reasoning-inductive` for synthesis:

- `market-research` → Synthesize market data into validated conclusions
- `knowledge-builder` → Synthesize source insights into unified frameworks

Process: Observations → Patterns → Generalizations → Testing → Synthesis

See [Inductive Reasoning Framework](#inductive-reasoning-framework) below for the 5-stage process.

---

## Inductive Reasoning Framework

The 5-stage inductive framework applies to all synthesis work (knowledge synthesis, market analysis, cross-source patterns).

### Why Inductive Reasoning for Research?

| Causal Reasoning | Inductive Reasoning |
|------------------|---------------------|
| For **known** cause-effect chains | For **discovering** cause-effect |
| Operational execution | Exploratory research |
| "Do X → Get Y" (deterministic) | "We observed X → Maybe Y" (probabilistic) |
| Assumes you know what to do | Figures out what to do |

**Research is discovery.** You start with observations and extract patterns. Inductive reasoning is the natural fit for any research context—market analysis, opportunity discovery, competitive intelligence, or technical exploration.

---

## The 5-Stage Inductive Framework

```
1-observations → 2-patterns → 3-generalizations → 4-testing → 5-synthesis
```

| Stage | Purpose | Input | Output |
|-------|---------|-------|--------|
| **1. Observations** | Collect instances | Sources, data | Structured dataset |
| **2. Patterns** | Find what recurs | Dataset | Pattern statements + evidence |
| **3. Generalizations** | Extract IF/THEN rules | Patterns | Rules with conditions + confidence |
| **4. Testing** | Validate rules | Rules + new data | Confirmed/revised rules |
| **5. Synthesis** | Decide + capture | Validated rules | Decision + knowledge artifacts |

---

## Stage 1: Observations

**Goal:** Collect structured instances from sources.

**Process:**
1. Define the research question clearly
2. Identify sources (documents, interviews, databases, web)
3. Extract instances with consistent attributes
4. Organize into categories/segments
5. Track metadata (count, quality, coverage)

**Quality Criteria:**
- 20-50+ instances for meaningful patterns
- Multiple segments/categories represented
- Attributes consistently captured across instances
- Quality score > 0.80 (data reliability)

**Output Format:**
```yaml
dataset:
  total_instances: N
  sources: [list]
  segments: [categories]
  attributes: [consistent fields per instance]
  quality_score: 0.XX
```

---

## Stage 2: Patterns

**Goal:** Detect what recurs across observations.

**Six Pattern Types:**

| Type | Question | Example |
|------|----------|---------|
| **Frequency** | How often does X occur? | "55% of cases show behavior Y" |
| **Correlation** | Do X and Y co-occur? | "High A correlates with low B" |
| **Sequence** | Does X lead to Y over time? | "Event A precedes outcome B" |
| **Cluster** | Do X, Y, Z group together? | "These 5 attributes cluster" |
| **Trend** | What direction over time? | "Metric increasing 73% YoY" |
| **Threshold** | Do breakpoints exist? | "Above 80%, behavior changes" |

**For Each Pattern, Capture:**
```yaml
pattern:
  id: P1
  type: [frequency|correlation|sequence|cluster|trend|threshold]
  statement: "Clear one-sentence pattern"
  evidence:
    - instance_1: description
    - instance_2: description
    - instance_3: description  # minimum 3
  mechanism: "Why this pattern exists (hypothesis)"
  strength: 0.XX  # 0-1 scale
  confidence: [strong|moderate|weak]
```

**Quality Criteria:**
- 3+ patterns identified
- Each pattern has 3+ evidence points
- Mechanisms hypothesized (not just correlation)
- Anomalies/exceptions documented

---

## Stage 3: Generalizations

**Goal:** Convert patterns to actionable rules.

**Rule Structure:**
```yaml
rule:
  id: R1
  statement: "IF [condition] THEN [prediction]"
  derived_from: [P1, P3, P7]

  structure:
    condition: "When to apply this rule"
    prediction: "What will happen"
    mechanism: "Why it works"

  applicability:
    works_for: ["contexts where this applies"]
    exceptions: ["when this doesn't apply"]

  confidence: 0.XX
```

**Quality Criteria:**
- Rules derived from patterns (not assumptions)
- Clear condition + prediction (testable)
- Exceptions documented
- Competing/conflicting rules identified

**Common Mistakes:**
- Generalizing from single pattern
- Ignoring exceptions
- Stating correlation as causation
- Over-confident rules from weak patterns

---

## Stage 4: Testing

**Goal:** Validate generalizations against evidence.

**Validation Methods:**

| Method | Description | When to Use |
|--------|-------------|-------------|
| **Holdout data** | Observations not used in pattern detection | Always (if possible) |
| **New instances** | Fresh data collected for validation | High-stakes decisions |
| **Edge cases** | Boundary conditions and exceptions | Rule refinement |
| **Expert review** | Domain expert feedback | Complex domains |
| **Prediction test** | Apply rule, check outcome | When outcomes observable |

**For Each Rule:**
1. Define 2+ tests
2. Run tests, track pass/fail
3. Calculate post-test confidence
4. Revise rule if partially failed
5. Reject rule if fundamentally failed

**Confidence Update:**
```
Pre-test confidence: 0.75
Tests: 4/5 passed
Post-test confidence: 0.70 (↓ adjusted for failure)
Revision: Added exception for edge case
```

---

## Stage 5: Synthesis

**Goal:** Make decision and capture knowledge.

### Decision Framework

| Decision | Meaning | Next Action |
|----------|---------|-------------|
| **GO** | Proceed | Define success criteria, timeline, first action |
| **NO-GO** | Stop | Document learning, define reopen conditions |
| **PIVOT** | Change direction | Document old → new direction, rationale |

### Knowledge Artifacts

After synthesis, create:

1. **Pattern Library Entries**
   - Validated patterns with evidence
   - Confidence scores
   - Application contexts

2. **Rules/Playbooks**
   - IF/THEN rules that survived testing
   - Conditions and exceptions
   - Mechanism explanations

3. **Decision Record**
   - Question asked
   - Answer found
   - Evidence basis
   - Limitations acknowledged

### Synthesis Template

```yaml
research_synthesis:
  question: "What we asked"
  answer: "What we found"
  decision: [go|no-go|pivot]

  key_findings:
    - finding_1: {rule, confidence, implication}
    - finding_2: {rule, confidence, implication}

  limitations:
    - limitation_1: impact on conclusions

  next_actions:
    - action_1: {what, success_criteria, timeline}

  knowledge_created:
    - patterns: [list]
    - rules: [list]
    - playbooks: [if applicable]
```

---

## When to Use Other Reasoning Modes

Inductive is default for research, but other modes serve specific purposes:

| Mode | Use When | Question Type |
|------|----------|---------------|
| **Inductive** | Extracting patterns from data | "What patterns exist?" |
| **Abductive** | Diagnosing anomalies | "Why did this happen?" |
| **Analogical** | Novel situation mapping | "What is this like?" |
| **Dialectical** | Conflicting evidence | "How do we reconcile X and Y?" |
| **Counterfactual** | Evaluating past decisions | "What if we had done X instead?" |
| **Causal** | Executing known processes | "How do we implement X?" |

### Mode Selection Guide

```
Is there a pattern to discover?
  YES → Inductive
  NO ↓

Is there an anomaly to explain?
  YES → Abductive
  NO ↓

Is there a novel situation?
  YES → Analogical
  NO ↓

Is there conflicting evidence?
  YES → Dialectical
  NO ↓

Are we evaluating past decisions?
  YES → Counterfactual
  NO ↓

Are we executing a known process?
  YES → Causal
```

---

## Research Checklist

### Before Starting
- [ ] Research question clearly defined
- [ ] Sources identified
- [ ] Attributes to capture defined
- [ ] Quality threshold set

### During Research
- [ ] 20+ observations collected
- [ ] Multiple segments represented
- [ ] 3+ patterns detected
- [ ] Mechanisms hypothesized
- [ ] Rules have conditions + exceptions
- [ ] 2+ tests per rule

### After Research
- [ ] Decision documented (go/no-go/pivot)
- [ ] Limitations acknowledged
- [ ] Knowledge artifacts created
- [ ] Next actions defined

---

## Common Failure Modes

| Failure | Signal | Fix |
|---------|--------|-----|
| **Confirmation bias** | Only finding expected patterns | Actively seek disconfirming evidence |
| **Small sample** | Patterns from <10 instances | Collect more data before generalizing |
| **Over-fitting** | Rules too specific to sample | Test on holdout data |
| **Missing mechanisms** | Correlation without causation | Always hypothesize "why" |
| **Skipped testing** | Rules not validated | No rule without 2+ tests |
| **Vague synthesis** | No clear decision | Force go/no-go/pivot choice |

---

## Quick Reference

### Pattern Detection Questions
- What appears frequently?
- What co-occurs?
- What sequences exist?
- What clusters together?
- What's trending?
- Where are the breakpoints?

### Rule Quality Test
- Is the condition clear?
- Is the prediction testable?
- Is the mechanism plausible?
- Are exceptions documented?
- What's the confidence?

### Synthesis Decision Criteria
- GO: High confidence (>0.75), clear next action, acceptable risk
- NO-GO: Low confidence (<0.50), unclear path, unacceptable risk
- PIVOT: Medium confidence, better direction identified