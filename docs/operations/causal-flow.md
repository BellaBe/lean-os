# 6-Stage Causal Flow

Universal decision framework for engineering, business, sales, and marketing threads.

## Overview

Every decision flows through 6 stages:
**Input → Hypothesis → Implication → Decision → Actions → Learning**

## Stage 1: INPUT

**Purpose:** Capture factual observation (not opinion)

**Process:**
- Record what happened
- Include numbers, dates, names
- Link to source

**Example:**
```
ElsaAI deal closed: $1.1M ARR, 38% return reduction
Source: Signed contract + pilot results
Date: 2024-11-15
```

**Skill:** `causal-flow/stages/causal-flow-input/`

---

## Stage 2: HYPOTHESIS

**Purpose:** Challenge/validate Canvas assumptions

**Process:**
- Identify which assumption this tests
- Link to `strategy/canvas/10-assumptions.md`
- State confidence level

**Example:**
```
Tests: A4 - Luxury brands prefer white-label
Result: Validated (5/5 chose white-label)
Confidence: 60% → 95%
```

**Skill:** `causal-flow/stages/causal-flow-hypothesis/`

---

## Stage 3: IMPLICATION

**Purpose:** Analyze business impact with numbers

**Process:**
- Quantify impact (revenue, cost, time)
- Calculate ROI or priority
- Identify risks

**Example:**
```
Impact: 500 sessions/month → 25 demos
Revenue: $5M pipeline influenced
Investment: 40 hours
Priority: 0.85
```

**Skill:** `causal-flow/stages/causal-flow-implication/`

---

## Stage 4: DECISION

**Purpose:** Official commitment with mode-aware impact scoring

**Process:**
1. Check business model mode (`strategy/canvas/00-business-model-mode.md`)
2. Calculate impact score using mode-specific formula
3. State decision (CREATE, DEFER, REJECT)
4. Document alternatives
5. Explain reasoning

**Impact Scoring (Mode-Aware):**

**VENTURE Mode:**
```
Impact = (Strategic Value × Market Size × Defensibility) / 3
```

**BOOTSTRAP Mode:**
```
Impact = (Revenue Impact × Time to Cash × Margin) / 3
```

**Threshold:**
- <0.8: AI proceeds autonomously
- ≥0.8: Human approval required

**Example (Bootstrap Mode):**
```
Decision: CREATE - White-label service for agencies

Impact Calculation:
- Revenue Impact: 0.7 ($25k MRR potential)
- Time to Cash: 0.8 (6 weeks to first payment)
- Margin: 0.9 (80% gross margin)
→ Impact: 0.80 (requires human approval)

Alternatives:
- Wait for more customers (rejected - opportunity cost too high)
- Partner with provider (rejected - poor margins)

Rationale: High confidence, immediate revenue, excellent margins
```

**Skill:** `causal-flow/stages/causal-flow-decision/`

**See also:** [Success Metrics](../integration/success-metrics.md) for mode-specific criteria

---

## Stage 5: ACTIONS

**Purpose:** Execute tasks

**Typed actions:**
- Engineering: analyze, design, implement, test, deploy
- Business: research, analyze, decide, communicate
- Sales: lead-intake, qualify, demo, pilot, close
- Marketing: create, publish, promote, measure

**Templates:** `causal-flow/actions/templates/`

**Skill:** `causal-flow/stages/causal-flow-actions/`

---

## Stage 6: LEARNING

**Purpose:** Validate hypothesis, update Canvas

**Process:**
- Compile metrics
- Validate/invalidate hypothesis
- Auto-update Canvas
- Detect new opportunities

**Key feature:** Automatically updates Canvas assumptions

**Skill:** `causal-flow/stages/causal-flow-learning/`

---

## Thread Types

**Engineering threads (optional):** `threads/engineering/{type}/{name}/`
- **Architecture:** System design decisions (`architecture/{system-name}/`)
- **Services:** Microservice implementation (`services/{service-name}/`)
- **Standards:** Standardization application (`standards/{concern-name}/`)
- 6-stage flow with technical actions
- **Stage 1:** Requirements, feature requests
- **Stage 2:** Design hypothesis, architectural assumptions
- **Stage 3:** Implementation effort, system impact
- **Stage 4:** Technical approach, alternatives considered
- **Stage 5:** Code generation, testing, deployment
- **Stage 6:** Validation results, performance metrics

**Business threads:** `threads/business/{name}/`
- Strategic decisions
- Canvas updates
- Process improvements

**Sales threads:** `threads/sales/{name}/`
- Deal progression
- Campaign execution
- Pipeline management

**Marketing threads:** `threads/marketing/campaigns/{slug}/`
- Content execution
- Campaign tracking
- Performance analysis

---

For complete examples, see:
- [Sales Workflow](sales-workflow.md)
- [Marketing Workflow](marketing-workflow.md)
- [How It Works](../overview/how-it-works.md)