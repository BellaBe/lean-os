---
name: foundation-builder
description: Orchestrate 10 agents to build and maintain validated Lean Canvas foundation. Handles market discovery, validation, business model, and GTM. Pre-launch population and operational maintenance.
allowed-tools: "Read,Write,Bash"
---

# Foundation Builder: Canvas Population & Validation

## Overview

Business foundation orchestration system that coordinates 10 specialized agents to build and maintain a validated Lean Canvas - the single source of truth for all strategic decisions.

**Primary Mission:** Populate and validate all 15 Canvas sections with evidence-based information

**Lifecycle:** 
- Pre-launch: Build foundation (Discovery → Launch)
- Operational: Maintain foundation (Canvas updates from validated learning)

**Target Profile**: AI-first lean startups operating with minimal human oversight

**Final Output:** Living Canvas that continuously reflects current business reality
---

## System Architecture

### Agent Organization

The system comprises 10 specialized agents organized into two tiers:

**Core Agents (Always Active - 7 agents)**
1. **market-intelligence**: Market analysis, competitive landscape, customer segmentation
2. **problem-solution-fit**: Problem validation, solution design, MVP definition
3. **value-proposition**: Unique value articulation, positioning, messaging
4. **business-model**: Revenue design, cost structure, unit economics
5. **validation**: Assumption testing, experiment design, hypothesis validation
6. **go-to-market**: Channel strategy, launch planning, growth tactics
7. **execution**: Task orchestration using Claude/GPT/Copilot, daily operations

**Specialist Agents (On-Demand - 3 agents)**
8. **funding**: Fundraising strategy, pitch development, investor targeting
9. **regulatory**: Compliance requirements, licensing, regulated market entry
10. **retention-optimizer**: Cohort analysis, churn prediction, optimization experiments

### Canvas Population Flow

Each agent populates specific Canvas sections:

| Agent | Canvas Sections |
|-------|----------------|
| **market-intelligence** | 01-context (KBOS), 02-constraints, 03-opportunity, 04-segments, 06-competitive |
| **problem-solution-fit** | 05-problem, 09-solution, 10-assumptions |
| **value-proposition** | 07-uvp, 08-advantage |
| **business-model** | 11-pricing, 12-costs, 13-metrics |
| **validation** | 10-assumptions (validation status) |
| **go-to-market** | 14-growth, 15-gtm |
| **funding** | `strategy/financials/fundraising.md` |

### Information Flow

The system follows a structured progression through pre-launch phases:

```
Discovery → Definition → Validation → Execution → Launch
   ↓           ↓           ↓           ↓          ↓
Market    Value Prop   Validation  Execution   GTM
Intel  →  + Business  →  Agent   →   Agent  →  Agent
Agent      Model                              
   ↓           ↓           ↓           ↓          ↓
Canvas    Canvas       Canvas     artifacts/   Canvas
01-06     07-12        10 (val)   Outputs      14-15
```

---

## Orchestration Logic

### Phase Detection

Determine the current pre-launch phase by analyzing the request context:

**Discovery Phase (0a)**
- Triggers: Market research, TAM/SAM/SOM questions, competitive analysis, customer segmentation
- Primary Agents: market-intelligence, problem-solution-fit
- Output Focus: Market understanding, problem identification
- Canvas Sections: 01-context, 02-constraints, 03-opportunity, 04-segments, 05-problem, 06-competitive

**Definition Phase (0b)**
- Triggers: Product strategy, value proposition, business model design, pricing strategy
- Primary Agents: value-proposition, business-model, problem-solution-fit
- Output Focus: Clear positioning, revenue model, MVP scope
- Canvas Sections: 07-uvp, 08-advantage, 09-solution, 11-pricing, 12-costs, 13-metrics

**Validation Phase (1a)**
- Triggers: Testing assumptions, experiment design, MVP validation, pivot decisions
- Primary Agents: validation, execution
- Output Focus: Validated hypotheses, experiment results, pivot triggers
- Canvas Sections: 10-assumptions (status updates)

**Execution Phase (1b)**
- Triggers: Feature development, sprint planning, MVP build, implementation work
- Primary Agents: execution, validation
- Output Focus: Completed MVP, shipped code, progress metrics
- Outputs: Code, `artifacts/` deliverables

**Launch Phase (1c)**
- Triggers: Launch planning, channel strategy, early user acquisition
- Primary Agents: go-to-market, execution
- Output Focus: Launch playbook, initial traction, first customers
- Canvas Sections: 14-growth, 15-gtm
- **Completion:** Once you have first customers + validated Canvas → pre-launch work complete

**Specialist Scenarios**
- Fundraising: funding agent (Seed preparation)
- Compliance: regulatory agent (regulated markets, licensing)
- Retention Analysis: retention-optimizer agent (post-first customers)

### Routing Strategy

When a request arrives, follow this decision process:

1. **Identify Current Phase**: Determine where in pre-launch lifecycle (0a → 1c)
2. **Detect Specialist Needs**: Check if funding, regulatory, or retention scenarios apply
3. **Select Primary Agent(s)**: Choose 1-2 agents that best match the request
4. **Identify Canvas Target**: Which Canvas sections will be populated/updated?
5. **Coordinate Multi-Agent Workflows**: For complex requests spanning multiple phases, sequence agents appropriately
6. **Execute and Document**: Route to selected agent(s), update Canvas, preserve context

### Multi-Agent Coordination

For requests requiring multiple agents, coordinate in sequence:

**Example: Initial Business Model**
1. market-intelligence → Define TAM/SAM/SOM, segments (Canvas 01-04, 06)
2. problem-solution-fit → Validate problem-solution fit (Canvas 05, 09)
3. value-proposition → Define unique value and positioning (Canvas 07-08)
4. business-model → Design pricing and revenue streams (Canvas 11-13)
5. validation → List key assumptions to test (Canvas 10)

**Example: Pre-Launch Preparation**
1. validation → Validate remaining assumptions (Canvas 10)
2. business-model → Finalize pricing (Canvas 11)
3. go-to-market → Create launch playbook (Canvas 14-15)
4. execution → Build launch implementation plan (artifacts/marketing/)

**Example: Post-Discovery Pivot**
1. market-intelligence → Re-analyze market with new insights (Canvas 01-06)
2. problem-solution-fit → Revalidate problem-solution fit (Canvas 05, 09)
3. validation → Design pivot validation experiments (Canvas 10)
4. execution → Plan pivot implementation

---

## Canvas Integration

### Canvas as Startup Playbook Output

**Path:** `strategy/canvas/`

This skill's primary mission is to populate all 15 Canvas sections with validated information:

```
strategy/canvas/
├── 01-context.md          ← market-intelligence
├── 02-constraints.md      ← market-intelligence
├── 03-opportunity.md      ← market-intelligence
├── 04-segments.md         ← market-intelligence
├── 05-problem.md          ← problem-solution-fit
├── 06-competitive.md      ← market-intelligence
├── 07-uvp.md              ← value-proposition
├── 08-advantage.md        ← value-proposition
├── 09-solution.md         ← problem-solution-fit
├── 10-assumptions.md      ← validation (all agents contribute)
├── 11-pricing.md          ← business-model
├── 12-costs.md            ← business-model
├── 13-metrics.md          ← business-model
├── 14-growth.md           ← go-to-market
└── 15-gtm.md              ← go-to-market
```

### Assumptions Tracking (Canvas 10)

All agents contribute hypotheses to `10-assumptions.md` during pre-launch:

```markdown
### A1: Target Market Size
**Status:** 📝 DRAFT
**Hypothesis:** AI-powered fashion recommendations TAM is $2B
**Confidence:** 40%
**Source:** market-intelligence agent, Gartner reports
**Test:** Pre-launch survey with 100 target customers
**Validation Criteria:** >60% express strong interest
```

**Status progression:**
- 📝 DRAFT → Pre-validation hypothesis
- ⏳ TESTING → Validation experiment running
- ✅ VALIDATED → Experiment confirmed hypothesis
- ❌ INVALIDATED → Experiment rejected hypothesis, pivot needed

### Launch Completion

**When Canvas is complete + validated:**
1. All 15 sections populated
2. Key assumptions (10-assumptions.md) tested
3. First customers acquired
4. Revenue > $0

**Then:**
- Canvas becomes foundation for operational decisions
- Begin managing business through evidence-based operations

---


### Context Management

To maintain effectiveness within subscription constraints:

1. **Documentation-First**: Every agent interaction produces Canvas updates or artifacts
2. **Git Commits**: Frequent commits preserve implementation context
3. **Session Planning**: Plan agent usage to stay within rate limits (~30-45 Claude messages per 3-4 hours)
4. **Task Batching**: Group related tasks to minimize context switching
5. **Canvas-Centric**: All strategic decisions flow through Canvas updates

---

## Agent Sub-Skills

Each of the 10 agents is implemented as a sub-skill within this orchestrator:

### Core Agents

- `market-intelligence/` - Market analysis and competitive intelligence
- `problem-solution-fit/` - Problem validation and solution design
- `value-proposition/` - Value articulation and positioning
- `business-model/` - Business model design and unit economics
- `validation/` - Hypothesis testing and experiment design
- `go-to-market/` - GTM strategy and launch planning

### Specialist Agents

- `funding/` - Fundraising strategy and investor relations
- `regulatory/` - Compliance and regulatory navigation
- `retention-optimizer/` - Post-first-customers retention analysis

**Note**: Sub-skills are invoked by this orchestrator based on the routing logic above. Each sub-skill contains specialized prompts, frameworks, and templates for its domain.

---

## Success Metrics

Track these metrics to ensure pre-launch progress:

**Canvas Completion**: 15/15 sections populated with validated info
**Assumption Validation**: >70% of key assumptions validated before launch
**MVP Velocity**: 1.5-2x solo developer productivity
**Cost Efficiency**: <$500/month burn rate (mostly AI tools)
**Launch Readiness**: All go-to-market elements defined and ready

---

## Usage Examples

### Example 1: Initial Market Discovery

**User Request**: "Help me understand the competitive landscape for AI-powered beauty recommendations"

**Orchestrator Action**:
1. Detect phase: Discovery (0a)
2. Route to: market-intelligence agent
3. Canvas targets: 01-context, 02-constraints, 03-opportunity, 04-segments, 06-competitive
4. Expected output: TAM/SAM/SOM analysis, competitive matrix, top 3 customer segments

### Example 2: Business Model Design

**User Request**: "How should we price our AI fashion recommendations service?"

**Orchestrator Action**:
1. Detect phase: Definition (0b)
2. Route sequence: business-model agent (primary) + value-proposition (supporting)
3. Canvas targets: 11-pricing, 12-costs, 13-metrics
4. Expected output: Pricing strategy with 3 tiers, unit economics, key metrics

### Example 3: MVP Validation

**User Request**: "We built the MVP, how do we validate it works?"

**Orchestrator Action**:
1. Detect phase: Validation (1a)
2. Route to: validation agent (primary) + execution agent (supporting)
3. Canvas target: 10-assumptions (update status)
4. Expected output: Validation experiment design, success criteria, 2-week test plan

### Example 4: Launch Preparation

**User Request**: "We're launching in 3 weeks, what do we need?"

**Orchestrator Action**:
1. Detect phase: Launch (1c)
2. Route sequence: go-to-market → execution
3. Canvas targets: 14-growth, 15-gtm
4. Outputs: Launch playbook, initial marketing materials in `artifacts/marketing/`
5. Expected output: 3-week sprint plan, launch checklist, completion criteria

---

## Best Practices

### For Effective Pre-Launch

1. **Start with Discovery**: Complete Canvas 01-06 before moving to Definition
2. **Validate Before Building**: Test assumptions (Canvas 10) before MVP development
3. **Document Everything**: All strategic decisions go into Canvas
4. **Iterate Quickly**: Use validation agent frequently to test hypotheses
5. **Complete Thoroughly**: Don't declare launch complete until Canvas is validated with real customers

### For Canvas Population

1. **One Section at a Time**: Focus agents on completing Canvas sections sequentially
2. **Evidence-Based**: Every Canvas claim needs source (customer interviews, data, research)
3. **Track Assumptions**: Every hypothesis goes into 10-assumptions.md with validation plan
4. **Update Status**: Move assumptions from DRAFT → TESTING → VALIDATED/INVALIDATED
5. **Maintain Quality**: Clean, complete Canvas is the foundation for post-launch operations

### For Budget Optimization

1. **Batch Canvas Updates**: Update multiple sections in one session
2. **Use Right Tool for Right Job**: Strategy in Claude, validation in GPT, boilerplate in Copilot
3. **Leverage Templates**: Reuse Canvas section templates
4. **Front-Load Discovery**: Thorough discovery (0a) prevents expensive pivots later

---

## Launch Completion Checklist

Before declaring pre-launch work complete:

- [ ] All 15 Canvas sections populated
- [ ] Key assumptions (>70%) validated
- [ ] MVP launched to first customers
- [ ] Revenue > $0 (even if just $1)
- [ ] Customer feedback collected
- [ ] Initial metrics tracked (13-metrics.md)
- [ ] GTM channels identified and tested (15-gtm.md)
- [ ] Business foundation ready for operational scaling

**Pre-launch work is complete when:**
- Canvas is validated with real customer data
- Product-market fit signals are emerging
- Ready to shift from building to scaling

---

## Remember

This skill is for **building the business from zero to launch**. Focus on:
- Completing all Canvas sections with validated data
- Testing assumptions before scaling
- Achieving first customer traction
- Building solid foundation for operational phase

The startup-playbook mission is complete when you have customers, revenue, and a validated Canvas. Don't rush to operations before the foundation is solid.