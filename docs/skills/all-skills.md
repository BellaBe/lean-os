# LeanOS Skills Reference

Complete reference of AI skills for business operations.

## Foundation Skills

### foundation-builder
**Purpose:** Orchestrate Canvas population through 5 phases  
**Phases:** Discovery → Definition → Validation → Execution → Launch  
**Agents:** 10 (7 core, 3 specialist)  
**Output:** Complete 15-section Canvas  
**Docs:** See [Canvas Setup](../foundation/canvas-setup.md)

---

## Sales Skills

### Strategy Skills

**icp-generator**
- Defines target customers per segment
- Input: Canvas 04-segments.md
- Output: research/customer/icp/{segment}-icp.yaml

**sales-narrative**
- Creates messaging per segment
- Input: Canvas + ICP
- Output: threads/sales/narrative/{segment}/

### Execution Skills

**sales-execution** (orchestrator)
- Coordinates sales workflow
- Subskills: 5

**materials-generation**
- Generates segment-specific materials
- Output: Pitch decks, scripts, templates

**prospect-research**
- Finds companies matching ICP
- Uses web_search
- Output: Prospect lists (CSV)

**contact-finding**
- Identifies decision-makers
- Uses LinkedIn, websites
- Output: Contact lists (CSV)

**outreach-sequencing**
- Creates email/phone cadences
- Output: Sequence templates

**qualification-support**
- Prepares for discovery calls
- Output: Call prep docs

---

## Marketing Skills

### Strategy Skills

**marketing-narrative**
- Defines content strategy
- Input: Canvas + Sales narratives
- Output: artifacts/marketing/narrative/

### Execution Skills

**marketing-execution** (orchestrator)
- Coordinates content workflow
- Subskills: 5

**content-strategy**
- Scans threads for opportunities
- Daily automated scan
- Output: Prioritized opportunities

**content-generation**
- Creates educational drafts
- Uses content patterns
- Output: Blog, case studies, guides

**seo-optimization**
- Optimizes for search
- Automated
- Output: SEO-optimized content

**content-distribution**
- Publishes multi-channel
- Adds UTM tracking
- Output: Published content

**performance-tracking**
- Measures impact
- Schedule: Day 7, 30, 90
- Output: Performance reports

---

## Orchestration Skills

### causal-flow
**Purpose:** 6-stage decision framework  
**Stages:** Input → Hypothesis → Implication → Decision → Actions → Learning  
**Thread types:** Business, sales, marketing  
**Key feature:** Stage 6 auto-updates Canvas  
**Docs:** See [Causal Flow](../operations/causal-flow.md)

### ops-dashboard
**Purpose:** Auto-generate daily interface  
**Outputs:** today.md, velocity.md, patterns.md, changes.md  
**Schedule:** Daily automated  
**Status:** Planned (Phase 4)

---

## Engineering Skills

### category-theoretic-system-design
**Purpose:** Compositional system design using category theory  
**Workflow:** 8 skills (ADT analyzer → code generator)  
**Use case:** Building complex microservices with correctness guarantees

### standardization-layer
**Purpose:** Apply uniform cross-cutting concerns  
**Applies:** Auth, validation, errors, observability, rate limiting  
**Use case:** Consistent middleware across microservices

**Note:** Engineering skills separate from business operations.

---

For workflow details, see:
- [Sales Workflow](../operations/sales-workflow.md)
- [Marketing Workflow](../operations/marketing-workflow.md)
- [How It Works](../overview/how-it-works.md)