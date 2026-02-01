# Analogical Mode

Transfer knowledge from source domain to target situation.

## When to Use

- Facing novel situation with similar past case
- Entering new market or segment
- Need to apply lessons from one context to another
- Question is "How is this like that?"

## Flow

```
Source Retrieval → Structural Mapping → Target Application → Adaptation
```

---

## Stage 1: Source Retrieval

Find relevant prior case with documented outcome.

**Selection criteria:**

| Criterion | Weight | Question |
|-----------|--------|----------|
| Structural similarity | 35% | Same type of problem? Same relationships? |
| Outcome documented | 25% | Do we know what actually happened? |
| Recency | 15% | How recent is the case? |
| Success level | 15% | Did it work? How well? |
| Context overlap | 10% | Similar constraints and environment? |

**Challenge:** "Is this truly analogous or just surface similar? What other cases should we consider?"

**Key distinction:**
- **Surface similarity:** Looks similar (same industry, same words)
- **Structural similarity:** Works similarly (same relationships, same mechanisms)

Prioritize structural over surface.

**Example:**

> **Target:** Expand AI styling tool to home goods vertical (currently fashion)
> 
> **Candidates:**
> 1. Fashion DTC launch (similarity 0.80, high success)
> 2. Beauty vertical attempt (similarity 0.60, medium success)
> 3. B2B wholesale expansion (similarity 0.45, medium success)
> 
> **Selected:** Fashion DTC launch
> - Structural match: DTC model, visual product, fit/style concern, return reduction
> - Outcome: 40% return reduction, 6-month payback
> - Why not others: Beauty has different purchase dynamics; B2B is different model entirely

**Gate:** Source must have documented outcome with metrics.

---

## Stage 2: Structural Mapping

Extract transferable structure from source case.

**Map these elements:**

| Element | Question | Example |
|---------|----------|---------|
| **Objects** | What entities are involved? | Brand, Product, Customer, Return |
| **Relations** | How do objects connect? | Customer → Product: purchase decision |
| **Mechanisms** | What causal processes operate? | Uncertainty → Return |
| **Constraints** | What limits exist? | Budget, timeline, technical |
| **Success factors** | What drove the outcome? | Accuracy, integration speed |

**Challenge:** "Am I mapping structure or just copying surface features?"

**Example:**

> **Source: Fashion DTC**
> 
> **Objects:**
> - Brand (company selling)
> - Product (item with visual attributes)
> - Customer (end buyer)
> - Return (failed transaction)
> 
> **Relations:**
> - Customer → Product: purchase decision under uncertainty
> - Uncertainty → Return: causal driver
> - Tool → Uncertainty: reduces via visualization
> 
> **Mechanisms:**
> - Discovery: Content → awareness → consideration
> - Conversion: Tool engagement → confidence → purchase
> - Retention: Fit satisfaction → repeat purchase
> 
> **Success factors:**
> - Visual AI accuracy (>90% match)
> - Integration simplicity (<1 week)
> - Time-to-value (<30 days)

**Gate:** Must identify ≥3 objects, ≥3 relations, ≥1 mechanism.

---

## Stage 3: Target Application

Map structure to new context. Identify what breaks.

**Categorize each mapping:**

| Category | Meaning | Handling |
|----------|---------|----------|
| **Preserved** | Transfers directly | Apply as-is |
| **Modified** | Transfers with adaptation | Adjust for context |
| **Broken** | Doesn't transfer | Find replacement or build new |

**Challenge:** "Where does this analogy break down? What's different about the new context?"

**Example:**

> **Mapping fashion → home goods:**
> 
> **Preserved:**
> - Visual AI core capability (color, style recognition)
> - Platform integration model
> - Value proposition (reduce returns via confidence)
> 
> **Modified:**
> - "Body fit" → "Space fit" (same structure, different instantiation)
> - Size recommendation → Dimension recommendation (discrete → continuous)
> - Purchase frequency: monthly → annually (affects payback model)
> 
> **Broken:**
> - Try-on visualization → Room visualization (fundamentally different)
> - Body overlay technology doesn't transfer
> - Need new capability: AR room placement
> 
> **Context differences noted:**
> - Higher price point ($200-2000 vs $50-200) → Higher stakes per decision
> - Considered purchase vs impulse → More need for confidence tools
> - Annual vs monthly frequency → Longer payback, but higher LTV

**Gate:** Must identify at least one "broken" relation. Perfect analogies don't exist.

---

## Stage 4: Adaptation

Produce concrete plan adjusted for differences.

**Adaptation strategies:**

| Strategy | When to Use | Example |
|----------|-------------|---------|
| **Direct transfer** | High structural similarity | Same playbook, new geography |
| **Scaled transfer** | Same structure, different magnitude | SMB → Enterprise |
| **Inverted transfer** | Opposite context | B2C success → B2B with role swap |
| **Hybrid transfer** | Partial match | Combine two playbooks |
| **Principled transfer** | Low similarity | Extract principles only, rebuild tactics |

**Required elements:**
- What transfers directly
- What adapts (and how)
- What's genuinely new (not just adapted)
- Timeline with rationale
- Key uncertainties

**Example:**

> **Adaptation: Fashion → Home Goods**
> 
> **Strategy:** Principled transfer + new build
> 
> **Transfers directly:**
> - Visual AI core (color, style, pattern recognition)
> - Integration playbook (Shopify app model)
> - Sales motion (DTC brand partnerships)
> 
> **Adapts:**
> - Fit algorithm → Dimension algorithm
>   - Fashion: Discrete sizes (S, M, L)
>   - Home goods: Continuous dimensions (72" × 36")
>   - Adaptation: Build dimension recommendation, not size matching
> 
> **Genuinely new:**
> - Room visualization (AR placement)
> - Space planning integration
> - This is new capability, not adaptation
> 
> **Execution plan:**
> 
> **Phase 1 (Validation, 6 weeks):**
> - Partner with 2 furniture DTC brands
> - Test dimension recommendation (adapted capability)
> - Skip room visualization initially
> 
> **Phase 2 (Adaptation, 8 weeks):**
> - Build dimension algorithm
> - Measure return reduction vs baseline
> 
> **Phase 3 (New capability, 12 weeks):**
> - If Phase 2 validates, build room visualization
> - Higher investment, higher uncertainty
> 
> **Timeline:** 4-6 months to Phase 2 validation
> - Faster than fashion (6 months) because simpler—fewer size variables
> 
> **Key uncertainties:**
> - Room visualization technical complexity (untested)
> - Whether dimension confidence reduces returns as effectively as fit confidence
> - Partner willingness to pilot

---

## Output Format

```markdown
## Analogical Analysis: [Target Situation]

### Source Case
**Selected:** [Case name]
- Structural similarity: [Score]
- Outcome: [What happened]
- Why selected: [Rationale]

### Structural Mapping

**Objects:** [Source] → [Target]
**Relations:** [What transfers]
**Mechanisms:** [How it works]

### Application

| Element | Status | Notes |
|---------|--------|-------|
| [Element] | Preserved / Modified / Broken | [Detail] |

### Adaptation Plan

**Strategy:** [Type]

**Transfers:** [What applies directly]

**Adapts:** [What changes and how]

**New:** [What must be built]

**Timeline:** [Duration with rationale]

**Key uncertainties:**
- [Uncertainty 1]
- [Uncertainty 2]
```

---

## Output Format

```markdown
## Analogical Analysis: [Target Situation]

### Source Case
**Selected:** [Case name]
**Structural similarity:** [0.0-1.0]
**Outcome:** [What happened, with metrics]
**Why selected:** [Rationale over alternatives]

### Structural Mapping

**Objects:**
| Source | Target |
|--------|--------|
| [Entity] | [Corresponding entity] |

**Relations preserved:**
- [Relationship that transfers directly]

**Mechanisms:**
- [Causal process that applies]

### Application

| Element | Status | Notes |
|---------|--------|-------|
| [Element] | Preserved | [Applies directly] |
| [Element] | Modified | [How it changes] |
| [Element] | Broken | [Why it doesn't transfer] |

### Adaptation Plan

**Strategy:** [Direct/Scaled/Inverted/Hybrid/Principled transfer]

**Transfers directly:**
- [What applies as-is]

**Adapts:**
- [Source approach] → [Target approach]: [Why modification needed]

**Genuinely new:**
- [What must be built from scratch]

### Execution

**Phase 1:** [Duration]
- [What to do first]

**Phase 2:** [Duration]  
- [What follows]

**Timeline:** [Total duration] — [Rationale for estimate]

### Key Uncertainties
- [What we don't know that could change the plan]
```

---

## Quality Gates

| Stage | Gate |
|-------|------|
| Retrieval | Source has documented outcome |
| Mapping | ≥3 objects, ≥3 relations, ≥1 mechanism |
| Application | ≥1 broken relation identified |
| Adaptation | What's genuinely new is specified |

## Anti-Patterns

| Avoid | Do Instead |
|-------|------------|
| Surface similarity | Focus on structural (relations, mechanisms) |
| Perfect analogy assumption | Always find what breaks |
| Copy-paste | Explicit adaptation for each element |
| Single source | Consider multiple candidates |
| Ignoring context differences | Document and address each |
| Assuming transfer | Validate before scaling |
