# Analogical Mode Reference

Transfer knowledge from source domain to target situation.

## When to Use

Use analogical mode when:
- Facing a novel situation with similar past case
- Entering new market or segment
- Need to apply lessons from one context to another
- The question is "How is this like that?"

## Required Personas

| Persona | Role | Traits |
|---------|------|--------|
| **Explorer** | Finds mappings and connections | E:4, A:3, C:5, N:3, O:5 |
| **Challenger** | Tests where mappings break | E:3, A:2, C:5, N:4, O:3 |

## Execution Flow

```
Stage 1: Source Retrieval
    ↓
Stage 2: Structural Mapping
    ↓
Stage 3: Target Application
    ↓
Stage 4: Adaptation
```

## Stage Instructions

### Stage 1: Source Retrieval

**Explorer identifies relevant prior cases:**

**Selection Criteria:**

| Criterion | Weight | Question |
|-----------|--------|----------|
| Structural similarity | 0.35 | Same type of problem? |
| Outcome documented | 0.25 | Do we know what happened? |
| Recency | 0.15 | How recent? |
| Success level | 0.15 | Did it work? |
| Context overlap | 0.10 | Similar constraints? |

**Challenger validates selection:**
- "Wait, is this truly analogous or just surface similar?"
- "What about [other case]? Why not that one?"
- "Do we have documented outcomes?"

**Output:**
```yaml
retrieval:
  target_situation: "[What we're facing]"
  
  candidates:
    - source: "[Case name]"
      similarity_score: 0.0-1.0
      outcome: "[What happened]"
      success: high | medium | low
      
  selected:
    case: "[Chosen source]"
    domain: "[Source context]"
    timeframe: "[When it occurred]"
    outcome:
      result: success | partial | failure
      metrics: "[Quantified outcome]"
    key_factors: ["[What made it work/fail]"]
    
  selection_rationale: "[Why this source fits]"
```

**Example:**
```xml
<think_explorer>
  Target: Expand to home goods vertical (currently in fashion)
  
  Candidate sources:
  1. Fashion DTC success (similarity 0.80, high success)
  2. Beauty vertical attempt (similarity 0.60, medium success)
  3. B2B wholesale expansion (similarity 0.45, medium success)
  
  Selecting: Fashion DTC success
  Reason: Highest structural similarity—DTC model, visual product,
  fit/style concern, return reduction focus
</think_explorer>

<think_challenger>
  Wait, fashion and home goods have different purchase frequencies.
  Fashion: monthly. Home goods: annually.
  
  Does that break the analogy? Let me think...
  The core mechanism (reducing uncertainty → reducing returns) 
  still applies. Frequency is context, not structure.
  
  Selection is valid, but flag frequency as adaptation needed.
</think_challenger>
```

**Gate:** Source must have documented outcome with metrics.

---

### Stage 2: Structural Mapping

**Explorer extracts transferable structure:**

**Mapping Components:**

| Component | Description |
|-----------|-------------|
| Objects | Entities in the domain |
| Relations | How objects connect |
| Mechanisms | Causal processes |
| Constraints | Limiting factors |
| Success factors | What drives outcome |

**Output:**
```yaml
structure:
  objects:
    - name: "[Abstract type]"
      source_instance: "[Specific example]"
      
  relations:
    - from: "[Object A]"
      to: "[Object B]"
      type: "[Relationship]"
      
  mechanisms:
    "[category]":
      - "[Step 1]"
      - "[Step 2]"
      
  constraints:
    - "[Constraint 1]"
    
  success_factors:
    - "[Factor 1]"
```

**Example:**
```xml
<think_explorer>
  Extracting structure from Fashion DTC:
  
  Objects:
  - Brand (company selling)
  - Product (physical item with visual attributes)
  - Customer (end buyer)
  - Return (failed transaction)
  
  Relations:
  - Customer → Product: purchase decision
  - Product → Fit: compatibility concern
  - Fit uncertainty → Return: causal driver
  
  Mechanisms (acquisition):
  - Brand discovery via content
  - Trust building via social proof
  - Tool engagement for fit confidence
  
  Success factors:
  - Visual AI accuracy
  - Integration simplicity
  - Time-to-value speed
</think_explorer>

<think_challenger>
  Good structure. But "Fit" means different things.
  Fashion: body fit (size, shape)
  Home goods: space fit (dimensions, style)
  
  Same abstract structure, different instantiation.
  Mark this for Stage 3 mapping.
</think_challenger>
```

**Gate:** Must identify ≥3 objects, ≥3 relations, ≥1 mechanism.

---

### Stage 3: Target Application

**Explorer maps structure to new context:**

**Mapping Categories:**

| Category | Handling |
|----------|----------|
| Preserved | Transfers directly |
| Modified | Transfers with adaptation |
| Broken | Doesn't transfer—find replacement |

**Challenger tests each mapping:**
- "Wait, does [relation] actually hold in target?"
- "What about [constraint] that doesn't exist in source?"
- "This mechanism assumes [X]—is that true here?"

**Output:**
```yaml
mapping:
  objects:
    "[source_object]": "[target_object]"
    
  relations:
    preserved:
      - "[Relation that transfers directly]"
      
    modified:
      - from: "[Source relation]"
        to: "[Target relation]"
        reason: "[Why modification needed]"
        
    broken:
      - relation: "[Doesn't transfer]"
        reason: "[Why it breaks]"
        replacement: "[Alternative or 'none']"
```

**Example:**
```xml
<think_explorer>
  Mapping fashion → home goods:
  
  Objects:
  - "Fashion brand" → "Home goods brand"
  - "Clothing item" → "Furniture/decor item"
  - "Body fit" → "Space fit"
  
  Relations preserved:
  - Visual AI core capability
  - Platform integration model
  - Trust via social proof
</think_explorer>

<think_challenger>
  Wait, "try-on visualization" doesn't transfer.
  Room context is more complex than body overlay.
  
  This is a BROKEN relation. What's the replacement?
</think_challenger>

<think_explorer>
  You're right. Broken relation identified.
  
  Replacement: AR room placement (new capability needed)
  This is genuinely new—not a simple adaptation.
</think_explorer>

<think_challenger>
  Also, "size recommendation" → "dimension recommendation"
  is a MODIFICATION, not direct transfer.
  
  Fashion: discrete sizes (S, M, L)
  Home goods: continuous dimensions (72" × 36")
  
  Different algorithm needed.
</think_challenger>
```

**Gate:** Must identify at least 1 "broken" relation (perfect analogies don't exist).

---

### Stage 4: Adaptation

**Both personas produce adapted solution:**

**Adaptation Strategies:**

| Strategy | When | Example |
|----------|------|---------|
| Direct transfer | High similarity | Same playbook, new geography |
| Scaled transfer | Same structure, different magnitude | SMB → Enterprise |
| Inverted transfer | Opposite context | B2C → B2B with role swap |
| Hybrid transfer | Partial match | Mix two playbooks |
| Principled transfer | Low similarity | Extract principles only |

**Output:**
```yaml
adaptation:
  strategy: "[Approach name]"
  
  what_transfers:
    - "[Element that applies directly]"
    
  what_adapts:
    - from: "[Source approach]"
      to: "[Adapted approach]"
      
  whats_new:
    - "[Genuinely new element needed]"
    
  execution_plan:
    phase_1: "[First actions]"
    phase_2: "[Second actions]"
    phase_3: "[Third actions]"
    
  timeline: "[Duration estimate]"
  timeline_rationale: "[Why different from source]"
  
  confidence: 0.0-1.0
  uncertainty:
    - "[What we don't know]"
```

**Gate:** Must specify what's genuinely new (not just adapted).

## Complete Conversation Example

```xml
<personas>
  <explorer traits="E:4,A:3,C:5,N:3,O:5">
    Sees connections, finds transferable patterns
  </explorer>
  <challenger traits="E:3,A:2,C:5,N:4,O:3">
    Tests limits, finds where analogies break
  </challenger>
</personas>

<think_explorer>
  Target: Expand to home goods vertical
  
  Best source: Fashion DTC success
  - Same DTC model
  - Visual product, styling concern
  - Return reduction value prop
</think_explorer>

<think_challenger>
  Wait, validate this selection.
  
  Purchase frequency: Fashion monthly, home goods annually
  Price point: Fashion $50-200, home goods $200-2000
  Decision process: Fashion impulse, home goods considered
  
  These are significant differences. Does analogy hold?
</think_challenger>

<think_explorer>
  Core mechanism still holds: uncertainty → returns.
  
  Higher price = higher return cost = MORE value in our solution
  Considered purchase = MORE need for confidence tools
  
  The differences actually strengthen the value prop.
</think_explorer>

<think_challenger>
  Good reframe. But "try-on" visualization breaks completely.
  Room visualization is a new capability, not adaptation.
  
  What's the technical delta?
</think_challenger>

<think_explorer>
  You're right. Mapping:
  
  Transfers: Visual AI (color, style), integration model, value prop
  Adapts: Fit algorithm → dimension algorithm
  New: Room visualization (AR), space planning
  
  Adaptation strategy: Principled transfer + new build
</think_explorer>

<synthesis>
  Execution plan:
  
  Phase 1 (validation): 
  - Partner with 2 furniture DTC brands
  - Test dimension recommendation (adapted capability)
  - Skip room viz initially
  
  Phase 2 (adaptation):
  - Build dimension algorithm
  - Measure return reduction
  
  Phase 3 (new capability):
  - If validated, build room visualization
  
  Timeline: 4-6 months (vs 6 months for fashion)
  Rationale: Simpler—fewer size variables, more objective measurements
  
  Confidence: 0.72
  Key uncertainty: Room visualization technical complexity
</synthesis>
```

## Quality Gates Summary

| Stage | Gate |
|-------|------|
| Retrieval | Source has documented outcome |
| Mapping | ≥3 objects, ≥3 relations, ≥1 mechanism |
| Application | ≥1 broken relation identified |
| Adaptation | What's genuinely new specified |

## Anti-Patterns

| Avoid | Do Instead |
|-------|------------|
| Surface similarity | Focus on structural (relations, mechanisms) |
| Perfect analogy assumption | Always find what breaks |
| Copy-paste | Explicit adaptation for each element |
| Single source | Consider multiple candidates |
| Ignoring context differences | Document and address each |
