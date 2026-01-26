# Dialectical Mode Reference

Synthesize opposing positions through multi-voice dialogue.

## When to Use

Use dialectical mode when:
- Stakeholders disagree on direction
- Trade-offs between valid positions exist
- Need to resolve conflicting requirements
- The question is "How do we resolve this?"

## Required Personas

| Persona | Role | Traits |
|---------|------|--------|
| **Thesis Voice** | Advocates first position | Varies by stakeholder |
| **Antithesis Voice** | Advocates counter-position | Low A (creates friction) |
| **Integrator** | Synthesizes resolution | E:3, A:4, C:5, N:3, O:4 |

## Execution Flow

```
Stage 1: Thesis (steel-man first position)
    ↓
Stage 2: Antithesis (steel-man counter-position)
    ↓
Stage 3: Dialogue (≥3 exchanges)
    ↓
Stage 4: Synthesis (integrate, don't compromise)
```

## Core Principles

### Steel-Man, Don't Straw-Man

Represent each position at its strongest:
- Assume good faith
- Find kernel of truth
- Best possible articulation

### Synthesis ≠ Compromise

| Invalid | Valid |
|---------|-------|
| Split the difference | Integrate at higher level |
| Take turns | Find frame that accommodates both |
| Declare winner | Address underlying concerns |
| Average positions | Transcend original framing |

## Stage Instructions

### Stage 1: Thesis

**Thesis Voice does:**
1. State position clearly
2. Identify underlying concern (often different from stated position)
3. Present supporting evidence
4. Explain implications if adopted

**Output:**
```yaml
thesis:
  persona:
    id: P1
    traits: {E: int, A: int, C: 5, N: int, O: int}
    represents: "[Stakeholder or perspective]"
    
  position:
    statement: "[Core claim]"
    underlying_concern: "[What this is really about]"
    
  evidence:
    - claim: "[Supporting point]"
      source: "[Evidence]"
      strength: 0.0-1.0
      
  implications:
    if_adopted: "[Consequences]"
    risks: ["[Potential downsides]"]
    benefits: ["[Potential upsides]"]
```

**Format:**
```xml
<think_thesis traits="E:2,A:4,C:5,N:2,O:3" represents="engineering">
  Position: Rebuild platform before new features.
  
  Underlying concern: Sustainable development velocity.
  
  Evidence:
  - Deploy time increased 300% YoY
  - 40% of sprint on workarounds
  - 3 critical incidents from architecture
  
  If adopted: 6-month rebuild, then 3x velocity.
</think_thesis>
```

**Gate:** Must state underlying concern, not just position.

---

### Stage 2: Antithesis

**Antithesis Voice does:**
1. State counter-position with equal strength
2. Identify underlying concern
3. Directly challenge thesis assumptions
4. Present counter-evidence

**Required:** Open with discourse marker challenging thesis.

**Output:**
```yaml
antithesis:
  persona:
    id: P2
    traits: {E: int, A: 2, C: 5, N: int, O: int}  # Low A required
    represents: "[Counter stakeholder]"
    
  position:
    statement: "[Counter claim]"
    underlying_concern: "[What this protects]"
    
  challenge:
    marker: "Wait | But | No | Actually"
    target: "[What's being challenged]"
    
  critique_of_thesis:
    - assumption: "[Thesis assumes X]"
      counter: "[But actually Y]"
      
  evidence:
    - claim: "[Counter point]"
      source: "[Evidence]"
```

**Format:**
```xml
<think_antithesis traits="E:4,A:2,C:5,N:4,O:4" represents="sales">
  Wait, 6 months without features is a death sentence.
  
  Position: Deliver Q2 features, defer rebuild.
  
  Underlying concern: Revenue target attainment.
  
  Thesis assumes: Rebuild must happen all at once.
  Counter: Incremental improvement is possible.
  
  Evidence:
  - $2M pipeline depends on Q2 features
  - Competitor launching similar features March
  - Board expects feature delivery, not infrastructure
</think_antithesis>
```

**Gate:** Must include discourse marker and direct challenge to thesis assumption.

---

### Stage 3: Dialogue

**Both voices engage in back-and-forth:**

**Minimum:** 3 exchanges (T → A → T → A → T → A)

**Each turn must:**
- Reference previous turn (not talk past)
- Add new information or angle
- Include discourse markers when shifting
- Move toward or defend position

**Valid Patterns:**

| Pattern | Example |
|---------|---------|
| Partial concession | "You're right that X, but..." |
| Evidence challenge | "The data shows otherwise..." |
| Reframe | "What if we think of it as..." |
| Condition | "I could accept that if..." |

**Invalid Patterns:**

| Pattern | Why Invalid |
|---------|-------------|
| "I agree, and..." | No tension |
| "Building on that..." | No challenge |
| "Yes, exactly..." | Sycophantic |
| Ignoring prior turn | Not engaging |

**Example dialogue:**
```xml
<think_thesis>
  You're right that 6 months is risky. But "figure it out later"
  is how we got here.
  
  What if we don't frame as all-or-nothing?
  - Identify features buildable on new architecture
  - Rebuild incrementally (strangler fig)
  - Ship features AND make progress
</think_thesis>

<think_antithesis>
  Actually, that could work. But I need guarantees.
  
  - Which 3 features are must-haves for Q2?
  - Can those be built on new modules?
  - What's realistic timeline?
  
  Not all 5 planned features—but top 3.
</think_antithesis>

<think_thesis>
  Let me check the mapping...
  
  Features 1, 2, 4 can go on new architecture.
  Features 3, 5 require old system extensions.
  
  Proposal: Build 1, 2, 4 on new. Defer 3, 5.
  Timeline: 4 months features + foundation, then continue.
</think_thesis>

<think_antithesis>
  Hmm, that means dropping 2 features.
  
  But if top 3 protect the $2M pipeline...
  And we get platform progress...
  
  I can accept that if we do joint prioritization
  to confirm which 3 matter most.
</think_antithesis>
```

**Gate:** ≥3 exchanges, each referencing prior turn.

---

### Stage 4: Synthesis

**Integrator produces resolution:**

**Synthesis Types:**

| Type | When | Example |
|------|------|---------|
| Integration | Both can coexist | "Do A AND B by [method]" |
| Sequencing | Temporal resolution | "First A, then B" |
| Segmentation | Context-dependent | "A for X, B for Y" |
| Reframing | False dichotomy | "Real question is C" |
| Transcendence | Higher goal | "Both serve Z" |

**Resolution must:**
- Address thesis's underlying concern
- Address antithesis's underlying concern
- Acknowledge trade-offs explicitly
- Get commitment from both voices

**Output:**
```yaml
synthesis:
  resolution_type: integration | sequencing | segmentation | reframing | transcendence
  
  integrated_position:
    statement: "[What we will do]"
    frame: "[How this resolves tension]"
    
  thesis_addressed:
    concern: "[P1's underlying concern]"
    how_met: "[How synthesis addresses it]"
    
  antithesis_addressed:
    concern: "[P2's underlying concern]"
    how_met: "[How synthesis addresses it]"
    
  trade_offs:
    - trade_off: "[What we're giving up]"
      accepted_by: "[Which voice]"
      mitigation: "[How we reduce impact]"
      
  commitments:
    - voice: P1
      commits_to: "[Specific commitment]"
    - voice: P2
      commits_to: "[Specific commitment]"
      
  confidence: 0.0-1.0
```

**Format:**
```xml
<think_integrator>
  Synthesis: Strangler fig pattern—rebuild incrementally 
  while delivering priority features.
  
  Resolution type: INTEGRATION
  
  Thesis (engineering) addressed:
  - Concern: Sustainable velocity
  - How: Rebuild happens, modularly. New features on new foundation.
  
  Antithesis (sales) addressed:
  - Concern: Revenue targets
  - How: Top 3 features in Q2. No 6-month freeze.
  
  Trade-offs:
  - Features 3, 5 deferred (accepted by sales with prioritization input)
  - Rebuild takes 9 months not 6 (accepted by eng given continuous delivery)
  
  Commitments:
  - Engineering: Deliver features 1, 2, 4 on new modules by Q2
  - Sales: Accept 3 features instead of 5, joint prioritization
</think_integrator>
```

**Gate:** Both voices must explicitly acknowledge synthesis.

## Complete Example

```xml
<personas>
  <thesis traits="E:2,A:4,C:5,N:2,O:3" represents="engineering">
    Values sustainability, long-term velocity
  </thesis>
  <antithesis traits="E:4,A:2,C:5,N:4,O:4" represents="sales">
    Values delivery, market timing
  </antithesis>
  <integrator traits="E:3,A:4,C:5,N:3,O:4">
    Finds resolution that serves both
  </integrator>
</personas>

<think_thesis>
  We need platform rebuild before features.
  
  Evidence: 300% deploy time increase, 40% sprint on workarounds.
  Underlying concern: Team velocity is degrading unsustainably.
</think_thesis>

<think_antithesis>
  Wait, 6 months without features means losing deals.
  
  $2M pipeline at risk. Competitor launching March.
  Underlying concern: We can't miss revenue targets.
</think_antithesis>

<think_thesis>
  You're right about risk. But what if incremental?
  
  Strangler fig: rebuild while shipping. Not all-or-nothing.
</think_thesis>

<think_antithesis>
  Actually, that could work. Which features on new architecture?
  
  Need top 3 committed for Q2. Not all 5.
</think_antithesis>

<think_thesis>
  Features 1, 2, 4 can go on new modules.
  3, 5 need old system—defer those.
</think_thesis>

<think_antithesis>
  Dropping 2 features is painful but acceptable
  if we jointly prioritize to confirm right 3.
</think_antithesis>

<think_integrator>
  Synthesis: Incremental rebuild + priority features
  Type: INTEGRATION
  
  Engineering gets: Platform progress, new foundation
  Sales gets: Top 3 features, no freeze
  
  Trade-off: 2 features deferred, rebuild takes 9 months
  
  Commitments confirmed by both parties.
  Confidence: 0.78
</think_integrator>
```

## Quality Gates Summary

| Stage | Gate |
|-------|------|
| Thesis | Underlying concern stated |
| Antithesis | Discourse marker + assumption challenge |
| Dialogue | ≥3 exchanges, each references prior |
| Synthesis | Both concerns addressed, both commit |

## Anti-Patterns

| Avoid | Do Instead |
|-------|------------|
| Straw-man positions | Steel-man each side |
| Pleasant agreement | Require low-A antithesis |
| Mushy middle | Force specific resolution type |
| Unacknowledged trade-offs | Explicit cost + who accepts |
| Implicit commitment | Both voices confirm |
