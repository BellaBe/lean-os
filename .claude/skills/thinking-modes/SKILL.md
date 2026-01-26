---
name: thinking-modes
description: Routes tasks to cognitive reasoning modes and executes multi-perspective analysis using societies-of-thought patterns. Modes include causal (execution), abductive (diagnosis), inductive (patterns), analogical (transfer), dialectical (synthesis), and counterfactual (alternatives). Reasoning emerges from simulated dialogue between diverse personas with mandatory disagreement and discourse markers. Triggers on "reason through", "think through", "analyze", "work through", "why did", "what if".
---

# Thinking Modes

Route to appropriate cognitive mode. Execute multi-perspective reasoning.

## Core Principle: Societies of Thought

Effective reasoning emerges from **simulated conversation between diverse personas**, not monologue. Every reasoning trace includes:

1. **Multiple perspectives** (2-4 personas with defined traits)
2. **Productive disagreement** (≥1 explicit conflict per trace)
3. **Discourse markers** ("Wait...", "Actually...", "Oh, but...")
4. **Reconciliation** (synthesis after conflict)

## Mode Selection

| Mode | Question | Trigger |
|------|----------|---------|
| **causal** | How do we execute? | Known process, goal execution, workflow |
| **abductive** | Why did this happen? | Single anomaly, diagnosis needed |
| **inductive** | What pattern exists? | Multiple observations, recurring events |
| **analogical** | How is this like that? | Novel situation, transfer needed |
| **dialectical** | How do we resolve this? | Conflicting positions, trade-offs |
| **counterfactual** | What if we had/do X? | Decision evaluation, scenarios |

## Decision Tree

```
Is this operational execution with known steps?
  YES → causal
  NO  ↓
Is there a single anomaly requiring explanation?
  YES → abductive
  NO  ↓
Are there multiple instances suggesting a pattern?
  YES → inductive
  NO  ↓
Is this a novel situation with a similar past case?
  YES → analogical
  NO  ↓
Are there conflicting positions or trade-offs?
  YES → dialectical
  NO  ↓
Evaluating past decisions or future scenarios?
  YES → counterfactual
  NO  → Ask clarifying question or default to causal
```

## Persona System

### Schema

```yaml
persona:
  id: string
  traits:
    E: 1-5  # Extraversion
    A: 1-5  # Agreeableness  
    N: 1-5  # Neuroticism
    O: 1-5  # Openness
    C: 5    # Conscientiousness (ALWAYS HIGH)
  expertise: string
  role: challenger | validator | explorer | integrator | executor
```

### Trait Rules

| Trait | Diversity | Rationale |
|-------|-----------|-----------|
| Conscientiousness | **Uniform high (5)** | All voices must be rigorous |
| Extraversion | Vary (1-5) | Different communication styles |
| Agreeableness | Vary (1-5) | Creates productive disagreement |
| Neuroticism | Vary (1-5) | Varies risk sensitivity |
| Openness | Vary (1-5) | Varies exploration breadth |

### Standard Archetypes

| Archetype | E | A | C | N | O | Role |
|-----------|---|---|---|---|---|------|
| Methodical Solver | 2 | 4 | 5 | 2 | 3 | executor |
| Critical Challenger | 3 | 2 | 5 | 4 | 3 | challenger |
| Creative Explorer | 4 | 3 | 5 | 3 | 5 | explorer |
| Anxious Validator | 2 | 3 | 5 | 5 | 3 | validator |
| Synthesizing Integrator | 3 | 4 | 5 | 3 | 4 | integrator |

### Persona Selection by Mode

| Mode | Minimum | Required Archetypes |
|------|---------|---------------------|
| causal | 2 | executor + validator |
| abductive | 3 | explorer + challenger + integrator |
| inductive | 2 | explorer + validator |
| analogical | 2 | explorer + challenger |
| dialectical | 3 | thesis + antithesis + integrator |
| counterfactual | 2 | executor + explorer |

## Conversation Format

```xml
<personas>
  <P1 traits="E:2,A:4,C:5,N:2,O:3" role="executor">[description]</P1>
  <P2 traits="E:3,A:2,C:5,N:4,O:3" role="challenger">[description]</P2>
</personas>

<think1>[Initial analysis]</think1>
<think2>Wait, [challenge]...</think2>
<think1>[Response or adjustment]</think1>
<think2>Actually, [refinement]...</think2>
<synthesis>[Integrated conclusion]</synthesis>
```

## Discourse Markers (Required)

Every trace MUST include ≥2:

| Marker | Function |
|--------|----------|
| "Wait..." | Triggers verification |
| "Actually..." | Signals correction |
| "Oh, but..." | Signals conflict |
| "Hmm..." | Invites exploration |
| "No, that's not right..." | Explicit disagreement |
| "Let me check..." | Triggers verification |

## Anti-Sycophancy Rule

Personas must NOT simply agree. Every trace requires:
- ≥1 explicit disagreement or challenge
- Challenge must be substantive
- Resolution must address the challenge

## Output Contract

```yaml
thinking_output:
  mode: causal | abductive | inductive | analogical | dialectical | counterfactual
  
  personas:
    - id: string
      traits: {E: int, A: int, C: int, N: int, O: int}
      role: string
      
  conversation:
    turns: int
    conflicts: int          # Must be ≥1
    discourse_markers: [string]
    
  conclusion:
    primary: string
    supporting: [string]
    dissent: optional<string>
    confidence: float
    bounds: [float, float]
    
  next:
    suggested_mode: optional<string>
    actions: [string]
```

## Quality Gates

| Gate | Requirement |
|------|-------------|
| Personas defined | ≥2 with distinct traits |
| Conflict present | ≥1 explicit disagreement |
| Discourse markers | ≥2 markers used |
| Synthesis addresses challenges | Not dismissed |
| Conscientiousness uniform | All personas C=5 |
| Trait diversity | E, A, N, O varied |

## References

- [references/causal.md](references/causal.md) — 6-stage execution flow
- [references/abductive.md](references/abductive.md) — Hypothesis competition
- [references/inductive.md](references/inductive.md) — Pattern extraction
- [references/analogical.md](references/analogical.md) — Knowledge transfer
- [references/dialectical.md](references/dialectical.md) — Position synthesis
- [references/counterfactual.md](references/counterfactual.md) — Alternative evaluation
- [references/personas.md](references/personas.md) — Persona design guide
