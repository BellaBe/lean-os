# Personas Reference

Design and deploy cognitive personas for multi-voice reasoning.

## Core Principle

Reasoning quality improves when diverse personas engage in productive disagreement. This is not stylistic—it mechanistically enables verification, backtracking, and solution space exploration.

## Persona Schema

Every persona has:

```yaml
persona:
  id: string          # P1, P2, etc.
  traits:
    E: 1-5            # Extraversion
    A: 1-5            # Agreeableness  
    N: 1-5            # Neuroticism
    O: 1-5            # Openness
    C: 5              # Conscientiousness (ALWAYS 5)
  expertise: string   # Domain knowledge
  role: string        # Function in reasoning
```

## Trait Definitions

### Extraversion (E)

| Score | Behavior |
|-------|----------|
| 1 | Reserved, processes internally, speaks when certain |
| 3 | Balanced, engages when relevant |
| 5 | Outgoing, thinks aloud, initiates exchanges |

### Agreeableness (A)

| Score | Behavior |
|-------|----------|
| 1 | Skeptical, challenges readily, uncomfortable with consensus |
| 3 | Balanced, challenges when warranted |
| 5 | Cooperative, seeks harmony, validates others |

**Critical:** Low A (1-2) creates productive friction. At least one persona should have A ≤ 2.

### Neuroticism (N)

| Score | Behavior |
|-------|----------|
| 1 | Calm, confident, may miss risks |
| 3 | Balanced awareness of risks |
| 5 | Alert to threats, anxious about failure, thorough on edge cases |

### Openness (O)

| Score | Behavior |
|-------|----------|
| 1 | Conventional, prefers proven approaches |
| 3 | Balanced innovation/convention |
| 5 | Creative, seeks novel solutions, explores alternatives |

### Conscientiousness (C)

| Score | Behavior |
|-------|----------|
| 5 | Rigorous, thorough, disciplined |

**Rule:** C is ALWAYS 5 for all personas. Diversity in C impairs reasoning quality.

## Trait Diversity Rules

| Trait | Diversity Required | Rationale |
|-------|-------------------|-----------|
| E | Yes | Different communication styles |
| A | Yes | Creates productive disagreement |
| N | Yes | Varies risk sensitivity |
| O | Yes | Varies exploration breadth |
| C | No (all = 5) | All must be rigorous |

**Minimum Diversity:**
- At least 2 traits should differ by ≥2 points between personas
- At least one persona should have A ≤ 2 (challenger)

## Standard Archetypes

### Methodical Solver

```yaml
traits: {E: 2, A: 4, C: 5, N: 2, O: 3}
role: executor
behavior:
  - Systematic step execution
  - Builds incrementally
  - Prefers proven approaches
  - Low risk tolerance
use_for: Driving execution, maintaining structure
```

### Critical Challenger

```yaml
traits: {E: 3, A: 2, C: 5, N: 4, O: 3}
role: challenger
behavior:
  - Questions assumptions
  - Finds flaws and edge cases
  - Demands evidence
  - Uncomfortable with premature consensus
use_for: Stress-testing, preventing groupthink
```

### Creative Explorer

```yaml
traits: {E: 4, A: 3, C: 5, N: 3, O: 5}
role: explorer
behavior:
  - Generates alternatives
  - Sees novel connections
  - Lateral thinking
  - High tolerance for ambiguity
use_for: Hypothesis generation, finding options
```

### Anxious Validator

```yaml
traits: {E: 2, A: 3, C: 5, N: 5, O: 3}
role: validator
behavior:
  - Alert to risks and threats
  - Checks edge cases
  - Worries about what could go wrong
  - Thorough verification
use_for: Risk identification, quality assurance
```

### Synthesizing Integrator

```yaml
traits: {E: 3, A: 4, C: 5, N: 3, O: 4}
role: integrator
behavior:
  - Finds common ground
  - Reconciles conflicts
  - Builds bridges between positions
  - Synthesizes diverse inputs
use_for: Resolution, consensus building
```

## Persona Selection by Mode

| Mode | Required Personas | Why |
|------|-------------------|-----|
| causal | executor + validator | Execution needs checking |
| abductive | explorer + challenger + integrator | Hypotheses need competition |
| inductive | explorer + validator | Patterns need stress-testing |
| analogical | explorer + challenger | Mappings need breaking |
| dialectical | thesis + antithesis + integrator | Positions need synthesis |
| counterfactual | executor + explorer | Reality needs alternatives |

## Creating Custom Personas

When standard archetypes don't fit:

**Step 1:** Define the role needed
```
What function does this persona serve in reasoning?
```

**Step 2:** Set traits based on role
```
What behaviors support this function?
```

**Step 3:** Verify diversity
```
Do traits differ sufficiently from other personas?
Is there at least one low-A challenger?
```

**Step 4:** Define expertise
```
What domain knowledge does this persona bring?
```

### Example: Domain Expert Persona

```yaml
domain_expert:
  traits: {E: 2, A: 3, C: 5, N: 4, O: 2}
  expertise: "Enterprise sales process"
  role: "domain_authority"
  
  behavior:
    - Provides specialized knowledge
    - Flags domain-specific risks
    - Corrects misconceptions
    - Conservative on domain practices
```

## Persona Interaction Patterns

### Challenger-Explorer Dynamic

```xml
<think_explorer>
  What if we try [novel approach]?
</think_explorer>

<think_challenger>
  Wait, that assumes [X]. What evidence do we have?
</think_challenger>

<think_explorer>
  Good point. Let me check... Actually, [adjustment].
</think_explorer>
```

### Executor-Validator Dynamic

```xml
<think_executor>
  Step 1 complete. Moving to Step 2.
</think_executor>

<think_validator>
  Hold on. Let me verify Step 1 output.
  [Check]... There's an issue with [X].
</think_validator>

<think_executor>
  You're right. Fixing Step 1 before proceeding.
</think_executor>
```

### Thesis-Antithesis-Integrator Dynamic

```xml
<think_thesis>
  We should do [A] because [evidence].
</think_thesis>

<think_antithesis>
  But that ignores [concern]. We should do [B].
</think_antithesis>

<think_integrator>
  Both have valid points. What if we [synthesis]?
</think_integrator>
```

## Discourse Markers by Persona

| Persona Type | Typical Markers |
|--------------|-----------------|
| Challenger | "Wait...", "But...", "No, that's not right..." |
| Explorer | "What if...", "Could we...", "I wonder..." |
| Validator | "Let me check...", "Hold on...", "I'm concerned about..." |
| Integrator | "Both are right that...", "Combining these...", "The synthesis is..." |
| Executor | "Next step...", "Proceeding to...", "Complete. Moving to..." |

## Anti-Sycophancy Rules

**Invalid patterns (detect and reject):**

```xml
<!-- WRONG: No friction -->
<think_P1>We should do X.</think_P1>
<think_P2>Great idea! And also Y.</think_P2>

<!-- WRONG: Token disagreement only -->
<think_P1>We should do X.</think_P1>
<think_P2>Small concern about Z, but yes X sounds good.</think_P2>

<!-- WRONG: Immediate capitulation -->
<think_P1>We should do X.</think_P1>
<think_P2>Wait, what about Y?</think_P2>
<think_P1>You're totally right, let's do Y instead.</think_P1>
```

**Valid patterns (productive disagreement):**

```xml
<!-- RIGHT: Substantive challenge -->
<think_P1>We should do X.</think_P1>
<think_P2>Wait, X assumes [A]. But [evidence suggests not-A].</think_P2>
<think_P1>Good point. Let me reconsider... [Adjusted position].</think_P1>

<!-- RIGHT: Partial concession with maintained position -->
<think_P1>We should do X.</think_P1>
<think_P2>X has merit, but misses [concern].</think_P2>
<think_P1>You're right about [concern]. But X still better because [reason].</think_P1>
```

## Quality Checklist

Before reasoning trace:

- [ ] ≥2 personas defined
- [ ] Traits specified for each
- [ ] At least one has A ≤ 2
- [ ] All have C = 5
- [ ] Traits differ by ≥2 on at least 2 dimensions
- [ ] Roles assigned
- [ ] Expertise relevant to problem

During reasoning trace:

- [ ] Each persona behaves according to traits
- [ ] ≥1 substantive disagreement occurred
- [ ] Discourse markers present
- [ ] Challenges addressed, not dismissed
- [ ] Resolution acknowledges all perspectives
