# Reasoning Workflow

How to use the reasoning agent and skills for structured thinking, problem solving, creative ideation, and learning.

---

## Overview

The reasoning system provides structured cognitive capabilities through 4 composable skills coordinated by 1 agent.

```
+---------------------------------------------------------------+
|                         REASONING                              |
+---------------------------------------------------------------+
|  AGENT                                                         |
|  +---------------------+                                       |
|  | rsn-problem-solver  |  Coordinates perceive --> think loop  |
|  +---------------------+                                       |
+---------------------------------------------------------------+
|  SKILLS                                                        |
|  +------------------+  +------------------+                    |
|  | rsn-perceiving-  |  | rsn-reasoning-   |                    |
|  | information      |  | problems         |                    |
|  | 6 modes          |  | 6 modes          |                    |
|  +------------------+  +------------------+                    |
|  +------------------+  +------------------+                    |
|  | rsn-learning-    |  | rsn-creating-    |                    |
|  | outcomes         |  | ideas            |                    |
|  | 5 modes          |  | 10+ techniques   |                    |
|  +------------------+  +------------------+                    |
+---------------------------------------------------------------+
```

### Cognitive Cycle

```
ENVIRONMENT
    |
    v
rsn-perceiving-information  (What's happening?)
    |
    v
rsn-reasoning-problems      (What does it mean?)
    |
    +-----------+-----------+
    |                       |
    v                       v
rsn-creating-ideas      ACTION
(What could we do?)     (Execute)
                            |
                            v
                    rsn-learning-outcomes
                    (What did we learn?)
```

---

## Skill Selection

### Decision Tree

```
What is the primary task?

+-- GATHER INFORMATION
|   +-- Don't know what to look for? --> perceiving.scanning
|   +-- Need deep understanding? --> perceiving.focusing
|   +-- Too much information? --> perceiving.filtering
|   +-- Need to verify a claim? --> perceiving.triangulating
|   +-- Need ongoing awareness? --> perceiving.monitoring
|   +-- Multiple signals to combine? --> perceiving.synthesizing
|
+-- REASON THROUGH SOMETHING
|   +-- Have goal to achieve? --> reasoning.causal
|   +-- Need to explain observation? --> reasoning.abductive
|   +-- Have instances, need rule? --> reasoning.inductive
|   +-- Novel situation, recall similar? --> reasoning.analogical
|   +-- Conflicting options/tensions? --> reasoning.dialectical
|   +-- Evaluating "what if"? --> reasoning.counterfactual
|
+-- GENERATE IDEAS
|   +-- Need breakthrough? --> creating-ideas (First Principles)
|   +-- Rapid ideation? --> creating-ideas (SCAMPER)
|   +-- Stuck in pattern? --> creating-ideas (Lateral Thinking)
|   +-- Evaluate idea quality? --> creating-ideas (AUDIT mode)
|
+-- LEARN FROM EXPERIENCE
|   +-- Action failed, need quick fix? --> learning.single-loop
|   +-- Pattern of failures? --> learning.double-loop
|   +-- Experience complete? --> learning.reflection
|   +-- Belief needs testing? --> learning.experimentation
|   +-- Predictions miscalibrated? --> learning.calibration
|
+-- SOLVE A PROBLEM (multi-step)
    +--> rsn-problem-solver agent (coordinates perceive --> think loop)
```

### Trigger Phrases

| If you hear... | Use this |
|----------------|----------|
| "What's out there?" | perceiving.scanning |
| "Tell me more about X" | perceiving.focusing |
| "Too much noise" | perceiving.filtering |
| "Is this true?" | perceiving.triangulating |
| "How do we do X?" | reasoning.causal |
| "Why did X happen?" | reasoning.abductive |
| "I keep seeing X" | reasoning.inductive |
| "This is like..." | reasoning.analogical |
| "On one hand... on the other..." | reasoning.dialectical |
| "What if we had done X?" | reasoning.counterfactual |
| "Brainstorm options" | creating-ideas |
| "What did we learn?" | learning.reflection |
| "Why does this keep happening?" | learning.double-loop |
| "Figure out why..." | rsn-problem-solver |

---

## Composition Patterns

Skills compose into pipelines. The output of one skill becomes input to the next.

### Perceive then Think

Most common pattern for analysis tasks.

```
perceiving.X --> reasoning.Y --> output
```

**Example:** scanning --> focusing --> triangulating --> synthesizing --> dialectical --> decision

### Think then Act then Learn

For tasks where inputs are already known.

```
reasoning.X --> action --> learning.Y
```

**Example:** abductive --> fix --> single-loop

### Create then Think

For tasks needing novel solutions.

```
creating-ideas --> reasoning.dialectical --> reasoning.causal
```

**Example:** ideate --> evaluate trade-offs --> plan execution

### Full Cycle

For complete operational workflows.

```
perceiving --> reasoning --> acting --> learning --> (back to perceiving)
```

---

## Workflow Patterns

### Research to Decision

```
perceiving.scanning --> perceiving.focusing --> perceiving.triangulating
    --> perceiving.synthesizing --> reasoning.dialectical --> decision
```

**Use when:** Strategic question requires investigation before deciding.

### Incident Response

```
perceiving.monitoring (trigger) --> reasoning.abductive (diagnose)
    --> learning.single-loop (fix) --> [if pattern] learning.double-loop
```

**Use when:** Something is broken and needs fixing.

### Hypothesis Validation

```
reasoning.abductive (hypothesis) --> validation criteria
    --> learning.experimentation --> learning.calibration --> decision
```

**Use when:** Belief needs validation before commitment.

### Retrospective

```
gather data --> learning.reflection --> learning.single-loop
    --> [if pattern] learning.double-loop --> recommendations
```

**Use when:** Learning from completed project or incident.

---

## Thread Integration

Reasoning skills map to the causal flow thread structure:

| Thread Stage | Reasoning Skill |
|--------------|-----------------|
| 1-input.md | rsn-perceiving-information (gather context) |
| 2-hypothesis.md | rsn-reasoning-problems (form hypothesis) |
| 3-implication.md | rsn-reasoning-problems.causal (derive implications) |
| 4-decision.md | rsn-reasoning-problems.dialectical (evaluate options) |
| 5-actions.md | Execution (not reasoning) |
| 6-learning.md | rsn-learning-outcomes.reflection (capture learnings) |

---

## Reference Card

### rsn-perceiving-information Modes

| Mode | Use When | Key Output |
|------|----------|------------|
| scanning | Need landscape awareness | Signals + focus candidates |
| focusing | Need deep understanding | Findings + implications |
| filtering | Information overload | Prioritized items |
| triangulating | Need to verify claims | Confidence-rated claims |
| monitoring | Need ongoing awareness | Alerts when threshold crossed |
| synthesizing | Need to integrate signals | Coherent picture |

### rsn-reasoning-problems Modes

| Mode | Use When | Key Output |
|------|----------|------------|
| causal | Executing, planning, procedures | Path from current to goal |
| abductive | Diagnosing, risk identification | Ranked hypotheses |
| inductive | Extracting patterns, summarizing | Pattern with confidence |
| analogical | Applying knowledge from similar domain | Transferred insight |
| dialectical | Resolving conflicts, deciding, evaluating | Synthesis or choice |
| counterfactual | Evaluating alternatives | Comparison of paths |

### rsn-learning-outcomes Modes

| Mode | Use When | Key Output |
|------|----------|------------|
| single-loop | Fixing immediate problem | Correction + verification |
| double-loop | Questioning the frame | Reframed assumptions |
| reflection | Extracting from experience | Insights + artifacts |
| experimentation | Testing hypothesis | Validated/invalidated + confidence |
| calibration | Adjusting predictions | Calibration rules |

### rsn-creating-ideas Techniques

| Technique | Use When | Key Output |
|-----------|----------|------------|
| First Principles | Need breakthrough | Rebuilt from fundamentals |
| SCAMPER | Rapid ideation | Systematic variations |
| Lateral Thinking | Stuck in pattern | Unexpected connections |
| Analogical Transfer | Need cross-domain insight | Borrowed solutions |
