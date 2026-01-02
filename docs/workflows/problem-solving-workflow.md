# Problem-Solving Gateway
**Workflow Specification (Authoritative)**

**Status:** Active
**Applies to:** Human operators and AI agents
**Agent:** `.claude/agents/problem-solving-gateway.md`

---

## Purpose

The **problem-solving-gateway** is the universal orchestration layer that converts ambiguous requests into **concrete, executable deliverables**.

It answers one question:

> **What should be produced, and how should it be produced?**

It does this by coordinating **action skills** and **reasoning modes** in a deterministic way.

---

## Position in the System

```
User / System Signal
└── problem-solving-gateway ← DEFAULT ENTRY POINT
    ├── (optional) reasoning-gateway
    └── action skills (deliverables)
        └── operational threads (causal execution)
```

### Key distinctions
- **Problem-solving-gateway** → produces deliverables
- **Reasoning-gateway** → produces reasoning-only analysis
- **Causal threads** → execute decisions operationally

---

## Relationship to Causal Execution

All execution in the system is **causal-first**.

The gateway **does not replace** causal execution.
It prepares, structures, and routes work *into* causal threads.

```
problem-solving-gateway
└── decision / plan / procedure
    └── reasoning-causal thread
        └── 6-stage causal flow
```

The **6-Stage Causal Flow** remains the execution backbone:

1. Input
2. Hypothesis
3. Implication
4. Decision
5. Actions
6. Learning

---

## Core Workflow (3-Step Loop)

### Step 1: Action Selection (Deliverable Intent)

Determine **what kind of output** the user expects.

Action skills are **output contracts**, not tools.

| Action Skill | Question Answered |
|-------------|------------------|
| action-descriptive | What is happening? |
| action-diagnostic | Why did this happen? |
| action-decision | Which option do we choose? |
| action-prescriptive | What should we do? |
| action-planning | How do we execute this? |

**Composite requests are decomposed** into ordered action chains.

Example:
```
"Why did churn spike and what should we do?"
→ action-diagnostic → action-prescriptive
```

---

### Step 2: Reasoning Selection (Thinking Lens)

Determine **how to think** in order to produce the action output.

This step may delegate to **reasoning-gateway**.

Reasoning modes are **internal lenses**, not deliverables.

| Reasoning Mode | When Used |
|---------------|-----------|
| causal | Known processes, execution flows |
| abductive | Explaining a single observation |
| inductive | Pattern extraction from repetition |
| analogical | Applying prior analogs |
| dialectical | Synthesizing competing positions |
| counterfactual | Evaluating alternatives |

**System default:** operational contexts are **causal-first**.

Reasoning mode names are **not exposed** unless explicitly requested.

---

### Step 3: Output Emission (Action Contract)

Produce a concrete deliverable that conforms **exactly** to the selected action skill format.

Rules:
- Action sections must remain ordered
- No interleaving between action types
- No reasoning traces unless requested

#### Optional (high-stakes cases)
A single reasoning summary block may be prepended:

```
conclusion:
confidence:
evidence:
open_questions:
```

This block summarizes reasoning; it does not replace action outputs.

---

## What the Gateway Does NOT Do

- Does not execute tasks
- Does not store state or memory
- Does not replace causal threads
- Does not expose reasoning by default

---

## Entry Point Rules

| User Intent | Entry Point |
|-------------|-------------|
| Explanation, analysis, recommendation, plan | problem-solving-gateway |
| "What should we do?" | problem-solving-gateway |
| Explicit reasoning mode requested | reasoning-gateway |
| Reasoning-only analysis | reasoning-gateway |
| Operational execution | causal threads |

---

## Failure Modes & Debugging

If outputs are incorrect or unexpected:

1. Check action misclassification
2. Check reasoning mode override
3. Verify composite action order

Most errors originate in Step 1 (wrong action selection).

---

## Invariants (Architecture Laws)

1. All execution is causal.
2. All deliverables are actions.
3. All reasoning is internal unless requested.
4. Users never choose skills or modes.

---

## References

- **Problem-Solving Gateway:** `.claude/agents/problem-solving-gateway.md`
- **Reasoning Gateway:** `.claude/agents/reasoning-gateway.md`
- **Action Skills:** `.claude/skills/action-*/`
- **Causal Reasoning:** `.claude/skills/reasoning-causal/`

---

## LeanOS Pro

Need more action skills? **LeanOS Pro** includes 11 action skills:
- action-evaluative (Is this good enough?)
- action-procedural (How do we execute this every time?)
- action-validation (How do we know it worked?)
- action-risk (What could go wrong?)
- action-constraint (What must not change?)
- action-alignment (Why are we misaligned?)

Plus domain-specific agents for sales, marketing, product, and engineering.

[Learn more about LeanOS Pro](https://bellabe.gumroad.com/l/leanos-pro)
