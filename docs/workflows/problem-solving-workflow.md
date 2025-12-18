# Problem-Solving Gateway  
**Workflow Specification (Authoritative)**

**Status:** Active  
**Version:** 1.0  
**Applies to:** Human operators and AI agents  
**Agent:** `.claude/agents/problem-solving-gateway.md`

---

## Purpose

The **problem-solving-gateway** is the universal orchestration layer that converts ambiguous requests into **concrete, executable deliverables**.

It answers one question:

> **What should be produced, and how should it be produced?**

It does this by coordinating **action skills**, **reasoning modes**, and **domain execution flows** in a deterministic way.

---

## Position in the System

```
User / System Signal
└── problem-solving-gateway ← DEFAULT ENTRY POINT
    ├── (optional) reasoning-gateway
    ├── action skills (deliverables)
    └── domain agents
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
    └── domain agent
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
| descriptive-action | What is happening? |
| diagnostic-action | Why did this happen? |
| evaluative-action | Is this good enough? |
| decision-action | Which option do we choose? |
| prescriptive-actions | What should we do? |
| planning-action | How do we execute this once? |
| procedural-action | How do we execute this every time? |
| validation-action | How do we know it worked? |
| risk-action | What could go wrong? |
| constraint-action | What must not change? |
| alignment-action | Why are we misaligned? |

**Composite requests are decomposed** into ordered action chains.

Example:
```
"Why did churn spike and what should we do?"
→ diagnostic-action → prescriptive-actions
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

## Domain Delegation

When domain intent is clear, delegate early.

| Domain | Delegated Agent |
|--------|-----------------|
| Sales | sales-execution |
| Marketing | marketing-execution |
| Foundations | foundations-builder |
| Engineering | lean-os |

Domain agents:
- Enforce domain rules
- Spawn causal threads
- Own execution sequencing

The gateway does not duplicate domain enforcement.

---

## What the Gateway Does NOT Do

- Does not execute tasks
- Does not store state or memory
- Does not replace causal threads
- Does not expose reasoning by default
- Does not bypass domain agents

---

## Entry Point Rules

| User Intent | Entry Point |
|-------------|-------------|
| Explanation, analysis, recommendation, plan | problem-solving-gateway |
| "What should we do?" | problem-solving-gateway |
| Runbook / SOP / validation | problem-solving-gateway |
| Explicit reasoning mode requested | reasoning-gateway |
| Reasoning-only analysis | reasoning-gateway |
| Operational execution | causal threads (via domain agents) |

---

## Failure Modes & Debugging

If outputs are incorrect or unexpected:

1. Check action misclassification
2. Check reasoning mode override
3. Check domain misrouting
4. Verify composite action order

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
- **Action Skills:** `.claude/skills/*-action/`
- **Causal Reasoning:** `.claude/skills/reasoning-causal/`

---

## Final Note

This document is both:

1. A human-readable mental model, and
2. An AI-operational specification.

It is safe to use as a live workflow contract.