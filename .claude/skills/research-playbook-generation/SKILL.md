---
name: research-playbook-generation
description: Generate actionable playbooks from extracted insights. Use when transforming source insights into step-by-step operational guides.
---

# Research Playbook Generation

Transform extracted insights into actionable, operational playbooks.

## Type Signature

```
PlaybookGeneration : [Insights] × Domain × Audience → Playbook

Where:
  Insights   : research/sources/{source}/insights.md (one or more)
  Domain     : Topic area (e.g., "network effects", "pricing")
  Audience   : founder | operator | executive | technical
  Playbook   : Principles × Framework × Steps × Checklist × Warnings
```

## When to Use

- After source processing, to create operational guide
- When multiple sources on same topic need consolidation
- Client deliverable requiring actionable framework
- Building reusable knowledge assets

## Input Requirements

| Field | Required | Description |
|-------|----------|-------------|
| insights_sources | Yes | Path(s) to insights.md file(s) |
| domain | Yes | Playbook topic domain |
| audience | No | Target reader (default: founder) |
| focus | No | Specific aspect to emphasize |

## Process

### Stage 1: Insight Aggregation

From source insights.md file(s):

```yaml
aggregation:
  sources: [{source_name, insight_count}]
  total_insights: N
  frameworks_found: [list]
  principles_found: [list]
  tactics_found: [list]
  warnings_found: [list]
```

### Stage 2: Framework Selection

Choose primary framework for playbook structure:

```yaml
framework_selection:
  primary_framework: "{name}"
  rationale: "Why this framework organizes the playbook"
  secondary_frameworks: [integrated as subsections]
  excluded: [{framework, reason}]
```

**Selection criteria:**
1. Most comprehensive (covers most insights)
2. Most actionable (leads to clear steps)
3. Most memorable (easy to recall/apply)

### Stage 3: Principle Extraction

Extract 3-7 core principles:

```yaml
principles:
  - id: P1
    name: "Short memorable name"
    statement: "One sentence principle"
    evidence: "From {source}: {quote}"
    application: "How to apply this"
    common_mistake: "What people get wrong"
```

**Principle quality:**
- Specific enough to guide action
- General enough to apply broadly
- Memorable (can recall without notes)
- Evidence-backed (not opinion)

### Stage 4: Step Sequencing

Convert tactics into ordered steps:

```yaml
steps:
  phase_1:
    name: "Phase name"
    goal: "What this phase achieves"
    steps:
      - step: 1
        action: "Specific action"
        why: "Why this matters"
        how: "How to do it"
        output: "What you produce"
        signals: "How you know it's working"

  phase_2:
    name: "Phase name"
    ...
```

**Sequencing logic:**
1. Dependencies (what must come first)
2. Risk reduction (validate before investing)
3. Value delivery (show progress early)
4. Natural progression (one thing leads to next)

### Stage 5: Warning Integration

Place warnings at decision points:

```yaml
warnings:
  - at_step: 3
    warning: "Common mistake at this stage"
    consequence: "What happens if ignored"
    prevention: "How to avoid"

  - general:
    warning: "Overall anti-pattern"
    applies_when: "Context"
```

### Stage 6: Checklist Creation

Synthesize into actionable checklist:

```yaml
checklist:
  pre_start:
    - "[ ] Prerequisite 1"
    - "[ ] Prerequisite 2"

  phase_1:
    - "[ ] Step 1 complete"
    - "[ ] Output 1 produced"

  quality_gates:
    - "[ ] Gate 1 passed before phase 2"
```

## Output Structure

Create file in `research/playbooks/{domain}.md`:

```markdown
# {Domain} Playbook

**Sources:** {List of source authors}
**Last Updated:** {YYYY-MM-DD}
**Audience:** {founder | operator | executive}

---

## Overview

{2-3 paragraphs explaining what this playbook covers and why it matters}

---

## Core Principles

### P1: {Principle Name}

**Principle:** {One sentence statement}

**Why:** {Why this matters}

**Evidence:**
> "{Quote from source}" — {Author}

**Application:** {How to apply}

**Common Mistake:** {What people get wrong}

---

### P2: {Principle Name}
...

---

## The Framework

### {Framework Name}

{Visual representation if applicable}

```
[Stage 1] → [Stage 2] → [Stage 3] → [Outcome]
```

**Stage 1: {Name}**
- Goal: {What this achieves}
- Activities: {What you do}
- Output: {What you produce}

**Stage 2: {Name}**
...

---

## Step-by-Step Execution

### Phase 1: {Phase Name}

**Goal:** {What this phase achieves}

**Duration:** {Typical timeframe}

#### Step 1: {Action Name}

**What:** {Specific action to take}

**Why:** {Why this matters}

**How:**
1. {Substep 1}
2. {Substep 2}
3. {Substep 3}

**Output:** {What you produce}

**Signals:** {How you know it's working}

> **Warning:** {Common mistake at this step}
>
> {What happens if ignored. How to prevent.}

#### Step 2: {Action Name}
...

---

### Phase 2: {Phase Name}
...

---

## Warnings & Anti-Patterns

### W1: {Warning Name}

**The Mistake:** {What people do wrong}

**Why It Happens:** {Root cause}

**Consequence:** {What goes wrong}

**Instead:** {What to do}

**Signs You're Making This Mistake:**
- {Signal 1}
- {Signal 2}

---

## Metrics & Benchmarks

| Metric | Target | Warning | Source |
|--------|--------|---------|--------|
| {metric} | {good} | {bad} | {author} |

---

## Checklists

### Pre-Start Checklist

```
[ ] {Prerequisite 1}
[ ] {Prerequisite 2}
[ ] {Prerequisite 3}
```

### Phase 1 Checklist

```
[ ] Step 1 complete: {output}
[ ] Step 2 complete: {output}
[ ] Quality gate: {criteria}
```

### Phase 2 Checklist
...

### Completion Checklist

```
[ ] All phases complete
[ ] Metrics in target range
[ ] No warning signs present
```

---

## Quick Reference

### The 3 Most Important Things

1. **{Thing 1}** — {Why}
2. **{Thing 2}** — {Why}
3. **{Thing 3}** — {Why}

### Decision Framework

```
IF {condition}
  → {action A}
ELSE IF {condition}
  → {action B}
ELSE
  → {action C}
```

---

## Sources

| Author | Source | Key Contribution |
|--------|--------|------------------|
| {name} | {source} | {what they contributed} |

---

## Related Playbooks

- [{Related playbook 1}](link)
- [{Related playbook 2}](link)

---

## Tags

`{tag1}` `{tag2}` `{tag3}`
```

## Quality Checklist

```
[ ] 3-7 core principles defined
[ ] Primary framework selected and explained
[ ] Steps are sequenced logically
[ ] Each step has what/why/how/output
[ ] Warnings placed at decision points
[ ] Metrics include targets and warning levels
[ ] Checklists are actionable
[ ] Sources properly attributed
[ ] Tags added for discoverability
```

## Integration

### From research-source-processing
- Receives insights.md as input
- Frameworks become playbook structure
- Tactics become playbook steps
- Warnings become anti-pattern section

### To reasoning-inductive (via knowledge-builder)
- Playbooks feed into cross-domain synthesis
- Patterns connect across playbooks
- Contradictions surface for resolution

### With Index
- Update `research/playbooks/index.md`
- Add to domain sections
- Cross-link related playbooks

## Example

**Input:**
```yaml
insights_sources:
  - research/sources/andrew-chen-network-effects/insights.md
domain: "network-effects"
audience: "founder"
```

**Output:**
```
research/playbooks/network-effects.md
├── Principles (5): Cold start, Density, Hard side, Atomic network, Engagement loop
├── Framework: The Cold Start Theory
├── Phases: Atomic → Tipping → Escape → Ceiling
├── Steps: 12 detailed steps with outputs
├── Warnings: 6 anti-patterns
├── Metrics: Network density targets, activation rates
└── Checklists: Pre-start, per-phase, completion
```

## Constraints

- **Actionable over theoretical** - Every section leads to action
- **Specific over vague** - Numbers, examples, concrete steps
- **Sequenced over random** - Clear order of operations
- **Attributed** - Credit sources for insights
- **Audience-appropriate** - Match complexity to reader
