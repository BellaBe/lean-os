---
name: product-design-flows
description: Transform requirements into user journeys and flow diagrams. Use when designing user workflows, mapping customer journeys, or planning interaction sequences.
---

# Product Design Flows

Transform product requirements and user stories into visual user journeys and interaction flows.

## Overview

This skill converts user stories into detailed flow diagrams showing how users move through the product. Based on User Story Mapping's journey approach and Shape Up's breadboarding technique.

**Primary Use Cases**: User journey mapping, flow design, interaction sequencing, happy path definition.

**Reads From**: User stories, Canvas segments (04-segments), problem context (05-problem)

## Core Functions

### 1. Create User Journey Map

Map the complete user experience from awareness to success.

**Journey Stages:**
```
┌─────────┬──────────┬──────────┬─────────┬─────────┐
│ AWARE   │ CONSIDER │ ACQUIRE  │ USE     │ SUCCEED │
├─────────┼──────────┼──────────┼─────────┼─────────┤
│ How do  │ How do   │ How do   │ How do  │ How do  │
│ they    │ they     │ they     │ they    │ they    │
│ find us?│ evaluate?│ start?   │ engage? │ achieve?│
└─────────┴──────────┴──────────┴─────────┴─────────┘
```

**Journey Map Template:**
```
# User Journey: {Persona} Achieving {Goal}

## Persona
Name: [From 04-segments]
Goal: [Primary outcome they want]
Context: [When/where they engage]

## Journey Stages

### 1. AWARE
- **Trigger:** What prompts them to look for a solution?
- **Touchpoints:** Where do they first encounter us?
- **Emotions:** What are they feeling?
- **Actions:** What do they do?
- **Pain Points:** What friction exists?

### 2. CONSIDER
- **Questions:** What do they need to know?
- **Touchpoints:** How do they evaluate?
- **Emotions:** Hopeful? Skeptical?
- **Actions:** Compare, research, ask
- **Pain Points:** What causes doubt?

### 3. ACQUIRE
- **Entry Point:** How do they start?
- **Touchpoints:** Signup, onboarding
- **Emotions:** Excited? Overwhelmed?
- **Actions:** Register, configure, first use
- **Pain Points:** Where do they get stuck?

### 4. USE
- **Core Tasks:** What do they do regularly?
- **Touchpoints:** Main features
- **Emotions:** Productive? Frustrated?
- **Actions:** [Key workflows]
- **Pain Points:** Daily friction

### 5. SUCCEED
- **Outcome:** How do they know it worked?
- **Touchpoints:** Results, reports, feedback
- **Emotions:** Satisfied? Delighted?
- **Actions:** Share, expand, recommend
- **Pain Points:** What could be better?

## Opportunity Map
| Stage | Pain Point | Opportunity | Priority |
|-------|------------|-------------|----------|
| [Stage] | [Friction] | [How to fix] | [H/M/L] |
```

### 2. Build Flow Diagrams (Breadboards)

Create abstract flow diagrams without visual design.

**Breadboard Components:**
```
┌─────────────┐     ┌─────────────┐
│   PLACE     │────>│   PLACE     │
│ (screen/    │     │ (next       │
│  state)     │     │  screen)    │
└─────────────┘     └─────────────┘
       │
       │ [Affordance - what user can do]
       │
       ▼
┌─────────────┐
│   PLACE     │
│ (alternate  │
│  path)      │
└─────────────┘
```

**Breadboard Template:**
```
# Flow: {Task Name}

## Entry Point
User arrives from: [Previous state/screen]
With context: [What they know/have done]

## Flow Diagram

[Start]
    │
    ▼
┌─────────────────┐
│ {Screen Name}   │
│                 │
│ Shows:          │
│ - [Element]     │
│ - [Element]     │
│                 │
│ Actions:        │
│ → [Action 1]    │
│ → [Action 2]    │
└────────┬────────┘
         │
    ┌────┴────┐
    │         │
[Action 1] [Action 2]
    │         │
    ▼         ▼
┌────────┐ ┌────────┐
│Screen 2│ │Screen 3│
└────────┘ └────────┘

## States
- Default: [What user sees initially]
- Loading: [Feedback during processing]
- Success: [Confirmation of completion]
- Error: [What happens when things fail]
- Empty: [When there's no data]

## Edge Cases
- If [condition]: [What happens]
- If [condition]: [What happens]
```

### 3. Define Happy Path

The ideal flow through a feature with no errors or edge cases.

**Happy Path Template:**
```
# Happy Path: {Feature/Task}

## Goal
User wants to: [Outcome]

## Preconditions
- User has: [Required state]
- User knows: [Required context]

## Steps

1. **[Action]**
   - User does: [Specific action]
   - System responds: [Feedback]
   - User sees: [Result]

2. **[Action]**
   - User does: [Specific action]
   - System responds: [Feedback]
   - User sees: [Result]

3. **[Action]**
   - User does: [Specific action]
   - System responds: [Feedback]
   - User sees: [Result]

## Success State
- User has achieved: [Outcome]
- System has: [State change]
- Next actions available: [What they can do next]

## Time to Complete
Expected: [X] minutes/seconds
```

### 4. Map Error Flows

Document what happens when things go wrong.

**Error Flow Template:**
```
# Error Flows: {Feature}

## Error Categories

### Validation Errors
| Error | Cause | Message | Recovery |
|-------|-------|---------|----------|
| [Error type] | [What triggers] | [User sees] | [How to fix] |

### System Errors
| Error | Cause | Message | Recovery |
|-------|-------|---------|----------|
| [Error type] | [What triggers] | [User sees] | [How to fix] |

### User Errors
| Error | Cause | Message | Recovery |
|-------|-------|---------|----------|
| [Error type] | [What triggers] | [User sees] | [How to fix] |

## Error Flow Diagram

[Happy Path Step 2]
         │
         │ [Error condition]
         ▼
┌─────────────────┐
│ Error State     │
│                 │
│ Shows:          │
│ - Error message │
│ - Recovery hint │
│                 │
│ Actions:        │
│ → Retry         │
│ → Go back       │
│ → Get help      │
└─────────────────┘
```

### 5. Create State Diagrams

Map all possible states for a feature or entity.

**State Diagram Template:**
```
# State Diagram: {Entity/Feature}

## States

┌─────────┐  [trigger]   ┌──────────┐
│ State A │─────────────>│ State B  │
└─────────┘              └──────────┘
     ^                        │
     │                   [trigger]
     │                        │
     │                        ▼
     │                  ┌──────────┐
     └──────────────────│ State C  │
          [trigger]     └──────────┘

## State Definitions

### State A: {Name}
- Description: [What this state means]
- Entry conditions: [How user gets here]
- Available actions: [What user can do]
- Exit conditions: [How user leaves]

### State B: {Name}
- Description: [What this state means]
- Entry conditions: [How user gets here]
- Available actions: [What user can do]
- Exit conditions: [How user leaves]

## Transitions
| From | To | Trigger | Side Effects |
|------|----|---------|--------------|
| State A | State B | [User action] | [What happens] |
```

### 6. Walking Skeleton Flow

Map the minimum end-to-end flow (from User Story Mapping).

**Walking Skeleton Template:**
```
# Walking Skeleton: {Feature/Product}

## Definition
The thinnest possible slice that exercises the full system.

## End-to-End Flow

[Entry] → [Core Action] → [Confirmation] → [Value Delivered]

## Minimal Steps

1. **Entry Point**
   - Screen: [Minimal UI]
   - User action: [Single action]
   - System: [Minimal response]

2. **Core Action**
   - Screen: [Minimal UI]
   - User action: [Primary task]
   - System: [Core processing]

3. **Confirmation**
   - Screen: [Success state]
   - User sees: [Result]
   - System: [State saved]

## What's Deferred
- [Enhancement for later]
- [Edge case handling]
- [Additional feature]

## Why This Slice
- Validates: [Core assumption]
- Exercises: [Key technical path]
- Delivers: [Minimum user value]
```

## Workflows

### Stories → Journey Map

```
1. Read user stories from product-requirements
2. Identify primary persona (04-segments)
3. Map stories to journey stages
4. Identify touchpoints and emotions
5. Find pain points and opportunities
6. Output: Complete journey map
```

### Stories → Flow Diagrams

```
1. Group stories by feature/task
2. Identify entry points and goals
3. Create breadboard for each task
4. Define happy path first
5. Add error flows and edge cases
6. Define all states
7. Output: Flow diagrams with states
```

## Input Requirements

**Required:**
- User stories (from product-requirements)
- Target persona (from 04-segments)

**Optional:**
- Existing flows to extend
- Technical constraints
- User research/feedback

## Output Structure

```
Design Flows Output:
├── journey_map.md           # Full user journey
├── flows/                   # Individual flow diagrams
│   ├── flow-{task-1}.md
│   ├── flow-{task-2}.md
│   └── ...
├── states/                  # State diagrams
│   ├── state-{entity}.md
│   └── ...
└── walking_skeleton.md      # Minimum viable flow
```

## Integration

**Receives from:**
- product-requirements - user stories to map
- Canvas 04-segments - persona context
- Canvas 05-problem - problem context

**Provides to:**
- product-design-wireframes - flows to visualize
- product-specification - flows for shaped pitches
- Engineering - interaction specifications

## Best Practices

### Journey Mapping
1. **User-centric**: Map user goals, not features
2. **Emotional**: Include how users feel
3. **Complete**: Don't skip painful stages
4. **Actionable**: Every pain point = opportunity

### Flow Design
1. **Happy path first**: Know the ideal before edge cases
2. **States matter**: Every element has multiple states
3. **Error recovery**: Always show a way forward
4. **Abstract first**: Breadboard before wireframe

### Avoiding Pitfalls
- Do NOT skip error flows
- Do NOT forget empty/loading states
- Do NOT design screens, design interactions
- Do NOT assume linear paths (users jump around)

## Key Principles

> "Design the whole flow first, then slice horizontally." — User Story Mapping

> "We need to know where things are and what they're called before we can determine how they look." — Shape Up (Breadboarding)

> "The journey map is the artifact of understanding, not the understanding itself."

---

**Related Playbooks:**
- [user-story-mapping](research/playbooks/user-story-mapping.md)
- [product-shaping](research/playbooks/product-shaping.md)
