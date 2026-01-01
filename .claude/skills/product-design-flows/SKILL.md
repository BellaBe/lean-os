---
name: product-design-flows
description: Transform stories into user journeys and flow diagrams. Use when mapping user workflows, creating breadboards, planning interaction sequences, or defining happy/error paths.
allowed-tools: Read, Grep, Glob
---

# Product Design Flows

Transform user stories into visual user journeys and interaction flows.

## Purpose

Convert stories into flow diagrams showing how users move through the product.

## When to Apply

- Mapping user journeys from awareness to success
- Creating breadboard diagrams for features
- Defining happy paths and error flows
- Building state diagrams for complex entities

## Boundaries

### This Skill Produces
- `journey-map.md` — Full user journey (stages, touchpoints, emotions)
- `{flow-name}.md` — Breadboard diagrams per feature/task

### This Skill Does NOT Produce
- Wireframes or mockups → Use `product-design-wireframes`
- User stories → Use `product-requirements`
- Engineering handoffs → Use `product-handoff`

### Handoff Points
- Receives from: product-requirements (stories)
- Provides to: product-design-wireframes, product-handoff

## Process

### Step 1: Create Journey Map

Map complete user experience.

**Output: journey-map.md**
```markdown
# User Journey: {Persona} → {Goal}

## Stages
| Stage | Trigger | Actions | Emotions | Pain Points |
|-------|---------|---------|----------|-------------|
| Aware | [Entry] | [Does] | [Feels] | [Friction] |
| Consider | [Trigger] | [Does] | [Feels] | [Friction] |
| Acquire | [Trigger] | [Does] | [Feels] | [Friction] |
| Use | [Trigger] | [Does] | [Feels] | [Friction] |
| Succeed | [Trigger] | [Does] | [Feels] | [Friction] |

## Opportunities
| Stage | Pain Point | Opportunity |
|-------|------------|-------------|
```

### Step 2: Build Breadboards

Abstract flow diagrams without visual design.

**Components:**
- **Places**: Screens/states (rectangles)
- **Affordances**: What user can do (labels)
- **Connections**: Flow between places (arrows)

**Output: {flow-name}.md**
```markdown
# Flow: {Task Name}

## Entry
- From: [Previous state]
- Context: [What user knows]

## Diagram
┌─────────┐     ┌─────────┐
│ Place A │────→│ Place B │
└─────────┘     └─────────┘
      │
      │ [affordance]
      ▼
┌─────────┐
│ Place C │
└─────────┘

## Places
1. **Place A**: [Purpose]
2. **Place B**: [Purpose]

## Happy Path
1. User does [X] → sees [Y]
2. User does [X] → sees [Y]
3. Success: [Outcome]

## Error Flows
| Error | Cause | Recovery |
|-------|-------|----------|
| [Type] | [Trigger] | [Path back] |

## States
| State | Entry | Exit |
|-------|-------|------|
| [Name] | [How user gets here] | [How user leaves] |
```

## Output

This skill produces:
- `journey-map.md`
- `{flow-name}.md`

Agent handles placement in `artifacts/{product}/design/flows/`

## Error Handling

### No Stories Provided
```
Action: "No user stories found. Run product-requirements first."
```

### Missing Acceptance Criteria
```
Action: "Story '[X]' missing criteria. Add GIVEN/WHEN/THEN before creating flows."
```

### Ambiguous Actions
```
Action: "Action '[X]' is ambiguous. Clarify:
        - What does user click/type?
        - What feedback do they receive?"
```

## References

For patterns and examples, see:
- `references/flow-patterns.md` — Common flow structures
- `references/state-diagrams.md` — State modeling patterns