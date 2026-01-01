---
name: product-design-wireframes
description: Transform flows into visual specifications using atomic design. Use when creating wireframes, component specs, UI architecture, or design token inventory.
allowed-tools: Read, Grep, Glob
---

# Product Design Wireframes

Transform flows into wireframe specifications using atomic design hierarchy.

## Purpose

Convert flow diagrams into wireframe specifications organized by atomic design levels.

## When to Apply

- Creating wireframes from flows
- Building component specifications
- Defining design tokens
- Inventorying existing vs needed components

## Boundaries

### This Skill Produces
- `tokens.md` — Design tokens inventory
- `components/inventory.md` — What exists, what's needed
- `components/{name}.md` — Component specs
- `wireframes/{screen}.md` — Screen layouts

### This Skill Does NOT Produce
- Final visual designs → UI designer
- User flows → Use `product-design-flows`
- Engineering handoffs → Use `product-handoff`

### Handoff Points
- Receives from: product-design-flows
- Provides to: product-handoff, Engineering

## Process

### Step 1: Define Tokens

**Output: tokens.md**
```markdown
# Design Tokens

## Colors
| Token | Value | Usage |
|-------|-------|-------|
| primary | #0066CC | Actions, links |
| error | #EF4444 | Errors, destructive |
| text | #111827 | Body text |

## Typography
| Token | Value | Usage |
|-------|-------|-------|
| heading-1 | 32px/700 | Page titles |
| body | 16px/400 | Content |

## Spacing
| Token | Value |
|-------|-------|
| sm | 8px |
| md | 16px |
| lg | 24px |

## Status
- [x] Exists in codebase
- [ ] Needs implementation
```

### Step 2: Inventory Components

**Atomic Design Levels:**
| Level | Definition | Examples |
|-------|------------|----------|
| Atoms | Smallest blocks | Button, Input, Label |
| Molecules | Atoms combined | Form Field, Search Bar |
| Organisms | Complex sections | Header, Card, Modal |

**Output: components/inventory.md**
```markdown
# Component Inventory

## Atoms
| Component | Status | Variants |
|-----------|--------|----------|
| Button | Exists | primary, secondary |
| Input | Exists | text, email |
| Checkbox | Needed | - |

## Molecules
| Component | Status | Uses |
|-----------|--------|------|
| FormField | Exists | Label + Input |
| SearchBar | Needed | Input + Button |

## Organisms
| Component | Status | Uses |
|-----------|--------|------|
| Header | Exists | Logo + Nav |
| ProductCard | Needed | Image + Title + Price |
```

### Step 3: Spec Components

**Output: components/{name}.md**
```markdown
# Component: {Name}

## Level
Atom / Molecule / Organism

## Purpose
[What it does, when to use]

## Anatomy
┌─────────────────────┐
│ [Label]             │
│ ┌─────────────────┐ │
│ │ [Input]         │ │
│ └─────────────────┘ │
│ [Helper text]       │
└─────────────────────┘

## Variants
| Variant | When |
|---------|------|
| Default | Normal |
| Error | Validation failed |
| Disabled | Not interactive |

## States
- Default
- Hover
- Focus
- Disabled
- Error

## Props
| Prop | Type | Default |
|------|------|---------|
| label | string | - |
| error | string | null |
```

### Step 4: Create Wireframes

**Output: wireframes/{screen}.md**
```markdown
# Wireframe: {Screen Name}

## Purpose
[What user accomplishes]

## Layout
┌─────────────────────────────┐
│          [Header]           │
├─────────┬───────────────────┤
│         │                   │
│ [Side]  │    [Content]      │
│         │                   │
└─────────┴───────────────────┘

## Components Used
| Component | Purpose |
|-----------|---------|
| Header | Navigation |
| ProductCard | Display items |

## States
- Default: [Description]
- Loading: [Description]
- Empty: [Description]
- Error: [Description]

## Interactions
| Element | Action | Result |
|---------|--------|--------|
| [Button] | Click | [Navigate] |
```

## Output

This skill produces:
- `tokens.md`
- `components/inventory.md`
- `components/{name}.md`
- `wireframes/{screen}.md`

Agent handles placement in `artifacts/{product}/design/`

## Error Handling

### No Flows Provided
```
Action: "No flows found. Run product-design-flows first."
```

### Missing States in Flow
```
Action: "Flow '[X]' missing states. Add: default, loading, empty, error"
```

### Existing Design System
```
Action: "Design system found at [path]. Extending existing tokens/components."
```

## References

For patterns and examples, see:
- `references/component-patterns.md` — Common component structures
- `references/ai-patterns.md` — AI-specific UI patterns