---
name: product-design-wireframes
description: Transform flows into visual specifications using atomic design. Use when creating wireframes, component specs, or UI architecture from user flows.
---

# Product Design Wireframes

Transform user flows into visual specifications using atomic design hierarchy and AI UX patterns.

## Overview

This skill converts flow diagrams into wireframe specifications organized by atomic design levels. Integrates AI UX patterns for AI-powered features.

**Primary Use Cases**: Wireframe creation, component specification, UI architecture, AI feature design.

**Based on**: Atomic Design (Brad Frost) + AI UX Patterns (Shape of AI, Microsoft HAI, Google PAIR)

## Core Functions

### 1. Apply Atomic Design Hierarchy

Organize UI specifications from smallest to largest.

**The Five Levels:**
```
ATOMS → MOLECULES → ORGANISMS → TEMPLATES → PAGES
  │         │           │           │          │
button   search      header    blog       actual
input    form        nav       template   content
label    card        footer
```

| Level | Definition | Example |
|-------|------------|---------|
| **Atoms** | Smallest building blocks | Button, input, label, icon |
| **Molecules** | Atoms with single function | Search form, form field, stat |
| **Organisms** | Complex UI sections | Header, card, sidebar, modal |
| **Templates** | Page-level structure | Two-column layout, dashboard |
| **Pages** | Templates with real content | Actual dashboard with data |

### 2. Define Design Tokens (Atoms)

Start with the foundational design decisions.

**Token Categories:**
```
## Design Tokens

### Colors
- Primary: #0066CC
- Secondary: #6B7280
- Success: #10B981
- Warning: #F59E0B
- Error: #EF4444
- Background: #FFFFFF
- Surface: #F9FAFB
- Text: #111827
- Text Secondary: #6B7280

### Typography
- Font Family: Inter, system-ui, sans-serif
- Heading 1: 32px / 700
- Heading 2: 24px / 600
- Heading 3: 18px / 600
- Body: 16px / 400
- Small: 14px / 400
- Caption: 12px / 400

### Spacing
- xs: 4px
- sm: 8px
- md: 16px
- lg: 24px
- xl: 32px
- 2xl: 48px

### Border Radius
- sm: 4px
- md: 8px
- lg: 12px
- full: 9999px

### Shadows
- sm: 0 1px 2px rgba(0,0,0,0.05)
- md: 0 4px 6px rgba(0,0,0,0.1)
- lg: 0 10px 15px rgba(0,0,0,0.1)
```

### 3. Specify Components

For each component in the flow, create a specification.

**Component Spec Template:**
```
## Component: {Name}

### Level
[Atom / Molecule / Organism]

### Description
[What this component does and when to use it]

### Anatomy
┌─────────────────────────────────┐
│  [Label]                        │
│  ┌─────────────────────────┐    │
│  │ [Icon] [Input field]    │    │
│  └─────────────────────────┘    │
│  [Helper text]                  │
└─────────────────────────────────┘

### Variants
| Variant | When to Use |
|---------|-------------|
| Default | Normal state |
| Filled | Has user input |
| Error | Validation failed |
| Disabled | Not interactive |
| Loading | Processing |

### States
- Default: [Description]
- Hover: [Description]
- Focus: [Description]
- Active: [Description]
- Disabled: [Description]
- Error: [Description]
- Loading: [Description]

### Props/Inputs
| Prop | Type | Default | Description |
|------|------|---------|-------------|
| label | string | - | Field label |
| placeholder | string | - | Placeholder text |
| error | string | null | Error message |
| disabled | boolean | false | Disable input |

### Usage Guidelines
- DO: [Good usage]
- DO: [Good usage]
- DON'T: [Bad usage]
- DON'T: [Bad usage]

### Accessibility
- [ ] Has visible label
- [ ] Error announced to screen readers
- [ ] Keyboard navigable
- [ ] Sufficient color contrast
```

### 4. Create Wireframe Layouts

Convert flows into visual page layouts.

**Wireframe Template:**
```
## Wireframe: {Screen Name}

### Purpose
[What user accomplishes on this screen]

### Entry Points
- From: [Previous screen/state]
- User context: [What they know/have done]

### Layout (Template Level)
┌─────────────────────────────────────────┐
│               [Header]                   │
├──────────────┬──────────────────────────┤
│              │                           │
│  [Sidebar]   │      [Main Content]       │
│              │                           │
│              │  ┌─────────────────────┐  │
│              │  │    [Component]      │  │
│              │  └─────────────────────┘  │
│              │                           │
│              │  ┌─────────────────────┐  │
│              │  │    [Component]      │  │
│              │  └─────────────────────┘  │
│              │                           │
├──────────────┴──────────────────────────┤
│               [Footer]                   │
└─────────────────────────────────────────┘

### Components Used
| Component | Type | Purpose |
|-----------|------|---------|
| Header | Organism | Navigation, branding |
| Sidebar | Organism | Secondary nav |
| [Component] | [Type] | [Purpose] |

### Interactions
| Element | Action | Result |
|---------|--------|--------|
| [Button] | Click | [Navigate to X] |
| [Link] | Click | [Open modal] |
| [Input] | Submit | [Process data] |

### States
- Default: [What user sees on load]
- Loading: [During data fetch]
- Empty: [When no data]
- Error: [When something fails]
```

### 5. Apply AI UX Patterns

For AI-powered features, apply specific patterns.

**AI Pattern Categories:**
```
## AI Patterns Applied

### Wayfinding (Help users start)
- [ ] Suggestions: Starter prompts provided
- [ ] Templates: Pre-structured formats available
- [ ] Examples: Sample inputs shown

### Trust Builders (Build confidence)
- [ ] Disclosure: AI content marked clearly
- [ ] Citations: Sources linked
- [ ] Confidence: Certainty levels shown
- [ ] Caveats: Limitations disclosed

### Governors (Maintain control)
- [ ] Action Plan: AI shows what it will do
- [ ] Controls: Stop/pause available
- [ ] Feedback: Thumbs up/down
- [ ] Undo: Can reverse AI actions

### Error Handling (Design for wrong)
- [ ] Easy dismissal: Can ignore suggestions
- [ ] Easy correction: Can fix mistakes
- [ ] Graceful degradation: Fails safely
```

**AI Component Spec Addition:**
```
### AI-Specific Properties

**Spatial Pattern:** [Alongside / Layered / Integrated / Conversational]

**Trust Patterns:**
- Disclosure: [How AI is identified]
- Confidence: [How certainty shown]
- Citations: [How sources linked]

**Control Patterns:**
- Invoke: [How to trigger AI]
- Dismiss: [How to ignore/hide]
- Correct: [How to fix mistakes]
- Stop: [How to interrupt]

**Error States:**
- AI unavailable: [Fallback behavior]
- Low confidence: [How indicated]
- Wrong output: [Recovery path]
```

### 6. Component Inventory

Create a complete inventory before building.

**Inventory Template:**
```
## Component Inventory

### Atoms (Foundation)
| Component | Variants | Status |
|-----------|----------|--------|
| Button | primary, secondary, ghost, link | Needed |
| Input | text, email, password, search | Needed |
| Label | default, required, optional | Needed |
| Icon | [icon set name] | Needed |

### Molecules (Functional Units)
| Component | Atoms Used | Status |
|-----------|------------|--------|
| Form Field | Label + Input + Helper | Needed |
| Search Bar | Input + Button + Icon | Needed |
| Stat Card | Number + Label + Trend | Needed |

### Organisms (Sections)
| Component | Molecules Used | Status |
|-----------|----------------|--------|
| Header | Logo + Nav + Search + Avatar | Needed |
| Card | Title + Body + Actions | Needed |
| Modal | Header + Content + Footer | Needed |

### Templates (Layouts)
| Template | Organisms Used | Pages Using |
|----------|----------------|-------------|
| Dashboard | Header, Sidebar, Card Grid | Home, Analytics |
| Form Page | Header, Form, Footer | Settings, Profile |
| Detail Page | Header, Content, Sidebar | Item View |
```

## Workflows

### Flows → Wireframes

```
1. Read flows from product-design-flows
2. Inventory required components
3. Define design tokens
4. Spec atoms (buttons, inputs, etc.)
5. Compose molecules (form fields, etc.)
6. Build organisms (header, cards, etc.)
7. Create templates (layouts)
8. Apply to pages with real content
9. Output: Component specs + wireframes
```

### AI Feature → AI Wireframe

```
1. Identify AI interaction type
2. Select spatial pattern (sidebar, inline, etc.)
3. Apply wayfinding patterns (suggestions, examples)
4. Add trust patterns (disclosure, citations)
5. Design control patterns (stop, undo, feedback)
6. Plan error states (fallbacks, recovery)
7. Output: AI-aware wireframe spec
```

## Input Requirements

**Required:**
- Flow diagrams from product-design-flows
- User stories for context

**Optional:**
- Existing design system
- Brand guidelines
- Technical constraints

## Output Structure

```
Wireframe Output:
├── tokens.md                # Design tokens
├── components/
│   ├── atoms/               # Button, Input, etc.
│   ├── molecules/           # Form Field, Search, etc.
│   └── organisms/           # Header, Card, etc.
├── templates/               # Layout structures
├── wireframes/              # Page wireframes
│   ├── {screen-1}.md
│   ├── {screen-2}.md
│   └── ...
└── inventory.md             # Component inventory
```

## Integration

**Receives from:**
- product-design-flows - flows to visualize
- Canvas 04-segments - user context
- Existing design system (if any)

**Provides to:**
- product-specification - visuals for shaped pitches
- Engineering - component specifications
- Designers - wireframe starting point

## Best Practices

### Atomic Design
1. **Build up**: Atoms → Molecules → Organisms
2. **Single responsibility**: Each component does one thing
3. **Context-agnostic**: Components work anywhere
4. **Document states**: Every component has multiple states

### AI Features
1. **Disclose AI**: Always mark AI-generated content
2. **Show confidence**: Users need to know certainty
3. **Easy escape**: Never trap users in AI flows
4. **Design for wrong**: AI WILL make mistakes

### Wireframes
1. **Structure over visuals**: Focus on what, not how it looks
2. **Real content**: Test with actual data lengths
3. **All states**: Default, loading, empty, error
4. **Responsive**: Consider mobile, tablet, desktop

### Avoiding Pitfalls
- Do NOT design final visuals (that's UI design)
- Do NOT skip empty/error states
- Do NOT forget responsive behavior
- Do NOT ignore accessibility

## Key Principles

> "You're not designing pages, you're designing systems of components."

> "Human-centric design: Patterns prioritize clarity, control, and trust rather than opaque 'magic.'"

> "Make clear what the system can do. Make clear how well the system can do what it can do." — Microsoft HAI

---

**Related Playbooks:**
- [design-systems](research/playbooks/design-systems.md)
- [ai-product-design](research/playbooks/ai-product-design.md)
