# Product Workflow

How to translate Canvas strategy into engineering-ready specifications using the Product layer.

---

## Overview

The Product layer bridges Canvas (strategy) and Engineering (code):

```
Canvas → Product → Engineering → Verified Code
           │
           ├── product-requirements
           ├── product-design-flows
           ├── product-design-wireframes
           ├── product-prioritization
           └── product-specification
```

**Agent:** `product-builder`
**Skills:** 5 product skills
**Output:** `artifacts/product/{feature}/`

---

## When to Use

| Situation | Route |
|-----------|-------|
| "Translate Canvas to requirements" | `product-builder` (activity_type: requirements) |
| "Create user stories" | `product-builder` (activity_type: requirements) |
| "Map user journeys" | `product-builder` (activity_type: flows) |
| "Design the UI" | `product-builder` (activity_type: wireframes) |
| "What should we build first?" | `product-builder` (activity_type: prioritization) |
| "Prepare for engineering" | `product-builder` (activity_type: specification) |
| "Full Canvas to spec" | `product-builder` (activity_type: full) |

---

## The 5 Skills

### 1. product-requirements

**Purpose:** Transform Canvas strategy into user stories

**Input:**
- Canvas 05-problem (problems to solve)
- Canvas 04-segments (target users)
- Canvas 09-solution (solution direction)

**Output:**
- `context_summary.md` - Canvas synthesis
- `story_map.md` - Visual story map (backbone → tasks → stories)
- `stories/US-*.md` - Individual user stories with acceptance criteria

**Key Concepts:**
- Story Map: Backbone (activities) → Tasks → Stories
- Walking Skeleton: Thinnest slice spanning all activities
- Horizontal slices for releases (not vertical features)

**Based on:** Marty Cagan (Product Operating Model) + Jeff Patton (User Story Mapping)

---

### 2. product-design-flows

**Purpose:** Transform stories into user journeys and flow diagrams

**Input:**
- User stories from product-requirements
- Persona context (04-segments)

**Output:**
- `journey_map.md` - 5-stage journey (Aware → Succeed)
- `flows/*.md` - Flow diagrams (breadboards)
- State diagrams

**Key Concepts:**
- Journey stages: Aware → Consider → Acquire → Use → Succeed
- Breadboards: Places + Affordances (not visual design)
- Happy path first, then error flows

**Based on:** User Story Mapping + Shape Up (breadboarding)

---

### 3. product-design-wireframes

**Purpose:** Transform flows into visual specifications

**Input:**
- Flow diagrams from product-design-flows
- Design system (if exists)

**Output:**
- `tokens.md` - Design tokens (colors, typography, spacing)
- `components/` - Component specs (atoms, molecules, organisms)
- `wireframes/*.md` - Page layouts with ASCII diagrams

**Key Concepts:**
- Atomic Design: Atoms → Molecules → Organisms → Templates → Pages
- All states: Default, Loading, Empty, Error
- AI UX patterns for AI features

**Based on:** Brad Frost (Atomic Design) + AI UX Patterns (Microsoft HAI, Google PAIR)

---

### 4. product-prioritization

**Purpose:** Score and prioritize features

**Input:**
- Feature list or user stories
- Business context (Canvas)

**Output:**
- `dhm_scores.md` - DHM scoring for each initiative
- `stack_rank.md` - Prioritized list
- `daily_lno.md` - Tactical task priorities (optional)

**Key Frameworks:**

**DHM (Strategic):**
| Dimension | Question | Score |
|-----------|----------|-------|
| Delight | Will customers love this? | 1-5 |
| Hard to copy | Can competitors replicate? | 1-5 |
| Margin | Does this improve economics? | 1-5 |

**Recommendation:**
- 12+ → Prioritize
- 9-11 → Consider
- <9 → Deprioritize

**LNO (Tactical):**
| Type | ROI | Approach |
|------|-----|----------|
| L (Leverage) | 10-100x | Perfectionist mode |
| N (Neutral) | 1x | Good enough |
| O (Overhead) | <1x | Minimum viable |

**Based on:** Gibson Biddle (DHM/Glee) + Shreyas Doshi (LNO)

---

### 5. product-specification

**Purpose:** Create shaped pitches ready for engineering

**Input:**
- Prioritized features
- All design artifacts (stories, flows, wireframes)

**Output:**
- `pitches/pitch-*.md` - Shaped pitches
- `specs/spec-*.md` - Engineering specifications

**Shaped Pitch Structure:**
1. **Problem** - What we're solving
2. **Appetite** - Time box (1 week / 2 weeks / 6 weeks)
3. **Solution** - Fat marker sketch + breadboard
4. **Rabbit Holes** - Known risks and mitigations
5. **No-Gos** - Explicitly out of scope

**Key Principle:** Fixed time, variable scope

**Based on:** Ryan Singer (Shape Up) + Jake Knapp (Design Sprint)

---

## Full Pipeline

When you need end-to-end Canvas → Engineering spec:

```
1. product-requirements
   Canvas → User stories + Story map

2. product-design-flows
   Stories → Journey map + Flow diagrams

3. product-design-wireframes
   Flows → Component specs + Wireframes

4. product-prioritization
   Features → DHM scores + Stack rank

5. product-specification
   Prioritized features → Shaped pitches + Eng specs
```

**Invoke:** `product-builder` with `activity_type: full`

---

## Output Structure

```
artifacts/product/{feature-name}/
├── requirements/
│   ├── context_summary.md
│   ├── story_map.md
│   └── stories/
│       ├── US-001.md
│       └── US-002.md
├── flows/
│   ├── journey_map.md
│   └── flows/
│       └── flow-{task}.md
├── wireframes/
│   ├── tokens.md
│   ├── components/
│   │   ├── atoms/
│   │   ├── molecules/
│   │   └── organisms/
│   └── wireframes/
│       └── {screen}.md
├── prioritization/
│   ├── dhm_scores.md
│   └── stack_rank.md
└── specs/
    ├── pitch-{feature}.md
    └── spec-{feature}.md
```

---

## Quality Gates

| From | To | Gate |
|------|----|------|
| Canvas | Requirements | Canvas 05, 04, 09 populated |
| Requirements | Flows | Stories have acceptance criteria |
| Flows | Wireframes | Happy path + error flows defined |
| Wireframes | Prioritization | Component inventory complete |
| Prioritization | Specification | DHM ≥ 9 (or explicit override) |
| Specification | Engineering | Rabbit holes identified, no-gos explicit |

---

## Integration

### With Canvas
- Reads: 04-segments, 05-problem, 09-solution, 10-assumptions
- Links stories to problems and assumptions

### With Goals
- Product work should link to goals
- Use `goal-setter` to create product goals
- Track with `goal-tracker`

### With Engineering
- Specifications flow to `lean-os` for implementation
- Shaped pitches define scope boundaries

---

## Playbooks

The Product skills are based on these processed sources:

| Source | Playbook |
|--------|----------|
| Marty Cagan | `research/playbooks/product-operating-model.md` |
| Ryan Singer | `research/playbooks/product-shaping.md` |
| Jake Knapp | `research/playbooks/product-sprint.md` |
| Jeff Patton | `research/playbooks/user-story-mapping.md` |
| Gibson Biddle + Shreyas Doshi | `research/playbooks/product-prioritization.md` |
| Brad Frost | `research/playbooks/design-systems.md` |
| AI UX Compilation | `research/playbooks/ai-product-design.md` |

---

## Quick Reference

**Invoke full pipeline:**
```
Use product-builder with activity_type: full
```

**Invoke single skill:**
```
Use product-builder with activity_type: requirements|flows|wireframes|prioritization|specification
```

**DHM Quick Score:**
```
D (Delight) + H (Hard to copy) + M (Margin) = /15
12+ = Prioritize | 9-11 = Consider | <9 = Deprioritize
```

**Shape Up Appetite:**
```
1-2 weeks = Small batch (well-understood)
6 weeks = Big batch (complex)
1 week spike = Learning first (unknown)
```