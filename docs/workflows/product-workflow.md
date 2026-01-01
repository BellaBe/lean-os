# Product Workflow
┌─────────────────────────────────────────────────────────────────┐
│                          CANVAS                                  │
│              (05-problem, 04-segments, 09-solution)              │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                   product-requirements                           │
│                                                                  │
│  Input: Canvas                                                   │
│  Output: design/requirements/                                    │
│          ├── context.md                                          │
│          ├── story-map.md                                        │
│          └── stories/US-{NNN}.md                                 │
│  References: story-examples.md                                   │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                   product-design-flows                           │
│                                                                  │
│  Input: Stories                                                  │
│  Output: design/flows/                                           │
│          ├── journey-map.md                                      │
│          └── {flow-name}.md                                      │
│  References: flow-patterns.md                                    │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                  product-design-wireframes                       │
│                                                                  │
│  Input: Flows                                                    │
│  Output: design/                                                 │
│          ├── tokens.md                                           │
│          ├── components/inventory.md                             │
│          ├── components/{name}.md                                │
│          └── wireframes/{screen}.md                              │
│  References: component-patterns.md, ai-patterns.md               │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                   product-prioritization                         │
│                                                                  │
│  Input: Features/Stories                                         │
│  Output: prioritization/                                         │
│          └── {date}-stack-rank.md                                │
│  References: dhm-examples.md                                     │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                     product-handoff                              │
│                                                                  │
│  Input: Prioritized feature + design artifacts                   │
│  Output: features/{slug}/v{N}/                                   │
│          └── handoff.md                                          │
│  References: handoff-examples.md                                 │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                        ENGINEERING                               │
│                   (FE/BE skills take over)                       │
└─────────────────────────────────────────────────────────────────┘



## All Files Per Skill
### product-requirements
```
product-requirements/
├── SKILL.md (157 lines)
│   - Canvas → context.md, story-map.md, stories/
└── references/
    └── story-examples.md (75 lines)
        - Good/bad story examples
        - GIVEN/WHEN/THEN patterns
        - Size guidelines
```

### product-design-flows
```
product-design-flows/
├── SKILL.md (140 lines)
│   - Stories → journey-map.md, {flow}.md
└── references/
    └── flow-patterns.md (107 lines)
        - Linear, branching, loop, hub-and-spoke
        - Error flow patterns
        - State diagram patterns
        - Anti-patterns to avoid
```
   
### product-design-wireframes
```
product-design-wireframes/
├── SKILL.md (214 lines)
│   - Flows → tokens.md, components/, wireframes/
└── references/
    ├── component-patterns.md (167 lines)
    │   - Atomic design hierarchy
    │   - State patterns (empty, loading, error)
    │   - Layout patterns
    │   - Anti-patterns
    └── ai-patterns.md (166 lines)
        - Wayfinding (suggestions, templates, examples)
        - Trust (disclosure, citations, confidence)
        - Control (preview, stop, feedback, undo)
        - Error handling
```

### product-prioritization
```
product-prioritization/
├── SKILL.md (148 lines)
│   - Features → {date}-stack-rank.md
└── references/
    └── dhm-examples.md (75 lines)
        - High/medium/low score examples
        - Hard-to-copy sources
        - Common scoring mistakes
```

### product-handoff
```
product-handoff/
├── SKILL.md (252 lines)
│   - Feature → handoff.md (context, scope, criteria, examples, tests)
└── references/
    └── handoff-examples.md (164 lines)
        - Complete handoff example
        - Criteria writing patterns
        - GIVEN/WHEN/THEN examples
```