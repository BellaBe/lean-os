# Release Plan: LeanOS Dashboard UI

## Release Overview

| Release | Theme | Stories | Appetite | Priority | Status |
|---------|-------|---------|----------|----------|--------|
| R1 | Walking Skeleton | 5 | 1 week | P0 - MUST HAVE | **COMPLETE** |
| R2 | Goal-Centric View | 5 | 1 week | P1 - HIGH | PARTIAL |
| R3 | Deep Exploration | 5 | 1 week | P2 - MEDIUM | PARTIAL |
| R4 | Complete Experience | 11 | 2 weeks | P3 - LOW | PENDING |

---

## Release 1: Walking Skeleton (P0) - COMPLETE

**Goal:** Demonstrate the LeanOS value proposition in a single impressive dashboard.

**Appetite:** 1 week
**Status:** COMPLETE (2024-12-27)

### Stories Included

| ID | Story | Estimate | Status |
|----|-------|----------|--------|
| US-001 | Dashboard Home | M | DONE |
| US-002 | System Stats | S | DONE |
| US-016 | Canvas Overview | M | DONE |
| US-019 | Active Threads | M | DONE |
| US-008 | Skill Catalog | M | DONE |

### Success Criteria

- [x] User can open dashboard and understand LeanOS in <60 seconds
- [x] All 4 main stat cards display correctly
- [x] Canvas 15-section grid renders with status indicators
- [x] Thread list shows grouped by type with stage progress
- [x] Skill catalog is browsable by category

### Pages/Routes

```
/                 --> Dashboard Home (US-001, US-002) ✓
/canvas           --> Canvas Overview (US-016) ✓
/threads          --> Thread List (US-019) ✓
/skills           --> Skill Catalog (US-008) ✓
```

### Implementation Notes

**Components created:**
- `src/components/leanos/logo.tsx` - LeanOS branding
- `src/components/leanos/sidebar.tsx` - Navigation sidebar with mode badge
- `src/components/leanos/stat-card.tsx` - Metric display cards
- `src/components/leanos/canvas-grid.tsx` - 15-section visualization
- `src/components/leanos/thread-progress.tsx` - 6-stage progress bars

**Data layer:**
- `src/lib/types.ts` - TypeScript interfaces
- `src/lib/data.ts` - Data loading and stats computation
- `src/lib/navigation.ts` - Route configuration
- `src/providers/data-provider.tsx` - React context

---

## Release 2: Goal-Centric View (P1) - PARTIAL

**Goal:** Show the goal-driven operating model with progress tracking.

**Appetite:** 1 week
**Status:** PARTIAL (2024-12-27)

### Stories Included

| ID | Story | Estimate | Status |
|----|-------|----------|--------|
| US-004 | Goal List | S | DONE (empty state) |
| US-005 | Goal Detail | M | PENDING |
| US-006 | Goal Progress | S | PENDING |
| US-012 | Thread List (enhanced) | S | DONE (filtering by type) |
| US-013 | Thread Detail | M | PENDING |

### Success Criteria

- [x] Goal list shows all active/completed/abandoned goals (empty state ready)
- [ ] Goal detail displays objective, success criteria, plan, state
- [ ] Thread detail shows all 6 stages with content
- [ ] Goals and threads are linked visually

### Pages/Routes

```
/goals            --> Goal List (US-004) ✓
/goals/[id]       --> Goal Detail (US-005, US-006) - PENDING
/threads/[path]   --> Thread Detail (US-013) - PENDING
```

---

## Release 3: Deep Exploration (P2) - PARTIAL

**Goal:** Enable deep understanding for power users and demos.

**Appetite:** 1 week
**Status:** PARTIAL (2024-12-27)

### Stories Included

| ID | Story | Estimate | Status |
|----|-------|----------|--------|
| US-007 | Goal Tree | M | PENDING |
| US-017 | Section Detail | S | PENDING |
| US-018 | Canvas Health Map | M | DONE (in Canvas Overview) |
| US-010 | Agent Catalog | S | DONE |
| US-022 | Source Library | M | DONE (empty state) |

### Success Criteria

- [ ] Goal tree shows goal -> subgoal -> thread hierarchy
- [ ] Canvas sections show full markdown content
- [x] Agent catalog shows skill routing
- [x] Research sources are browsable

### Pages/Routes

```
/goals/tree       --> Goal Tree (US-007) - PENDING
/canvas/[slug]    --> Section Detail (US-017) - PENDING
/agents           --> Agent Catalog (US-010) ✓
/research         --> Source Library (US-022) ✓
/artifacts        --> Artifact Browser (BONUS) ✓
```

---

## Release 4: Complete Experience (P3)

**Goal:** Polish and complete all remaining functionality.

**Appetite:** 2 weeks

### Stories Included

| ID | Story | Estimate | Why Nice |
|----|-------|----------|----------|
| US-003 | Quick Actions | S | Shortcut commands |
| US-009 | Skill Detail | M | Individual skill view |
| US-011 | Agent Detail | S | Agent skill routing view |
| US-014 | Stage Viewer | S | Individual stage content |
| US-015 | Thread Timeline | M | Temporal activity view |
| US-023 | Playbook Library | M | Generated playbooks |
| US-024 | Source Viewer | S | Source detail |
| US-025 | Artifact Browser | M | Generated artifacts |
| US-026 | Artifact Detail | S | Artifact content |

---

## Technical Considerations

### Data Source

All data comes from `/public/data/leanos.json`:

```json
{
  "goals": [],
  "canvas": { "mode": "BOOTSTRAP", "sections": [...], "health": 0 },
  "threads": [...],
  "skills": [...],
  "agents": [...],
  "artifacts": [],
  "research": { "sources": [], "playbooks": [] },
  "meta": { "lastBuilt": "...", "version": "1.0.0" }
}
```

### Component Library

Use existing Untitled UI components in `/src/components/`:
- Base components (buttons, inputs, cards, badges)
- Application components (navigation, tables, modals)
- Foundation components (icons, featured icons)

### Navigation Structure

```
LeanOS Dashboard
├── Home (/)
├── Goals (/goals)
│   ├── List
│   ├── Detail (/goals/[id])
│   └── Tree (/goals/tree)
├── Canvas (/canvas)
│   └── Section (/canvas/[slug])
├── Threads (/threads)
│   └── Detail (/threads/[type]/[name])
├── Skills (/skills)
│   ├── Catalog
│   └── Detail (/skills/[name])
├── Agents (/agents)
│   └── Detail (/agents/[name])
└── Research (/research)
    ├── Sources
    └── Playbooks
```

---

## Implementation Priority

### Week 1 (R1 - Walking Skeleton)
1. Dashboard layout with navigation
2. Stats cards component
3. Canvas grid component
4. Thread list component
5. Skill catalog component

### Week 2 (R2 - Goal-Centric)
1. Goal list and detail pages
2. Thread detail with 6-stage view
3. Goal-thread linking
4. Progress indicators

### Week 3 (R3 - Deep Exploration)
1. Goal tree visualization
2. Canvas section detail
3. Agent catalog
4. Research source browser

### Weeks 4-5 (R4 - Complete)
1. Remaining detail views
2. Polish and refinements
3. Timeline views
4. Artifact browser
