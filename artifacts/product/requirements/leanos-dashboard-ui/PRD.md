# PRD: LeanOS Dashboard UI

## Overview

**Objective:** Create a showcase dashboard that visualizes the LeanOS autonomous operating system, demonstrating its value proposition and enabling users to understand system state at a glance.

**Owner:** Product Team
**Target Release:** 4-5 weeks from start
**Status:** Release 1 COMPLETE (2024-12-27)

---

## Implementation Status

| Release | Status | Pages Delivered |
|---------|--------|-----------------|
| R1 Walking Skeleton | **COMPLETE** | /, /canvas, /threads, /skills |
| R2 Goal-Centric | PARTIAL | /goals (list only) |
| R3 Deep Exploration | PARTIAL | /agents, /research, /artifacts |
| R4 Complete | PENDING | - |

**Total Pages Delivered:** 8 routes functional

## Context

### Problem

LeanOS is a powerful AI-native operating system with 70+ skills, 13 agents, and a sophisticated goal-driven architecture. However, all operations happen invisibly in the file system. Users struggle to:

1. **See what's happening** - No visibility into autonomous AI operations
2. **Understand the system** - Complex architecture with goals, canvas, threads, skills
3. **Trust autonomous decisions** - Can't see decision rationale or impact scores

### User Segment

**Primary:** Startup founders/solo operators using LeanOS
- Technical enough to use CLI tools
- Want to operate like a 5-10 person team
- Spend <30 min/day on operations
- Need visibility into AI decision-making

**Secondary:** Potential LeanOS adopters
- Exploring LeanOS as a solution
- Need to understand value proposition quickly

### Assumption Being Tested

A1: Users will understand LeanOS faster through visualization than documentation
A2: Seeing autonomous decisions in real-time builds trust, not fear
A3: A showcase UI will drive LeanOS adoption more than documentation

---

## User Stories

### Release 1: Walking Skeleton (P0)

| ID | Story | Priority |
|----|-------|----------|
| US-001 | Dashboard Home - See entire system at a glance | P0 |
| US-002 | System Stats - Visual metric cards | P0 |
| US-016 | Canvas Overview - 15-section grid with status | P0 |
| US-019 | Active Threads - Real-time execution view | P0 |
| US-008 | Skill Catalog - Browsable 70+ capabilities | P0 |

### Release 2: Goal-Centric View (P1)

| ID | Story | Priority |
|----|-------|----------|
| US-004 | Goal List - All active goals | P1 |
| US-005 | Goal Detail - Structure and state | P1 |
| US-006 | Goal Progress - Visual indicators | P1 |
| US-012 | Thread List - All threads with filtering | P1 |
| US-013 | Thread Detail - Full 6-stage view | P1 |

### Release 3-4: Deep Exploration & Complete (P2-P3)

Additional detail views for power users and demo scenarios.

---

## Success Metrics

| Metric | Current | Target | How Measured |
|--------|---------|--------|--------------|
| Time to understand | N/A | <60 seconds | User can explain LeanOS after viewing |
| Information density | N/A | High | Key stats visible without scrolling |
| Navigation depth | N/A | <3 clicks | Any detail accessible quickly |
| Visual appeal | N/A | Demo-ready | Suitable for presentations |

---

## Scope

### In Scope

**Pages:**
- Dashboard Home with stats cards
- Canvas Overview (15-section grid)
- Thread List (grouped by type, 6-stage progress)
- Skill Catalog (70 skills by category)
- Agent Catalog (13 orchestrators)
- Goal List and Detail
- Research Library

**Features:**
- Read-only visualization of leanos.json data
- Navigation between all major sections
- Progress indicators for threads and canvas
- Search/filter for skills

### Out of Scope (No-Gos)

- **Write operations** - No creating/editing goals, threads, or canvas (CLI only)
- **Real-time updates** - Static data load, no websockets
- **Authentication** - Public showcase, no login required
- **Settings/Preferences** - No user customization
- **Interactive CLI** - No embedded terminal
- **Multi-tenant** - Single instance visualization

### Future Considerations (V2)

- Real-time thread status updates
- Interactive Canvas editing
- Goal creation wizard
- Thread stage approval workflows
- Skill invocation from UI

---

## Risks & Dependencies

| Risk | Impact | Mitigation |
|------|--------|------------|
| Data structure changes | H | Keep leanos.json schema stable |
| Component library gaps | M | Use Untitled UI, build custom if needed |
| Performance with large data | L | Virtualize long lists, lazy load |
| Complex visualizations | M | Start simple, iterate based on feedback |

---

## Open Questions

- [ ] Should Canvas sections show full markdown content or summary?
- [ ] How to visualize goal-thread relationships effectively?
- [ ] Should Skills/Agents be combined or separate pages?
- [ ] What visual style best represents "AI operations"?

---

## Key Pages Specification

### 1. Dashboard Home (/)

**Purpose:** First impression, system overview

**Components:**
- Header with LeanOS branding + business mode indicator
- 4 stat cards (Goals, Canvas, Threads, Skills)
- Canvas health mini-grid (15 cells)
- Active threads summary (by type)
- Recent activity feed

**Data:**
```typescript
interface DashboardData {
  goals: { active: number; completed: number };
  canvas: { health: number; mode: string; populated: number };
  threads: { total: number; active: number; byType: Record<string, number> };
  skills: { total: number };
  agents: { total: number };
}
```

### 2. Canvas Overview (/canvas)

**Purpose:** Visualize strategic foundation

**Components:**
- Health progress bar (X% populated)
- 3x5 grid of Canvas sections
- Status indicators (populated/missing)
- Section grouping by theme (optional)

**Data:**
```typescript
interface CanvasSection {
  number: string;
  name: string;
  slug: string;
  status: 'populated' | 'missing';
  content: string;
}
```

### 3. Threads (/threads)

**Purpose:** Show execution activity

**Components:**
- Filter tabs (All/Sales/Marketing/Operations)
- Thread cards with 6-stage progress
- Stage indicators (completed/pending)
- Grouped by type

**Data:**
```typescript
interface Thread {
  type: string;
  name: string;
  path: string;
  currentStage: number;
  stages: Array<{
    number: number;
    name: string;
    status: 'pending' | 'completed';
  }>;
}
```

### 4. Skills (/skills)

**Purpose:** Show system capabilities

**Components:**
- Category sidebar (9 categories)
- Skill list with name and purpose
- Search/filter input
- Agent sidebar (13 agents)

**Data:**
```typescript
interface Skill {
  name: string;
  category: string;
  purpose: string;
  whenToUse: string[];
  location: string;
}
```

---

## Visual Design Guidelines

### Style

- Clean, modern, professional
- Dark mode preferred (tech/AI aesthetic)
- High information density
- Consistent with Untitled UI design system

### Colors

- Use status colors: green (success/populated), amber (warning), red (error), gray (missing/pending)
- Brand colors from Untitled UI palette
- Clear visual hierarchy

### Typography

- Headlines: Bold, clear
- Body: Readable at small sizes
- Monospace for paths/code

### Icons

- Use @untitledui/icons throughout
- Consistent icon sizing
- Meaningful iconography for sections

---

## Technical Architecture

### Data Flow

```
leanos.json (static file)
      |
      v
Next.js App (SSR/Client)
      |
      v
React Components
      |
      v
Untitled UI Components
```

### Routes

```
/                    - Dashboard Home
/canvas              - Canvas Overview
/canvas/[slug]       - Canvas Section Detail
/threads             - Thread List
/threads/[type]/[name] - Thread Detail
/goals               - Goal List
/goals/[id]          - Goal Detail
/skills              - Skill Catalog
/skills/[name]       - Skill Detail
/agents              - Agent Catalog
/research            - Research Library
```

### Data Loading

- Server-side: Load leanos.json at build/request time
- Client-side: React Context for global data access
- Caching: Static file, refresh on rebuild

---

## Implementation Plan

### Week 1: Walking Skeleton
- Dashboard layout + navigation
- Stat cards component
- Canvas grid component
- Thread list component
- Skill catalog component

### Week 2: Goal-Centric
- Goal list and detail pages
- Thread detail with 6-stage view
- Goal-thread linking

### Week 3: Deep Exploration
- Goal tree visualization
- Canvas section detail
- Agent catalog

### Weeks 4-5: Polish
- Remaining detail views
- Visual refinements
- Performance optimization

---

## Appendix

### File Structure

```
artifacts/product/requirements/leanos-dashboard-ui/
├── PRD.md                    # This file
├── context_summary.md        # Product context
├── story_map.md              # Visual story map
├── release_plan.md           # Release breakdown
└── stories/
    ├── US-001-dashboard-home.md
    ├── US-002-system-stats.md
    ├── US-008-skill-catalog.md
    ├── US-016-canvas-overview.md
    └── US-019-active-threads.md
```

### Related Documents

- [LeanOS Architecture](/home/bellabe/lean-os/docs/reference/architecture.md)
- [What is LeanOS](/home/bellabe/lean-os/docs/reference/what-is-leanos.md)
- [Causal Flow](/home/bellabe/lean-os/docs/workflows/causal-flow.md)
