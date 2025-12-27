# US-001: Dashboard Home

## Status: COMPLETE (2024-12-27)

## Story

As a **startup founder using LeanOS**,
I want to **see my entire business state at a glance when I open the dashboard**,
so that **I can understand system health and know what needs my attention in under 60 seconds**.

## Acceptance Criteria

- [x] GIVEN I open the dashboard, WHEN the page loads, THEN I see a header with "LeanOS" branding and business mode indicator (VENTURE/BOOTSTRAP)
- [x] GIVEN the dashboard loads, WHEN I look at the main area, THEN I see 4-6 key metrics displayed prominently
- [x] GIVEN the dashboard loads, WHEN goals exist, THEN I see a count of active goals with completion percentage
- [x] GIVEN the dashboard loads, WHEN canvas sections exist, THEN I see a visual canvas health indicator (X/15 populated)
- [x] GIVEN the dashboard loads, WHEN threads exist, THEN I see count of active threads and their types
- [x] GIVEN the dashboard loads, WHEN I look at navigation, THEN I can access Goals, Canvas, Threads, Skills, Research sections
- [ ] GIVEN the system has recent activity, WHEN I view the dashboard, THEN I see a "Recent Activity" feed showing last 5 events (DEFERRED)

## Implementation

**File:** `src/app/page.tsx`

**Components used:**
- `StatCard` - 4 metric cards (Goals, Canvas Health, Threads, Skills)
- `CanvasGrid` - Mini 15-section grid
- `ThreadCard` - Active threads summary

**Features delivered:**
- Sidebar navigation with LeanOS branding
- BOOTSTRAP/VENTURE mode badge
- Stats cards with icons and subtitles
- Canvas health progress bar + compact grid
- Active threads list with 6-stage progress

## Links

- **Solves:** Problem 1 (Invisible AI Operations)
- **Validates:** A1 (visualization beats documentation)
- **Depends on:** None (entry point)

## Priority: P0
## Estimate: M

## Wireframe Concept

```
+------------------------------------------------------------------+
|  LeanOS                                    [BOOTSTRAP] mode       |
+------------------------------------------------------------------+
|                                                                    |
|  +------------+  +------------+  +------------+  +------------+   |
|  | GOALS      |  | CANVAS     |  | THREADS    |  | SKILLS     |   |
|  |   0        |  |  0/15      |  |   6        |  |   70       |   |
|  |  active    |  | populated  |  |  active    |  | available  |   |
|  +------------+  +------------+  +------------+  +------------+   |
|                                                                    |
|  +-----------------------------+  +----------------------------+  |
|  |  Canvas Health              |  |  Recent Activity           |  |
|  |  [visual 15-section grid]   |  |  - Thread X completed      |  |
|  |                             |  |  - Skill Y invoked         |  |
|  |  [###...............] 20%   |  |  - Goal Z created          |  |
|  +-----------------------------+  +----------------------------+  |
|                                                                    |
|  +-----------------------------+  +----------------------------+  |
|  |  Active Threads             |  |  Quick Reference           |  |
|  |  - sales/example (done)     |  |  - 13 Agents               |  |
|  |  - marketing/campaigns      |  |  - 70 Skills               |  |
|  |  - operations/archive       |  |  - 6 Reasoning Modes       |  |
|  +-----------------------------+  +----------------------------+  |
|                                                                    |
+------------------------------------------------------------------+
```

## Data Requirements

From `leanos.json`:
- `goals.length` - active goal count
- `canvas.health` - percentage populated
- `canvas.mode` - VENTURE/BOOTSTRAP
- `threads.length` - total threads
- `threads.filter(active)` - active threads
- `skills.length` - total skills
- `agents.length` - total agents
