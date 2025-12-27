# US-016: Canvas Overview

## Status: COMPLETE (2024-12-27)

## Story

As a **startup founder using LeanOS**,
I want to **see all 15 Canvas sections visualized as a grid showing their status**,
so that **I can understand my strategic coverage and identify gaps in my business foundation**.

## Acceptance Criteria

- [x] GIVEN I navigate to Canvas, WHEN the page loads, THEN I see a 3x5 or similar grid showing all 15 Canvas sections
- [x] GIVEN a Canvas section is populated, WHEN I view the grid, THEN that cell shows a "populated" status with green indicator
- [x] GIVEN a Canvas section is empty/missing, WHEN I view the grid, THEN that cell shows "missing" status with gray indicator
- [x] GIVEN the grid is displayed, WHEN I view section names, THEN I see both the number and name (e.g., "01", "Context")
- [x] GIVEN the grid is displayed, WHEN I see the header, THEN I see overall health percentage (X% populated)
- [ ] GIVEN a section cell, WHEN I click it, THEN I navigate to the section detail view (US-017) - DEFERRED
- [x] GIVEN the Canvas is empty (0%), WHEN I view the page, THEN I see a status legend and section details
- [x] GIVEN the mode indicator, WHEN I view it, THEN I see the current business mode in sidebar (VENTURE/BOOTSTRAP)

## Implementation

**File:** `src/app/canvas/page.tsx`

**Components used:**
- `CanvasGrid` - 15-section grid with status indicators

**Features delivered:**
- Health overview card with progress bar and percentage
- 3x5 grid with section status icons (CheckCircle, AlertCircle, Circle)
- Legend showing complete/draft/missing status
- Section details list with status and summaries

## Links

- **Solves:** Problem 2 (System Comprehension)
- **Validates:** A1 (visualization beats documentation)
- **Depends on:** None

## Priority: P0
## Estimate: M

## Wireframe Concept

```
+------------------------------------------------------------------+
|  Canvas Health                                    [BOOTSTRAP]     |
|  [========------------] 0% populated (0/15 sections)              |
+------------------------------------------------------------------+
|                                                                    |
|  +------------------+  +------------------+  +------------------+  |
|  | 01 Context       |  | 02 Constraints   |  | 03 Opportunity   |  |
|  | [ ] missing      |  | [ ] missing      |  | [ ] missing      |  |
|  +------------------+  +------------------+  +------------------+  |
|                                                                    |
|  +------------------+  +------------------+  +------------------+  |
|  | 04 Segments      |  | 05 Problem       |  | 06 Competitive   |  |
|  | [ ] missing      |  | [ ] missing      |  | [ ] missing      |  |
|  +------------------+  +------------------+  +------------------+  |
|                                                                    |
|  +------------------+  +------------------+  +------------------+  |
|  | 07 UVP           |  | 08 Advantage     |  | 09 Solution      |  |
|  | [ ] missing      |  | [ ] missing      |  | [ ] missing      |  |
|  +------------------+  +------------------+  +------------------+  |
|                                                                    |
|  +------------------+  +------------------+  +------------------+  |
|  | 10 Assumptions   |  | 11 Pricing       |  | 12 Costs         |  |
|  | [ ] missing      |  | [ ] missing      |  | [ ] missing      |  |
|  +------------------+  +------------------+  +------------------+  |
|                                                                    |
|  +------------------+  +------------------+  +------------------+  |
|  | 13 Metrics       |  | 14 Growth        |  | 15 Go-to-Market  |  |
|  | [ ] missing      |  | [ ] missing      |  | [ ] missing      |  |
|  +------------------+  +------------------+  +------------------+  |
|                                                                    |
+------------------------------------------------------------------+
|  Canvas is your strategic foundation.                              |
|  [ Run Canvas Setup ] to populate sections with AI assistance.    |
+------------------------------------------------------------------+
```

## Canvas Section Groups (Visual Hint)

Could color-code by theme:
- **Foundation** (01-03): Context, Constraints, Opportunity
- **Customer** (04-06): Segments, Problem, Competitive
- **Value** (07-09): UVP, Advantage, Solution
- **Validation** (10-12): Assumptions, Pricing, Costs
- **Growth** (13-15): Metrics, Growth, Go-to-Market

## Data Requirements

From `leanos.json`:
- `canvas.mode` - BOOTSTRAP/VENTURE
- `canvas.health` - percentage (0-100)
- `canvas.sections[]` - all 15 sections with:
  - `number` - "01" through "15"
  - `name` - section name
  - `slug` - file identifier
  - `status` - "populated" | "missing"
  - `content` - markdown content (for preview)
