# US-019: Active Threads

## Status: COMPLETE (2024-12-27)

## Story

As a **startup founder using LeanOS**,
I want to **see all active threads with their current execution stage**,
so that **I can understand what the AI is working on and track decision progress**.

## Acceptance Criteria

- [x] GIVEN I navigate to Threads, WHEN the page loads, THEN I see a list of all threads
- [x] GIVEN a thread is displayed, WHEN I view it, THEN I see the thread name, type, and current stage (X/6)
- [x] GIVEN a thread, WHEN I view its progress, THEN I see a 6-step progress indicator showing completed vs pending stages
- [x] GIVEN a thread at stage 6, WHEN I view it, THEN it shows as "completed" with a success indicator
- [x] GIVEN a thread at stage 1-5, WHEN I view it, THEN it shows as "in progress" with current stage highlighted
- [ ] GIVEN the thread list, WHEN I click a thread, THEN I navigate to thread detail (US-013) - DEFERRED
- [x] GIVEN the thread list, WHEN I view it, THEN I can filter by type (sales/marketing/operations/all)
- [ ] GIVEN the thread has a goal_id, WHEN I view it, THEN I see the linked goal indicated - DEFERRED

## Implementation

**File:** `src/app/threads/page.tsx`

**Components used:**
- `ThreadCard` - Thread card with 6-stage progress
- `ThreadProgress` - Visual 6-stage progress indicator

**Features delivered:**
- Stats cards (total, in progress, completed)
- Filter pills by thread type
- 6-stage causal flow legend
- Thread cards with progress visualization
- Empty state for no threads

## Links

- **Solves:** Problem 1 (Invisible AI Operations), Problem 3 (Trust in Autonomous Operations)
- **Validates:** A2 (seeing decisions builds trust)
- **Depends on:** None

## Priority: P0
## Estimate: M

## Wireframe Concept

```
+------------------------------------------------------------------+
|  Threads                                         [Filter: All v]  |
|  6 total | 2 completed | 4 in progress                           |
+------------------------------------------------------------------+
|                                                                    |
|  SALES (2)                                                        |
|  +--------------------------------------------------------------+  |
|  | example                                    [completed]        |  |
|  | [1] [2] [3] [4] [5] [6]  <-- all green                       |  |
|  | Input -> Hypothesis -> Implication -> Decision -> Actions    |  |
|  +--------------------------------------------------------------+  |
|  | campaigns                                  [stage 1]          |  |
|  | [1] [ ] [ ] [ ] [ ] [ ]  <-- 1 green, rest gray              |  |
|  | Input (pending)                                               |  |
|  +--------------------------------------------------------------+  |
|                                                                    |
|  MARKETING (2)                                                    |
|  +--------------------------------------------------------------+  |
|  | example                                    [completed]        |  |
|  | [1] [2] [3] [4] [5] [6]                                      |  |
|  +--------------------------------------------------------------+  |
|  | campaigns                                  [stage 1]          |  |
|  | [1] [ ] [ ] [ ] [ ] [ ]                                      |  |
|  +--------------------------------------------------------------+  |
|                                                                    |
|  OPERATIONS (2)                                                   |
|  +--------------------------------------------------------------+  |
|  | example                                    [completed]        |  |
|  | [1] [2] [3] [4] [5] [6]                                      |  |
|  +--------------------------------------------------------------+  |
|  | archive                                    [stage 1]          |  |
|  | [1] [ ] [ ] [ ] [ ] [ ]                                      |  |
|  +--------------------------------------------------------------+  |
|                                                                    |
+------------------------------------------------------------------+
```

## Stage Labels (for clarity)

| Stage | Name | Description |
|-------|------|-------------|
| 1 | Input | Factual observation captured |
| 2 | Hypothesis | Canvas assumption challenged |
| 3 | Implication | Business impact analyzed |
| 4 | Decision | Commitment with impact score |
| 5 | Actions | Tasks executed |
| 6 | Learning | Outcomes validated, Canvas updated |

## Data Requirements

From `leanos.json`:
- `threads[]` - all threads with:
  - `type` - "sales" | "marketing" | "operations"
  - `name` - thread identifier
  - `path` - file path
  - `currentStage` - 1-6
  - `stages[]` - array of 6 stages with:
    - `number` - 1-6
    - `name` - stage name
    - `status` - "pending" | "completed"
