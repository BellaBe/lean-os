# US-008: Skill Catalog

## Status: COMPLETE (2024-12-27)

## Story

As a **startup founder exploring LeanOS**,
I want to **browse all 70 skills organized by category with their purposes**,
so that **I understand the full capability of the autonomous operating system**.

## Acceptance Criteria

- [x] GIVEN I navigate to Skills, WHEN the page loads, THEN I see all skills grouped by category
- [x] GIVEN the skill list, WHEN I view categories, THEN I see category filter pills with counts
- [x] GIVEN a category, WHEN I click it, THEN I see only skills in that category
- [x] GIVEN a skill, WHEN I view it, THEN I see: name, category prefix, and purpose (truncated to 1-2 lines)
- [x] GIVEN the skill list, WHEN I want to search, THEN I can filter skills by name or purpose text
- [ ] GIVEN a skill in the list, WHEN I click it, THEN I navigate to skill detail (US-009) - DEFERRED
- [x] GIVEN the page header, WHEN I view it, THEN I see total skill count and category count

## Implementation

**File:** `src/app/skills/page.tsx`

**Features delivered:**
- Header with skill count and category count
- Search input with icon for filtering
- Category filter pills (All + each category with count)
- Skills grouped by category with section headers
- Skill cards with icon, name, and truncated purpose
- Empty state for no search results

## Links

- **Solves:** Problem 2 (System Comprehension)
- **Validates:** A3 (showcase UI drives adoption)
- **Depends on:** None

## Priority: P0
## Estimate: M

## Wireframe Concept

```
+------------------------------------------------------------------+
|  Skills & Agents                              [Search skills...]  |
|  70 skills | 13 agents                                            |
+------------------------------------------------------------------+
|                                                                    |
|  +----------------------+  +-----------------------------------+  |
|  | CATEGORIES           |  | SKILLS                            |  |
|  +----------------------+  +-----------------------------------+  |
|  | [>] action (11)      |  |                                   |  |
|  | [>] engineering (20) |  | ENGINEERING (20 skills)           |  |
|  | [>] foundations (10) |  | --------------------------------- |  |
|  | [>] goal (2)         |  | engineering-spec-objects          |  |
|  | [v] marketing (5)    |  |   Extract type definitions from   |  |
|  | [>] product (5)      |  |   requirements...                 |  |
|  | [>] reasoning (6)    |  |                                   |  |
|  | [>] research (5)     |  | engineering-spec-morphisms        |  |
|  | [>] sales (6)        |  |   Extract operations as           |  |
|  +----------------------+  |   categorical morphisms...        |  |
|                            |                                   |  |
|  +----------------------+  | engineering-build-category        |  |
|  | AGENTS (13)          |  |   Formalize domain as a           |  |
|  +----------------------+  |   category...                     |  |
|  | lean-os              |  |                                   |  |
|  | lean-os-spec         |  | [... more skills ...]             |  |
|  | lean-os-build        |  |                                   |  |
|  | foundations-builder  |  +-----------------------------------+  |
|  | sales-execution      |                                        |
|  | marketing-execution  |                                        |
|  | [... more agents]    |                                        |
|  +----------------------+                                        |
|                                                                    |
+------------------------------------------------------------------+
```

## Category Summaries

| Category | Count | Purpose |
|----------|-------|---------|
| action | 11 | Deliverable contracts - prescriptive, diagnostic, evaluative, etc. |
| engineering | 20 | SPEC -> BUILD -> VERIFY -> GEN pipeline for verified code |
| foundations | 10 | Canvas setup, ICP, business model, go-to-market |
| goal | 2 | Goal setting and tracking |
| marketing | 5 | Content strategy, generation, delivery, optimization |
| product | 5 | Requirements, flows, wireframes, prioritization, specification |
| reasoning | 6 | Causal, abductive, inductive, analogical, dialectical, counterfactual |
| research | 5 | Market research (venture/bootstrap), source processing, playbooks |
| sales | 6 | Prospecting, contacts, materials, outreach, qualification |

## Data Requirements

From `leanos.json`:
- `skills[]` - all skills with:
  - `name` - skill name (e.g., "engineering-spec-objects")
  - `category` - extracted from name prefix (e.g., "engineering")
  - `purpose` - skill description
  - `whenToUse` - usage guidance (may be empty)
  - `location` - file path
- `agents[]` - all agents with:
  - `name` - agent name
  - `purpose` - agent description
  - `skills` - skills it orchestrates
  - `location` - file path
