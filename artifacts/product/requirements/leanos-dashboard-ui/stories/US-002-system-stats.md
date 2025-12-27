# US-002: System Stats

## Story

As a **startup founder using LeanOS**,
I want to **see key system statistics displayed as visual cards**,
so that **I can quickly assess the operational state of my AI-operated business**.

## Acceptance Criteria

- [ ] GIVEN the dashboard loads, WHEN I view stats cards, THEN I see a "Goals" card showing count of active goals
- [ ] GIVEN the dashboard loads, WHEN I view stats cards, THEN I see a "Canvas Health" card showing X/15 sections populated with a progress indicator
- [ ] GIVEN the dashboard loads, WHEN I view stats cards, THEN I see a "Threads" card showing active/total thread counts by type
- [ ] GIVEN the dashboard loads, WHEN I view stats cards, THEN I see a "Skills" card showing total available skills (70) grouped by category
- [ ] GIVEN a stat card, WHEN I click on it, THEN I navigate to the detailed view for that entity type
- [ ] GIVEN the canvas health is low (<50%), WHEN I view the card, THEN it shows a warning indicator suggesting Canvas setup

## Links

- **Solves:** Problem 1 (Invisible AI Operations), Problem 2 (System Comprehension)
- **Validates:** A1 (visualization beats documentation)
- **Depends on:** US-001 (part of dashboard)

## Priority: P0
## Estimate: S

## Stat Card Designs

### Goals Card
```
+------------------+
|  [icon] GOALS    |
|                  |
|     0            |
|   active         |
|                  |
| [View Goals ->]  |
+------------------+
```

### Canvas Health Card
```
+------------------+
|  [icon] CANVAS   |
|                  |
|   0 / 15         |
|  populated       |
|  [=====-----] 0% |
| [View Canvas ->] |
+------------------+
```

### Threads Card
```
+------------------+
|  [icon] THREADS  |
|                  |
|     6            |
|   total          |
|  2 completed     |
| [View Threads ->]|
+------------------+
```

### Skills Card
```
+------------------+
|  [icon] SKILLS   |
|                  |
|    70            |
|  skills          |
|  13 agents       |
| [View Skills ->] |
+------------------+
```

## Data Requirements

From `leanos.json`:
- `goals.length`
- `canvas.health` (0-100)
- `canvas.sections.filter(s => s.status !== 'missing').length`
- `threads.length`
- `threads.filter(t => t.currentStage === 6).length` (completed)
- `skills.length`
- `agents.length`
