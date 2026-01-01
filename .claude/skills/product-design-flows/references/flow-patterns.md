# Flow Patterns Reference

## Common Flow Structures

### Linear Flow
```
[Start] → [Step 1] → [Step 2] → [Success]
```
Use for: Onboarding, checkout, wizards

### Branching Flow
```
[Start] → [Decision] ─→ [Path A] → [End]
              │
              └─→ [Path B] → [End]
```
Use for: Conditional logic, user choices

### Loop Flow
```
[Start] → [Action] → [Review] ─→ [Done]
              ↑          │
              └──────────┘
```
Use for: Editing, iterative tasks

### Hub-and-Spoke
```
         ┌→ [Feature A] → ┐
[Hub] ───┼→ [Feature B] → ┼→ [Hub]
         └→ [Feature C] → ┘
```
Use for: Dashboards, main menus

## Error Flow Patterns

### Inline Recovery
```
[Action] → [Error] → [Fix inline] → [Retry]
```
Best for: Form validation, minor errors

### Redirect Recovery
```
[Action] → [Error] → [Error page] → [Start over]
```
Best for: System failures, auth errors

### Graceful Degradation
```
[Action] → [Partial failure] → [Cached/fallback] → [Continue]
```
Best for: Network issues, optional features