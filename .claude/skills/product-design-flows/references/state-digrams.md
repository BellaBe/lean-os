# State Diagrams Reference

## State Diagram Patterns

### Simple States
```
[Empty] → [Loading] → [Loaded]
                  ↘→ [Error]
```

### CRUD Entity
```
[Draft] → [Active] → [Archived]
   ↑          │
   └──────────┘ (reactivate)
```

### Auth States
```
[Anonymous] → [Authenticating] → [Authenticated]
                     ↓
               [Failed] → [Anonymous]
```

## Avoid These

### Missing Error Paths
```
❌ [Submit] → [Success]

✓ [Submit] → [Success]
        ↘→ [Validation Error]
        ↘→ [Network Error]
        ↘→ [Server Error]
```

### Assuming Linear Users
```
❌ Users always go A → B → C

✓ Users may:
  - Jump: A → C
  - Back: B → A
  - Abandon: B → Exit
```

### Forgetting Empty States
```
❌ [List Page] shows items

✓ [List Page] → [Has items] → show list
             → [Empty] → show CTA
             → [Loading] → show skeleton
             → [Error] → show retry
```