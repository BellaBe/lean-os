# Acceptance Criteria Patterns

## GIVEN-WHEN-THEN
```
GIVEN [precondition/context]
WHEN [action taken]
THEN [expected result]
```

## Cover These Cases
1. Happy path (normal flow)
2. Edge cases (empty, max, min)
3. Error cases (invalid input, failures)
4. State transitions (before/after)

## Size Guidelines

| Size | Criteria |
|------|----------|
| S | Single UI change, no backend |
| M | Frontend + backend, single flow |
| L | Multiple flows, complex logic |

If L, consider splitting.