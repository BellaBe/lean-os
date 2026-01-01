# Story Examples Reference

## Good Stories

### Clear User, Action, Benefit
```markdown
As a shopper,
I want to filter products by price range,
so that I can find items within my budget.
```

### Testable Acceptance Criteria
```markdown
- [ ] GIVEN product list, WHEN I set min=$50 max=$100, THEN only products in range show
- [ ] GIVEN active filter, WHEN I clear it, THEN all products show
- [ ] GIVEN no products in range, WHEN filter applied, THEN empty state with message shows
```

## Bad Stories

### System-Focused (Wrong)
```markdown
❌ As a system,
   I want to store user preferences in the database,
   so that they persist.

✓ As a user,
   I want my preferences saved,
   so that I don't have to set them again.
```

### Implementation-Focused (Wrong)
```markdown
❌ As a user,
   I want a Redux store for cart state,
   so that it's reactive.

✓ As a shopper,
   I want my cart to update immediately when I add items,
   so that I always see accurate totals.
```

### Vague Criteria (Wrong)
```markdown
❌ - [ ] Search works correctly
   - [ ] Results are good

✓ - [ ] GIVEN search term "shoes", WHEN submitted, THEN results contain "shoes" in title or description
   - [ ] GIVEN search results, WHEN displayed, THEN show product image, title, price
```