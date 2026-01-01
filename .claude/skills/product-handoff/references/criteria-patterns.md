# Acceptance Criteria Writing Patterns

## Criteria Writing Patterns

### Good Criteria
```markdown
- [ ] GIVEN user on checkout, WHEN they click "Pay", THEN order is created AND confirmation shown
```

### Bad Criteria
```markdown
❌ - [ ] Checkout works
❌ - [ ] Payment is processed correctly
❌ - [ ] User experience is good
```

### Pattern: GIVEN-WHEN-THEN
```
GIVEN [precondition/state]
WHEN [action taken]  
THEN [observable result]
```

### Multiple Outcomes
```markdown
- [ ] GIVEN valid card, WHEN submitted, THEN order created AND email sent AND confirmation shown
```

### Negative Cases
```markdown
- [ ] GIVEN invalid card, WHEN submitted, THEN error shown AND form preserved AND no order created
```