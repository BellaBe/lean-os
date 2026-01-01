---
name: product-handoff
description: Create engineering handoff with scope, acceptance criteria, and examples. Use when handing features to engineering, defining boundaries, documenting test cases, or creating definition of done.
allowed-tools: Read, Grep, Glob
---

# Product Handoff

Create complete engineering contract: scope, criteria, examples, verification.

## Purpose

Single document that gives engineering everything needed to build. Defines WHAT and HOW TO VERIFY, not HOW TO BUILD.

## When to Apply

- Handing off prioritized features to engineering
- Defining scope boundaries
- Documenting acceptance criteria
- Creating examples for AI/human engineers

## Boundaries

### This Skill Produces
- `handoff.md` — Complete engineering contract

### This Skill Does NOT Produce
- API designs → Engineering
- Data models → Engineering
- Code → Engineering

### Handoff Points
- Receives from: product-requirements (stories), product-design-flows, product-design-wireframes, product-prioritization
- Provides to: FE/BE engineering skills

## Process

### Step 1: Context

Pull from stories and design artifacts.

```markdown
# Handoff: {Feature Name}

## Context

### Problem
[What user problem, from story]

### Users
[Who experiences this, from segments]

### References
- Story: [link to US-NNN]
- Flows: [link to flow]
- Wireframes: [link to wireframe]
```

### Step 2: Scope

Explicit boundaries. AI will gold-plate without these.

```markdown
## Scope

### In Scope
- [Capability to build]
- [Capability to build]

### Out of Scope
- [Don't build] — Why: [prevents scope creep]
- [Don't build] — Why: [future version]

### Constraints
- [Technical constraint]
- [Business constraint]
- [Performance target]

### Dependencies
- [Must exist first]
- [External service needed]

### Risks
| Risk | Mitigation |
|------|------------|
| [Unknown] | [Approach] |
```

### Step 3: Acceptance Criteria

Testable, behavioral, pass/fail.

```markdown
## Acceptance Criteria

### Core
- [ ] GIVEN [context], WHEN [action], THEN [result]
- [ ] GIVEN [context], WHEN [action], THEN [result]

### Edge Cases
- [ ] GIVEN [empty state], WHEN [action], THEN [appropriate response]
- [ ] GIVEN [max limit], WHEN [exceeded], THEN [constraint message]

### Errors
- [ ] GIVEN [error condition], WHEN [failure], THEN [recovery path]
```

### Step 4: Examples

Show, don't just tell. Critical for AI engineers.

```markdown
## Examples

### Happy Path
**Input:**
- User: logged in, has items in cart
- Action: clicks "Checkout"

**Output:**
- Navigates to checkout page
- Cart items displayed with totals
- Payment form shown

### Edge Case: Empty Cart
**Input:**
- User: logged in, cart empty
- Action: clicks "Checkout"

**Output:**
- Stays on cart page
- Message: "Add items to checkout"
- CTA: "Continue Shopping"

### Error Case: Payment Fails
**Input:**
- User: completes form
- Action: submits payment
- Condition: payment provider returns error

**Output:**
- Error message: "Payment failed. Please try again."
- Form preserved (not cleared)
- Retry button available
```

### Step 5: Test Cases

Specific scenarios to verify.

```markdown
## Test Cases

### Functional
- [ ] User can complete checkout with valid card
- [ ] User sees error with invalid card
- [ ] Cart total matches sum of items

### Edge Cases
- [ ] Single item checkout works
- [ ] Max items (100) checkout works
- [ ] Zero-value items handled

### Error Handling
- [ ] Network timeout shows retry option
- [ ] Invalid promo code shows error
- [ ] Session expiry redirects to login
```

### Step 6: Quality Bar

Non-functional requirements.

```markdown
## Quality Bar

### Performance
- Page load: < 2s
- Action response: < 200ms

### Accessibility
- Keyboard navigable
- Screen reader compatible
- Color contrast AA

### Error Handling
- All errors have user-friendly messages
- No raw error codes shown
- Retry available where appropriate
```

### Step 7: Definition of Done

```markdown
## Definition of Done

- [ ] All acceptance criteria pass
- [ ] All examples produce expected output
- [ ] Test cases covered
- [ ] Quality bar met
- [ ] No critical/high bugs
- [ ] Code reviewed
- [ ] Product approved
```

## Output

This skill produces: `handoff.md`

Agent handles placement in `artifacts/{product}/features/{slug}/v{N}/`

## Error Handling

### Missing Design Artifacts
```
Action: "Missing [flows/wireframes] for '[X]'.
        Run product-design-flows/wireframes first or mark as 'engineer discretion'."
```

### Vague Criteria
```
Action: "Criterion '[X]' not testable.
        
        Bad: 'Search works correctly'
        Good: 'GIVEN search term, WHEN submitted, THEN results contain term'
        
        Rewrite with GIVEN/WHEN/THEN."
```

### Missing Examples
```
Action: "No examples provided.
        Add at minimum:
        - Happy path example
        - One edge case
        - One error case"
```

### Scope Creep
```
Action: "Handoff includes '[X]' not in story.
        Options:
        1. Remove from handoff
        2. Add to story first
        3. Move to Out of Scope"
```

## References

For patterns and examples, see:
- `references/handoff-examples.md` — Complete handoff examples
- `references/criteria-patterns.md` — Writing testable criteria