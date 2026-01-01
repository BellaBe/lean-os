# Handoff Examples Reference

## Complete Handoff Example

```markdown
# Handoff: Product Search

## Context

### Problem
Users can't find products, leading to abandonment. #1 support complaint.

### Users
Shoppers looking for specific products.

### References
- Story: US-015
- Flow: product-search-flow.md
- Wireframe: search-results.md

## Scope

### In Scope
- Keyword search in title and description
- Filter by category, price range
- Sort by relevance, price, date

### Out of Scope
- Fuzzy matching — Why: V2 after baseline
- Voice search — Why: Separate initiative
- Image search — Why: Different tech stack

### Constraints
- Results < 500ms
- Max 10,000 products indexed
- Works offline (cached results)

### Dependencies
- Product catalog API
- Search index (Elasticsearch)

### Risks
| Risk | Mitigation |
|------|------------|
| Slow with large catalog | Pagination, lazy load |
| Poor relevance | Tune ranking, gather feedback |

## Acceptance Criteria

### Core
- [ ] GIVEN search page, WHEN I type "shoes" and submit, THEN results show products with "shoes" in title/description
- [ ] GIVEN results, WHEN I select category "Running", THEN only running shoes show
- [ ] GIVEN results, WHEN I set price $50-$100, THEN only products in range show

### Edge Cases
- [ ] GIVEN no matching products, WHEN search submitted, THEN show "No results" with suggestions
- [ ] GIVEN special characters in query, WHEN submitted, THEN handled gracefully (escaped, not error)

### Errors
- [ ] GIVEN network failure, WHEN searching, THEN show cached results + "Results may be outdated"
- [ ] GIVEN timeout, WHEN searching, THEN show retry button

## Examples

### Happy Path
**Input:**
- Query: "running shoes"
- Filters: Category = Footwear, Price < $150

**Output:**
- 24 products displayed
- All contain "running" or "shoes"
- All under $150
- Sorted by relevance

### Edge Case: No Results
**Input:**
- Query: "xyzabc123"

**Output:**
- "No products found for 'xyzabc123'"
- Suggestions: "Try: shoes, shirts, pants"
- Recent searches shown

### Error Case: Network Failure
**Input:**
- Query: "shoes"
- Condition: Network offline

**Output:**
- Cached results shown (if available)
- Banner: "You're offline. Showing saved results."
- "Retry" button when network returns

## Test Cases

### Functional
- [ ] Search returns relevant products
- [ ] Filters narrow results correctly
- [ ] Sort orders applied correctly
- [ ] Pagination works (next/prev)

### Edge Cases
- [ ] Empty query shows browse mode
- [ ] Single character query works
- [ ] Very long query (500 chars) handled

### Error Handling
- [ ] Malformed API response handled
- [ ] Timeout shows retry
- [ ] 500 error shows friendly message

## Quality Bar

### Performance
- First results: < 500ms
- Filter application: < 200ms
- Perceived instant (skeleton loading)

### Accessibility
- Search input has label
- Results announced to screen reader
- Filter controls keyboard accessible

## Definition of Done

- [ ] All acceptance criteria pass
- [ ] All examples produce expected output
- [ ] Test cases covered
- [ ] Performance targets met
- [ ] Accessibility audit passed
- [ ] Product approved
```