# Proof Techniques in Category Theory

This guide explains practical proof techniques for verifying categorical properties in system design.

## Equational Reasoning

The primary proof technique in functional programming and category theory.

### Principle

Functions are defined as equations. Left side = Right side. You can substitute one for the other.

### Technique

1. Start with what you want to prove
2. Apply definitions (substitute equals for equals)
3. Simplify using known equations
4. Arrive at the desired result

### Example: Proving Functor Identity for Maybe

**Claim:** `fmap id = id` for Maybe functor

**Proof:**

Case 1: Nothing
```
  fmap id Nothing
= Nothing                    -- by definition of fmap
= id Nothing                 -- by definition of id
```

Case 2: Just x
```
  fmap id (Just x)
= Just (id x)                -- by definition of fmap
= Just x                     -- by definition of id
= id (Just x)                -- by definition of id
```

Both cases hold, therefore `fmap id = id`. ∎

See full proofs.md for complete proof techniques including:
- Pattern matching proofs
- Diagram chasing
- Universal property proofs
- Parametricity arguments
- Induction proofs
- Type-driven proofs
