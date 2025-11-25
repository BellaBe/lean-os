
Phase 2 & 3: Skeleton Specification
Phase 2: Inverse Transformations & Effect System (2 weeks)
New Sub-Skills: 3
1.10 effect-system-analyzer (system-architect)
Input: Type signatures from specifications
Output: effects.yaml
Purpose: Make side effects explicit (IO, Error, State)
Why: Prevent hidden IO in "pure" functions
1.11 spec-to-requirements-extractor (system-architect)
Input: specifications/v{X}/
Output: requirements-reconstructed.md
Purpose: Verify specs satisfy original requirements (inverse direction)
Why: Validate roundtrip correctness
2.5 code-to-spec-analyzer (backend-prover)
Input: Existing Python codebase
Output: specifications-inferred/v{X}/
Purpose: Import legacy systems into LeanOS
Why: Analyze existing code, competitive analysis

Phase 3: Behavioral Equivalence & Optimization (1.5 weeks)
New Sub-Skills: 2
4.5 contract-test-generator (frontend-prover)
Input: api.openapi.json
Output: Property-based tests
Purpose: Verify behavioral correctness (not just types)
Why: Ensure pagination/errors/auth actually work correctly
system-optimizer enhancement (1.6)
New capability: Coproduct optimization
Input: Platform = Shopify + WooCommerce + BigCommerce
Output: Unified interface + adapters
Purpose: Reduce code duplication for sum types
Why: 60% code reduction, shared implementation

Build Pipeline Additions
bash# Phase 2
15-verify-effect-system.sh           # Effects explicit?
16-validate-requirements-equivalence.sh  # Specs = Requirements?
17-analyze-existing-code.sh          # Optional: import legacy
18-verify-inferred-specs.sh          # Optional: validate import

# Phase 3
19-generate-contract-tests.sh        # Generate behavioral tests
20-run-contract-tests.sh             # Run 10K property tests
21-verify-coproduct-optimization.sh  # Verify optimizations
22-final-verification.sh             # All phases complete?

Timeline
Phase 2: 2 weeks (3 sub-skills)
Phase 3: 1.5 weeks (2 sub-skills)
Total: 3.5 weeks