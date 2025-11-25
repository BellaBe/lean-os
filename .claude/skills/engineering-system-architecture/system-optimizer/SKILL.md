---
name: system-optimizer
description: Apply algebraic laws to optimize system architecture. Uses distributivity for service specialization, product decomposition for parallel execution, and common subexpression factoring. All optimizations are semantics-preserving and verified.
allowed-tools: Read, Write, Bash
version: 1.0.0
---

# System Optimizer

## Purpose

Apply algebraic laws (distributivity, factoring, decomposition) to transform system architectures for better performance, parallelization, and resource usage while preserving semantics.

## Input

```
artifacts/engineering/specifications/v{VERSION}/types.curry-howard
artifacts/engineering/specifications/v{VERSION}/architecture.categorical
```

## Output

```
Updated: artifacts/engineering/specifications/v{VERSION}/architecture.categorical (optimized)
```

## Optimization Laws

### Law 1: Distributivity (Service Specialization)

**Rule:** `a × (b + c) = (a × b) + (a × c)`

**Use Case:** Split monolithic service into specialized services

**Example:**
```
Before: Auth × ({Platform} + {AltPlatform} + Stripe)
After: (Auth × {Platform}) + (Auth × {AltPlatform}) + (Auth × Stripe)

Benefit:
- 3 specialized microservices
- Each has only needed dependencies
- Independent scaling per platform
```

### Law 2: Product Decomposition (Parallel Execution)

**Rule:** `(a × b)^c = a^c × b^c`

**Use Case:** Transform sequential operations into parallel

**Example:**
```
Before: Request → (ProductInfo × StockLevel × Reviews)
After: (Request → ProductInfo) × (Request → StockLevel) × (Request → Reviews)

Benefit:
- All queries execute in parallel
- Latency: max(t1, t2, t3) instead of t1 + t2 + t3
- 2-3x speedup typical
```

### Law 3: Common Subexpression Factoring

**Rule:** `(a × b) + (a × c) = a × (b + c)`

**Use Case:** Reuse common components

**Example:**
```
12 implementations: Tenant × Env × Version × Platform
Factor: Tenant handler (reused 12 times)

Reduction: 12 implementations → 5 components
- 1 tenant handler
- 3 environment handlers
- 2 version handlers
- 2 platform adapters
```

## Execution Steps

### Step 1: Analyze Composition Graph

```bash
python {baseDir}/scripts/analyze_composition.py \
  --types artifacts/engineering/specifications/v{VERSION}/types.curry-howard \
  --functors artifacts/engineering/specifications/v{VERSION}/architecture.categorical \
  --output /tmp/composition-graph.json
```

### Step 2: Identify Optimization Opportunities

```bash
python {baseDir}/scripts/identify_optimizations.py \
  --graph /tmp/composition-graph.json \
  --strategies distributivity,product_decomposition,factoring \
  --output /tmp/optimization-plan.json
```

### Step 3: Apply Optimizations

```bash
python {baseDir}/scripts/apply_optimizations.py \
  --plan /tmp/optimization-plan.json \
  --functors artifacts/engineering/specifications/v{VERSION}/architecture.categorical \
  --output artifacts/engineering/specifications/v{VERSION}/architecture.categorical
```

### Step 4: Verify Semantics Preservation

```bash
python {baseDir}/scripts/verify_optimization.py \
  --before /tmp/composition-graph.json \
  --after artifacts/engineering/specifications/v{VERSION}/architecture.categorical \
  --output artifacts/engineering/proofs/architecture/optimization/verification.json
```

## Optimization Example: Catalog Service

### Before Optimization
```yaml
expression: Tenant × (Dev + Staging + Prod) × (V1 + V2) × ({Platform} + {AltPlatform})
paths: 12

implementations:
  - tenant_dev_v1_{platform}
  - tenant_dev_v1_woo
  - tenant_dev_v2_{platform}
  - tenant_dev_v2_woo
  - tenant_staging_v1_{platform}
  - tenant_staging_v1_woo
  - tenant_staging_v2_{platform}
  - tenant_staging_v2_woo
  - tenant_prod_v1_{platform}
  - tenant_prod_v1_woo
  - tenant_prod_v2_{platform}
  - tenant_prod_v2_woo

total_components: 12
code_size: ~1200 LOC
```

### After Optimization
```yaml
# Apply distributivity to factor common terms
optimized_expression: Tenant × ((Dev + Staging + Prod) × (V1 + V2) × ({Platform} + {AltPlatform}))

# Factor: Tenant handler (reused)
# Specialize: Environment, Version, Platform

components:
  tenant_handler:
    reused: 12 times
    code: ~100 LOC
  
  environment_handlers:
    - dev_handler (50 LOC)
    - staging_handler (50 LOC)
    - prod_handler (50 LOC)
  
  version_handlers:
    - v1_handler (80 LOC)
    - v2_handler (80 LOC)
  
  platform_adapters:
    - {platform}_adapter (120 LOC)
    - {altplatform}_adapter (120 LOC)

total_components: 8
code_size: ~650 LOC
reduction: 46% (1200 → 650 LOC)

composition:
  tenant_handler(
    environment_handler(
      version_handler(
        platform_adapter(request)
      )
    )
  )
```

### Optimization Verification
```json
{
  "optimization": "distributivity + factoring",
  "semantics_preserved": true,
  "verification_method": "property_testing",
  "test_cases": 10000,
  "all_passed": true,
  
  "before_after_equivalence": {
    "for_all_inputs": "output_before(input) == output_after(input)",
    "verified": true
  },
  
  "performance_impact": {
    "code_reduction": "46%",
    "deployment_size": "650 LOC vs 1200 LOC",
    "reusability": "8 components vs 12 implementations"
  }
}
```

## Output Format

```yaml
# Appended to artifacts/engineering/specifications/v{VERSION}/architecture.categorical

optimization_strategy:
  applied_laws:
    - law: distributivity
      expression: "Auth × ({Platform} + {AltPlatform})"
      result: "(Auth × {Platform}) + (Auth × {AltPlatform})"
      benefit: "Service specialization: 2 independent microservices"
    
    - law: product_decomposition
      expression: "Request → (Info × Stock × Reviews)"
      result: "(Request → Info) × (Request → Stock) × (Request → Reviews)"
      benefit: "Parallel execution: 2.2x speedup"
    
    - law: common_subexpression_factoring
      expression: "Tenant × Env × Version × Platform (12 paths)"
      result: "Tenant × ((Env + Staging + Prod) × (V1 + V2) × (Platform))"
      benefit: "Component reuse: 12 → 8 components (33% reduction)"

  performance_improvements:
    code_reduction: "46%"
    parallel_execution: "2.2x speedup"
    deployment_size: "650 LOC vs 1200 LOC"
    reusability: "Tenant handler reused 12 times"

  verification:
    semantics_preserved: true
    property_tests_passed: 10000
    equivalence_verified: true
```

## Success Criteria

1. ✅ All optimization laws applied
2. ✅ Semantics preserved (10000/10000 tests)
3. ✅ Performance improvements documented
4. ✅ Code reduction measured
5. ✅ Verification proofs generated

## Next Steps

- Pass to **architecture-validator** for final validation
- Use optimized architecture in **backend-prover**