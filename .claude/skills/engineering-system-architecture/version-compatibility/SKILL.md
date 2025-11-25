---
name: version-compatibility-prover
description: Prove version migrations are safe by modeling versions as functors and migrations as natural transformations. Verifies backward compatibility OR documents breaking changes. Generates migration/rollback code with correctness proofs.
allowed-tools: Read, Write, Bash
version: 1.0.0
---

# Version Compatibility Prover

## Purpose

Prove API version migrations preserve correctness. Model versions as functors (V1, V2), migrations as natural transformations (α: V1 → V2), and verify compatibility.

## Input

```
artifacts/engineering/specifications/v{VERSION}/versions.yaml (transformations)
artifacts/engineering/specifications/v{VERSION}/types.curry-howard (type proofs)
```

## Output

```
Updated: artifacts/engineering/specifications/v{VERSION}/versions.yaml (with proofs)
artifacts/engineering/proofs/architecture/version-compatibility/
artifacts/engineering/code/migrations/
```

## Compatibility Types

### Type 1: Backward Compatible

**Definition:** All V1 clients work with V2 server

**Proof Obligation:**
```
∀ v1_request. ∃ v2_response. α(v1_request) → v2_response
```

**Example:**
```yaml
v1_to_v2:
  backward_compatible: true
  
  proof: |
    Theorem: All V1 requests can be handled by V2
    
    Proof:
      V1Response = {products: List[Product]}
      V2Response = {products: List[Product], page: int, total_pages: int}
      
      α: V1Response → V2Response
      α(v1) = V2Response(products=v1.products, page=1, total_pages=1)
      
      For all v1: V1Response,
        α(v1) is well-defined and type-correct
      
      ∴ Backward compatible. QED
  
  breaking_changes: []
```

### Type 2: Breaking Changes

**Definition:** Some V1 clients CANNOT work with V2 server

**Proof Obligation:**
```
∃ v1_request. ¬∃ v2_response. α(v1_request) → v2_response
```

**Example:**
```yaml
v1_to_v2:
  backward_compatible: false
  
  breaking_changes:
    - field: user.email
      reason: "Required in V2, optional in V1"
      impact: "Requests without email will be rejected"
    
    - field: response.pagination
      reason: "Added required field in V2"
      impact: "V1 clients cannot parse V2 responses"
  
  migration_required: true
  
  proof: |
    Theorem: V1 clients cannot handle V2 responses
    
    Proof by counterexample:
      V1Response = {products: List[Product]}
      V2Response = {products: List[Product], page: int} (page required)
      
      V1 client expects: {products: [...]}
      V2 server returns: {products: [...], page: 1}
      
      V1 client cannot parse `page` field (not in schema)
      ∴ Breaking change. QED
```

### Type 3: Reversible Migration

**Definition:** Can migrate V1 → V2 → V1 without data loss

**Proof Obligation:**
```
∀ v1. β(α(v1)) = v1  (where β: V2 → V1 is inverse)
```

**Example:**
```yaml
v1_to_v2:
  reversible: true
  
  forward_migration: α
  backward_migration: β
  
  proof: |
    Theorem: Migration is reversible
    
    Proof:
      α: V1 → V2
      β: V2 → V1
      
      For all v1: V1,
        β(α(v1)) = v1 (no data loss)
      
      Example:
        v1 = {products: [p1, p2]}
        α(v1) = {products: [p1, p2], page: 1}
        β(α(v1)) = {products: [p1, p2]} = v1 ✓
      
      ∴ Reversible. QED
```

## Execution Steps

### Step 1: Load Version Definitions

```bash
python {baseDir}/scripts/load_versions.py \
  --versions artifacts/engineering/specifications/v{VERSION}/versions.yaml \
  --output /tmp/version-definitions.json
```

### Step 2: Prove Compatibility

```bash
python {baseDir}/scripts/prove_compatibility.py \
  --versions /tmp/version-definitions.json \
  --types artifacts/engineering/specifications/v{VERSION}/types.curry-howard \
  --output artifacts/engineering/proofs/architecture/version-compatibility/proofs.json
```

### Step 3: Generate Migration Code

```bash
python {baseDir}/scripts/generate_migrations.py \
  --versions /tmp/version-definitions.json \
  --proofs artifacts/engineering/proofs/architecture/version-compatibility/proofs.json \
  --language python \
  --output artifacts/engineering/code/migrations/
```

### Step 4: Generate Rollback Code

```bash
python {baseDir}/scripts/generate_rollbacks.py \
  --versions /tmp/version-definitions.json \
  --proofs artifacts/engineering/proofs/architecture/version-compatibility/proofs.json \
  --language python \
  --output artifacts/engineering/code/migrations/
```

## Output Format

```yaml
# Updated: artifacts/engineering/specifications/v{VERSION}/versions.yaml

api_versions:
  current: v2
  previous: v1
  
  migrations:
    v1_to_v2:
      backward_compatible: true
      reversible: true
      breaking_changes: []
      
      proof: proofs/architecture/version-compatibility/v1-to-v2.proof
      
      migration_function: |
        def migrate_v1_to_v2(v1: V1Response) -> V2Response:
            """
            Proven safe: All V1 responses can be converted to V2
            Reversible: Can convert back without data loss
            """
            return V2Response(
                products=v1.products,
                page=1,
                total_pages=ceil(len(v1.products) / 50),
                has_more=len(v1.products) > 50
            )
      
      rollback_function: |
        def rollback_v2_to_v1(v2: V2Response) -> V1Response:
            """
            Proven safe: No data loss (pagination metadata discarded)
            """
            return V1Response(products=v2.products)
      
      migration_strategy:
        type: "dual-write"
        steps:
          - "Deploy V2 API alongside V1"
          - "Route V1 clients to V1 endpoint"
          - "Route V2 clients to V2 endpoint"
          - "Monitor for errors"
          - "Migrate clients incrementally"
          - "Deprecate V1 after 6 months"
```

## Generated Migration Code

```python
# artifacts/engineering/code/migrations/v1_to_v2.py

from dataclasses import dataclass
from typing import List
from math import ceil

@dataclass
class V1Response:
    products: List[Product]

@dataclass
class V2Response:
    products: List[Product]
    page: int
    total_pages: int
    has_more: bool

def migrate_v1_to_v2(
    v1: V1Response,
    page_size: int = 50
) -> V2Response:
    """
    Natural transformation: V1Response → V2Response
    
    Proven properties:
    - Backward compatible: All V1 responses can be converted
    - Reversible: Can rollback without data loss
    - Total function: Defined for all inputs
    
    Proof: proofs/architecture/version-compatibility/v1-to-v2.proof
    """
    products = v1.products
    total = len(products)
    total_pages = ceil(total / page_size) if total > 0 else 1
    
    return V2Response(
        products=products,
        page=1,
        total_pages=total_pages,
        has_more=total > page_size
    )

def rollback_v2_to_v1(v2: V2Response) -> V1Response:
    """
    Inverse transformation: V2Response → V1Response
    
    Property: rollback(migrate(v1)) = v1 (lossless)
    """
    return V1Response(products=v2.products)

# Test: Verify reversibility
def test_reversibility():
    v1 = V1Response(products=[Product(id=1), Product(id=2)])
    v2 = migrate_v1_to_v2(v1)
    v1_restored = rollback_v2_to_v1(v2)
    
    assert v1 == v1_restored, "Migration not reversible!"
```

## Success Criteria

1. ✅ Compatibility proven (backward compatible OR breaking changes documented)
2. ✅ Migration functions generated
3. ✅ Rollback functions generated (if reversible)
4. ✅ Migration strategy defined
5. ✅ Test cases for reversibility

## Next Steps

- Migration code ready for deployment
- Rollback strategy documented
- Version specifications complete