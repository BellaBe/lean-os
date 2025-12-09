---
name: natural-transformation-engine
description: Generate natural transformations for version migrations, feature flag changes, and strategy updates. Proves transformations preserve structure and verifies naturality conditions. Outputs migration/rollback code with correctness proofs.
allowed-tools: Read, Write, Bash
version: 1.0.0
---

# Natural Transformation Engine

## Purpose

Generate natural transformations (α: F → G) for version migrations, feature flags, and strategic changes. Verify naturality conditions and prove transformation correctness.

## Input

```
artifacts/engineering/specifications/v{X}/architecture.categorical (functors)
threads/engineering/{requirement}/1-input.md (version requirements)
```

## Output

```
artifacts/engineering/specifications/v{X}/versions.yaml
artifacts/engineering/proofs/architecture/natural-transformations/
```

## Transformation Types

### Type 1: Version Migration (V1 → V2)

**Use Case:** API version upgrade

**Example:**
```
V1Response = {products: List[Product]}
V2Response = {products: List[Product], page: int, total_pages: int}

Natural transformation α: V1 → V2
```

**Naturality Condition:**
```
For any f: V1 → V1,
α ∘ F(f) = G(f) ∘ α

Where F, G are version functors
```

**Implementation:**
```yaml
transformations:
  v1_to_v2:
    source_type: V1Response
    target_type: V2Response
    naturality_verified: true
    
    definition: |
      α(v1: V1Response) -> V2Response:
        return V2Response(
          products=v1.products,
          page=1,
          total_pages=ceil(len(v1.products) / page_size),
          has_more=len(v1.products) > page_size
        )
    
    backward_compatible: true
    rollback_possible: false  # V2 -> V1 loses pagination metadata
```

### Type 2: Feature Flag Change

**Use Case:** Enable/disable features

**Example:**
```
FeatureOff = Standard processing
FeatureOn = Enhanced processing

Natural transformation α: FeatureOff → FeatureOn
```

**Implementation:**
```yaml
transformations:
  enable_ai_analysis:
    source_type: ManualCategorization
    target_type: AICategorization
    naturality_verified: true
    
    definition: |
      α(manual: ManualCategories) -> AICategories:
        return AICategories(
          categories=manual.categories,  # Preserve existing
          confidence_scores=infer_confidence(manual.categories)
        )
    
    backward_compatible: true
    rollback_strategy: "Drop confidence scores, keep categories"
```

### Type 3: Platform Strategy Change

**Use Case:** Switch sync strategy

**Example:**
```
RestAPI = HTTP polling
WebhookAPI = Event-driven

Natural transformation α: RestAPI → WebhookAPI
```

**Implementation:**
```yaml
transformations:
  rest_to_webhook:
    source_type: PollingStrategy
    target_type: WebhookStrategy
    naturality_verified: true
    
    definition: |
      α(polling: PollingStrategy) -> WebhookStrategy:
        return WebhookStrategy(
          endpoint=polling.api_endpoint + "/webhooks",
          events=["product.created", "product.updated"],
          poll_interval=None  # Disable polling
        )
    
    backward_compatible: false
    migration_required: true
```

## Naturality Verification

### Naturality Square

For α: F → G to be natural:

```
F(A) --F(f)--> F(B)
 |              |
 αA             αB
 |              |
 v              v
G(A) --G(f)--> G(B)
```

**Condition:** `αB ∘ F(f) = G(f) ∘ αA`

### Verification Script

```bash
python {baseDir}/scripts/verify_naturality.py \
  --transformation v1_to_v2 \
  --functors artifacts/engineering/specifications/v{VERSION}/architecture.categorical \
  --iterations 1000 \
  --output artifacts/engineering/proofs/architecture/natural-transformations/v1-to-v2.proof
```

Expected output:
```json
{
  "transformation": "v1_to_v2",
  "naturality_verified": true,
  "test_cases": 1000,
  "all_passed": true,
  "diagram_commutes": true,
  "proof": "For all f: V1 → V1, verified: α ∘ F(f) = G(f) ∘ α"
}
```

## Execution Steps

### Step 1: Identify Transformation Needs

```bash
python {baseDir}/scripts/identify_transformations.py \
  --requirements threads/engineering/{requirement}/1-input.md \
  --current-version artifacts/engineering/specifications/v{PREV}/versions.yaml \
  --output /tmp/transformation-plan.json
```

### Step 2: Generate Transformation Definitions

```bash
python {baseDir}/scripts/generate_transformations.py \
  --plan /tmp/transformation-plan.json \
  --functors artifacts/engineering/specifications/v{VERSION}/architecture.categorical \
  --output artifacts/engineering/specifications/v{VERSION}/versions.yaml
```

### Step 3: Verify Naturality

```bash
python {baseDir}/scripts/verify_all_naturality.py \
  --transformations artifacts/engineering/specifications/v{VERSION}/versions.yaml \
  --output artifacts/engineering/proofs/architecture/natural-transformations/
```

### Step 4: Generate Migration/Rollback Code

```bash
python {baseDir}/scripts/generate_migration_code.py \
  --transformations artifacts/engineering/specifications/v{VERSION}/versions.yaml \
  --language python \
  --output artifacts/engineering/code/migrations/
```

## Output Format

```yaml
# artifacts/engineering/specifications/v{VERSION}/versions.yaml

current_version: v2
previous_version: v1

transformations:
  v1_to_v2:
    type: version_migration
    source: V1Response
    target: V2Response
    naturality_verified: true
    proof: proofs/architecture/natural-transformations/v1-to-v2.proof
    
    definition: |
      def migrate_v1_to_v2(v1: V1Response, page_size: int = 50) -> V2Response:
          """Natural transformation: V1Response → V2Response"""
          products = v1.products
          total = len(products)
          return V2Response(
              products=products,
              page=1,
              total_pages=(total + page_size - 1) // page_size,
              has_more=total > page_size
          )
    
    backward_compatible: true
    breaking_changes: []
    migration_required: false
  
  enable_ai_categorization:
    type: feature_flag
    source: ManualCategorization
    target: AICategorization
    naturality_verified: true
    proof: proofs/architecture/natural-transformations/ai-categorization.proof
    
    definition: |
      def enable_ai(manual: ManualCategories) -> AICategories:
          """Natural transformation: Manual → AI"""
          return AICategories(
              categories=manual.categories,
              confidence_scores=infer_confidence(manual.categories),
              model_version="v1.2.0"
          )
    
    backward_compatible: true
    rollback_strategy: "Drop confidence_scores, keep categories"

composition:
  sequential_migrations:
    - v1_to_v2
    - enable_ai_categorization
  
  composed_transformation: |
    # Vertical composition: α₂ ∘ α₁
    # V1 --α₁--> V2 --α₂--> V2+AI
    
    def migrate_v1_to_v2_with_ai(v1: V1Response) -> V2AIResponse:
        v2 = migrate_v1_to_v2(v1)
        return enable_ai(v2)
```

## Success Criteria

1. ✅ All transformations defined
2. ✅ Naturality verified (1000/1000 tests)
3. ✅ Backward compatibility documented
4. ✅ Migration/rollback code generated
5. ✅ Breaking changes identified

## Next Steps

- Pass to **curry-howard-prover** for type safety proofs
- Use in **version-compatibility-prover** for migration correctness