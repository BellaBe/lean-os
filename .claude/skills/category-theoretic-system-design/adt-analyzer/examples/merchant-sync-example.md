# Merchant Sync Example

## Requirement

"Merchant onboarding service needs authentication and supports Shopify or WooCommerce platforms, with either AI-powered analysis or manual entry for product categorization."

## Step 1: Identify Structure

**Products (×):**
- "needs authentication" → Auth is required
- "with...for" → Analysis method is required

**Coproducts (+):**
- "Shopify or WooCommerce" → Platform choice
- "AI-powered analysis or manual entry" → Analysis method choice

## Step 2: Build ADT

```
MerchantSync = Auth × Platform × Analysis

Where:
  Platform = Shopify + WooCommerce
  Analysis = AI + Manual
```

Substituting:
```
MerchantSync = Auth × (Shopify + WooCommerce) × (AI + Manual)
```

## Step 3: Apply Distributive Law

First distribute over Platform:
```
= Auth × Shopify × (AI + Manual) + Auth × WooCommerce × (AI + Manual)
```

Then distribute over Analysis:
```
= (Auth × Shopify × AI) 
+ (Auth × Shopify × Manual)
+ (Auth × WooCommerce × AI)
+ (Auth × WooCommerce × Manual)
```

## Step 4: Canonical Form

```json
{
  "specification": "Merchant onboarding with auth, platform choice, analysis choice",
  "canonical_form": {
    "paths": [
      {
        "id": 1,
        "components": ["Auth", "Shopify", "AI"],
        "description": "Shopify integration with AI analysis"
      },
      {
        "id": 2,
        "components": ["Auth", "Shopify", "Manual"],
        "description": "Shopify integration with manual entry"
      },
      {
        "id": 3,
        "components": ["Auth", "WooCommerce", "AI"],
        "description": "WooCommerce integration with AI analysis"
      },
      {
        "id": 4,
        "components": ["Auth", "WooCommerce", "Manual"],
        "description": "WooCommerce integration with manual entry"
      }
    ],
    "total_paths": 4
  }
}
```

## Implementation

Each path becomes a concrete implementation:

```python
class MerchantSyncService:
    def sync(self, auth: Auth, platform: Platform, analysis: Analysis):
        match (platform, analysis):
            case (Shopify(), AI()):
                return self.shopify_ai_sync(auth)
            case (Shopify(), Manual()):
                return self.shopify_manual_sync(auth)
            case (WooCommerce(), AI()):
                return self.woocommerce_ai_sync(auth)
            case (WooCommerce(), Manual()):
                return self.woocommerce_manual_sync(auth)
```

## Test Cases

Each path needs:
1. Unit tests
2. Integration tests  
3. Edge case handling

Total test scenarios: 4 × 3 = 12 minimum test cases.

## Benefits

- **Completeness**: All 4 paths explicitly identified
- **No missing cases**: Exhaustive enumeration
- **Clear implementation**: Each path maps to code
- **Testability**: Each path independently testable
