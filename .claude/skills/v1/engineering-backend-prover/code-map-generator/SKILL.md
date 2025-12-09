---
name: code-map-generator
description: Generate structural code maps from system-architect specifications. Parses ADT, functors, composition rules and creates service maps (~300 lines) without implementation details. Sub-skill of backend-prover Phase 1.
version: 1.0.0
allowed-tools: bash_tool, create_file, view
model: claude-sonnet-4-20250514
license: Proprietary - LeanOS Engineering Layer
---

# code-map-generator: Specification → Maps

## Purpose

Generate structural specifications (maps) from system-architect output. Maps declare structure WITHOUT implementation:

**What maps contain:**
- Service structure (name, dependencies, methods)
- Type signatures (morphisms)
- Composition order (explicit sequence)
- Effects (IO, Error, State)
- Error handling strategies
- Implementation strategies (sequential, parallel, cached)

**What maps do NOT contain:**
- Actual code
- Implementation logic
- Business rules

**Output size:** ~300 lines (vs 5000+ for code)

---

## Input

**From system-architect:**
```
artifacts/engineering/specifications/v{X}/
├── manifest.json                    # Version + hash (locked)
├── adt.yaml                        # Algebraic Data Types
├── functors.yaml                   # Functor definitions
├── composition.yaml                # Composition rules
├── state-machines.yaml             # State machines
├── effects.yaml                    # Effect system
├── services.spec.yaml              # Service topology
└── api.openapi.json                # Public API
```

---

## Process

### Step 1: Load Specifications

```bash
# Read manifest
spec_version=$(jq -r '.version' artifacts/engineering/specifications/manifest.json)
spec_hash=$(jq -r '.hash' artifacts/engineering/specifications/manifest.json)

echo "Generating maps from specification v$spec_version ($spec_hash)"

# Load specification files
adt_file="artifacts/engineering/specifications/v${spec_version}/adt.yaml"
functors_file="artifacts/engineering/specifications/v${spec_version}/functors.yaml"
composition_file="artifacts/engineering/specifications/v${spec_version}/composition.yaml"
services_file="artifacts/engineering/specifications/v${spec_version}/services.spec.yaml"
effects_file="artifacts/engineering/specifications/v${spec_version}/effects.yaml"
sm_file="artifacts/engineering/specifications/v${spec_version}/state-machines.yaml"
```

### Step 2: Generate Types Map

Parse `adt.yaml` and create type definitions:

```yaml
# Output: artifacts/engineering/maps/backend/types.map.yaml

types:
  - name: Tenant
    category_role: Object
    description: Multi-tenant context
    fields:
      - name: id
        type: UUID
        required: true
      - name: config
        type: TenantConfig
        required: true
  
  - name: Entity
    category_role: Object
    description: Domain entity
    fields:
      - name: id
        type: UUID
      - name: name
        type: String
      - name: value
        type: Decimal
      - name: status
        type: EntityStatus

  - name: Entities
    category_role: Object
    description: Entity collection
    fields:
      - name: items
        type: List[Entity]
      - name: total
        type: Int
      - name: cursor
        type: Optional[String]

specification_version: "v1.2.0"
generated_at: "2025-01-15T10:30:00Z"
```

**Key principles:**
- One type per ADT definition
- Include category role (Object, Sum Type, Product Type)
- List all fields with types
- Mark required vs optional

---

### Step 3: Generate Service Maps

For each service in `services.spec.yaml`:

```yaml
# Output: artifacts/engineering/maps/backend/services/{domain}_service.map.yaml

service:
  name: {Domain}Service
  type: Object[{Domain}Service]
  category_role: Object in ServiceCategory

  metadata:
    description: Multi-tenant {domain} data synchronization
    owner: engineering
    version: 1.0.0
    specification_version: "v1.2.0"
  
  # Dependencies from services.spec.yaml
  dependencies:
    - name: db
      type: DatabaseConnection
      morphism: TenantConfig → DatabaseConnection
      initialization: "from_tenant_config(tenant)"
      required: true
      
    - name: cache
      type: RedisConnection
      morphism: TenantConfig → RedisConnection
      initialization: "redis_pool.get_connection(tenant.redis_config)"
      required: false
      
    - name: platform_adapter
      type: PlatformAdapter
      morphism: TenantConfig → PlatformAdapter
      initialization: "PlatformAdapter(tenant)"
      required: true
  
  # State from services.spec.yaml
  state:
    stateful: false
    state_machine: null
    state_type: null
  
  # Methods from composition.yaml
  methods:
    - name: sync_entities
      signature: (Tenant, Platform) → IO[Either[Error, Entities]]
      category_role: Morphism[Tenant × Platform, IO[Either[Error, Entities]]]

      # Composition from composition.yaml
      composition:
        - call: platform_adapter.fetch_entities
          morphism: Platform → IO[Either[Error, RawEntities]]
          parallel: false
          description: Fetch entities from platform API

        - call: transform_entities
          morphism: RawEntities → Entities
          parallel: false
          description: Transform to canonical format

        - call: db.save_entities
          morphism: Entities → IO[Either[Error, Unit]]
          parallel: false
          description: Save to tenant database

      # Will be verified in composition-map-validator
      composition_law_verified: false
      proof_reference: proofs/backend/composition/sync-entities.proof

      # Effects from effects.yaml
      effects:
        io: [http, database, cache]
        error: [PlatformAPIError, DatabaseError, ValidationError, NetworkError]
        state: []

      # Error handling from effects.yaml
      error_handling:
        PlatformAPIError: retry_3x_exponential
        DatabaseError: rollback_transaction
        ValidationError: return_left
        NetworkError: circuit_breaker

      # Implementation strategy
      implementation_strategy: sequential_with_retry

      # Documentation
      documentation: |
        Fetches entities from platform API, transforms to canonical format,
        saves to tenant database. Composition of 3 morphisms with IO effects.
        Guarantees atomicity through transaction management.
      
      # Tests specification
      tests:
        unit:
          - name: test_sync_entities_success
            property: For valid tenant and platform, returns Entities

          - name: test_sync_entities_api_failure
            property: PlatformAPIError triggers retry with exponential backoff

          - name: test_sync_entities_db_failure
            property: DatabaseError triggers rollback

        integration:
          - name: test_sync_entities_end_to_end
            scenario: Real Platform API → Transform → DB save → Verification

        property:
          - name: test_composition_associativity
            property: Composition order doesn't affect result

    - name: bulk_sync_entities
      signature: (Tenant, Platform, List[EntityID]) → IO[Either[Error, SyncResults]]
      category_role: Morphism[Tenant × Platform × List[EntityID], IO[Either[Error, SyncResults]]]

      composition:
        - call: platform_adapter.fetch_entities_batch
          morphism: (Platform, List[EntityID]) → IO[Either[Error, List[RawEntities]]]
          parallel: true  # Batch fetch in parallel
          description: Parallel fetch entity batches

        - call: transform_entities_parallel
          morphism: List[RawEntities] → List[Entities]
          parallel: true  # Transform in parallel
          description: Parallel transformation

        - call: db.save_entities_batch
          morphism: List[Entities] → IO[Either[Error, SyncResults]]
          parallel: false  # Sequential for consistency
          description: Sequential batch save for consistency
      
      composition_law_verified: false
      proof_reference: proofs/backend/composition/bulk-sync-entities.proof

      effects:
        io: [http_batch, database_batch, cache]
        error: [PlatformAPIError, DatabaseError, ValidationError, PartialFailureError]
        state: []

      error_handling:
        PlatformAPIError: partial_retry
        DatabaseError: rollback_transaction
        ValidationError: skip_invalid_continue
        PartialFailureError: aggregate_results

      implementation_strategy: parallel_with_partial_failure

      documentation: |
        Bulk synchronization with parallel processing and partial failure handling.
        Uses parallel functor composition for performance while maintaining correctness.

generated_at: "2025-01-15T10:30:00Z"
```

**Generation rules:**
1. One service map per service in services.spec.yaml
2. Extract dependencies from service topology
3. Extract methods from composition.yaml
4. Composition order MUST be explicit (ordered list)
5. Effects MUST be declared (io, error, state)
6. Error handling MUST be specified for each error type
7. Test specifications MUST be included

---

### Step 4: Generate Composition Map

Map composition relationships across services:

```yaml
# Output: artifacts/engineering/maps/backend/composition.map.yaml

compositions:
  - name: {domain}_sync_pipeline
    signature: (Tenant, Platform) → IO[Either[Error, Entities]]
    description: End-to-end entity synchronization pipeline

    # Services involved
    components:
      - service: {Domain}Service
        method: sync_entities
        morphism: (Tenant, Platform) → IO[Either[Error, Entities]]
    
    # Composition structure (will verify in validator)
    composition_structure:
      associativity_verified: false
      identity_preserved: false
      effects_compose: true
      
      sequential_flow: |
        Platform → fetch_products → RawProducts
                ↓
        RawProducts → transform_products → Products
                ↓
        Products → save_products → IO[Either[Error, Unit]]
                ↓
        Result: IO[Either[Error, Products]]
    
    proof_reference: proofs/backend/composition/catalog-sync-pipeline.proof
    
    visualization: |
      graph LR
        A[Platform] --> B[fetch_products]
        B --> C[RawProducts]
        C --> D[transform_products]
        D --> E[Products]
        E --> F[save_products]
        F --> G[IO Either Error Unit]
  
  - name: cross_service_integration
    signature: (Order, Tenant) → IO[Either[Error, PaymentResult]]
    description: Multi-service composition (catalog → billing)
    
    components:
      - service: CatalogService
        method: get_product_price
        morphism: ProductID → IO[Either[Error, Price]]
      
      - service: BillingService
        method: charge_customer
        morphism: (CustomerId, Price) → IO[Either[Error, PaymentResult]]
    
    composition_structure:
      associativity_verified: false
      identity_preserved: false
      effects_compose: true
      
      sequential_flow: |
        Order → extract_product_id → ProductID
                ↓
        ProductID → CatalogService.get_product_price → Price
                ↓
        (CustomerId, Price) → BillingService.charge_customer → PaymentResult

specification_version: "v1.2.0"
generated_at: "2025-01-15T10:30:00Z"
```

**Composition types:**
1. **Single-service:** Methods within one service
2. **Cross-service:** Methods across multiple services
3. **Complex pipelines:** Multi-step, multi-service flows

---

### Step 5: Generate Effects Map

Declare effect system from `effects.yaml`:

```yaml
# Output: artifacts/engineering/maps/backend/effects.map.yaml

effect_system:
  # IO effects
  io_effects:
    - name: http
      description: External HTTP API calls
      retry_policy: exponential_backoff
      timeout: 30s
      max_retries: 3
      
    - name: database
      description: Database read/write operations
      transactional: true
      timeout: 10s
      isolation_level: read_committed
      
    - name: cache
      description: Redis cache operations
      timeout: 5s
      failure_mode: degrade_gracefully
      
    - name: http_batch
      description: Batch HTTP requests
      retry_policy: partial_retry
      timeout: 60s
      max_concurrent: 10
  
  # Error types
  error_types:
    - name: {Platform}APIError
      category: external
      retryable: true
      retry_strategy: exponential_backoff_3x
      base_delay: 1s
      max_delay: 30s
      
    - name: DatabaseError
      category: infrastructure
      retryable: false
      requires_rollback: true
      
    - name: ValidationError
      category: domain
      retryable: false
      user_facing: true
      
    - name: NetworkError
      category: infrastructure
      retryable: true
      retry_strategy: circuit_breaker
      failure_threshold: 5
      timeout: 30s
      
    - name: PartialFailureError
      category: domain
      retryable: false
      aggregates_errors: true
  
  # Composition rules
  composition_rules:
    - rule: IO effects compose sequentially by default
      verified: true
      
    - rule: Parallel IO requires explicit annotation
      verified: true
      
    - rule: Error effects short-circuit on Left
      verified: true
      
    - rule: State effects must be declared
      verified: true

specification_version: "v1.2.0"
generated_at: "2025-01-15T10:30:00Z"
```

---

### Step 6: Generate State Machines Map

Reference state machines from `state-machines.yaml`:

```yaml
# Output: artifacts/engineering/maps/backend/state-machines.map.yaml

state_machines:
  - name: PaymentFlow
    reference: specifications/v1.2.0/state-machines.yaml#PaymentFlow
    description: Payment processing state machine
    
    states:
      - pending
      - processing
      - completed
      - failed
      - refunded
    
    initial_state: pending
    terminal_states: [completed, failed, refunded]
    
    transitions:
      - from: pending
        to: processing
        event: start_payment
        guard: has_valid_payment_method
        
      - from: processing
        to: completed
        event: payment_success
        
      - from: processing
        to: failed
        event: payment_failure
        
      - from: completed
        to: refunded
        event: initiate_refund
        guard: within_refund_window
    
    invariants:
      - Terminal states have no outgoing transitions
      - All states reachable from initial
      - No deadlocks (all non-terminal states have outgoing transitions)
  
  - name: OrderFlow
    reference: specifications/v1.2.0/state-machines.yaml#OrderFlow
    description: Order lifecycle state machine
    
    states:
      - draft
      - confirmed
      - shipped
      - delivered
      - cancelled
    
    initial_state: draft
    terminal_states: [delivered, cancelled]
    
    transitions:
      - from: draft
        to: confirmed
        event: confirm_order
        guard: has_valid_items
        
      - from: confirmed
        to: shipped
        event: mark_shipped
        guard: payment_completed
        
      - from: shipped
        to: delivered
        event: confirm_delivery
        
      - from: [draft, confirmed]
        to: cancelled
        event: cancel_order

specification_version: "v1.2.0"
generated_at: "2025-01-15T10:30:00Z"
```

---

## Output

**Generated maps:**
```
artifacts/engineering/maps/backend/
├── services/
│   ├── catalog_service.map.yaml         (~80 lines)
│   ├── billing_service.map.yaml         (~75 lines)
│   ├── auth_service.map.yaml            (~60 lines)
│   └── ... (N services)
│
├── types.map.yaml                        (~50 lines)
├── composition.map.yaml                  (~40 lines)
├── effects.map.yaml                      (~35 lines)
└── state-machines.map.yaml              (~30 lines)

Total: ~300 lines (vs 5000+ for code)
```

**Map metadata:**
```yaml
# Each map includes:
specification_version: "v1.2.0"        # Locked version
generated_at: "2025-01-15T10:30:00Z"  # Generation timestamp
```

---

## Success Criteria

✓ All services from services.spec.yaml have maps
✓ All methods have explicit composition order
✓ All effects declared (io, error, state)
✓ All error types have handling strategies
✓ All state machines referenced
✓ Test specifications included
✓ Maps are ~300 lines total
✓ Maps contain NO implementation code

---

## Next Step

After maps generated, invoke `composition-map-validator` to verify structural correctness BEFORE code generation.

---

## Error Handling

**Specification file missing:**
```bash
ERROR: adt.yaml not found
Action: Verify system-architect completed successfully
```

**Invalid YAML:**
```bash
ERROR: Failed to parse composition.yaml
Action: Check system-architect output validity
```

**Missing composition rules:**
```bash
ERROR: No composition rules for method sync_products
Action: Verify system-architect generated composition.yaml
```

---

## Key Insights

1. **Maps are cheap** - 300 lines vs 5000+ for code
2. **Maps are readable** - Human can review in 5 minutes
3. **Maps are language-agnostic** - Same maps → Python, TypeScript, Rust
4. **Maps enable verification** - Structural checking (decidable, fast)
5. **Maps prevent waste** - Catch errors before expensive code generation

**Next:** composition-map-validator validates these maps structurally (~1 second)