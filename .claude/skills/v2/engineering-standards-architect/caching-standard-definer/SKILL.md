---
name: caching-standard-definer
description: |
  Define caching standards as categorical structures. Produces cache adjunction 
  (Forget ⊣ Cache), invalidation strategies, consistency models, and TTL policies.
  Caching as adjunction between cached and uncached domains.
  Input: categories/*.std.yaml, services.spec.yaml
  Output: standards/caching/*.std.yaml
---

# Caching Standard Definer

Define caching patterns as categorical structures.

## Purpose

Transform cacheable operations into formal cache standards:
1. Cache adjunction (Forget ⊣ Cache)
2. Invalidation strategies
3. Consistency models
4. TTL policies

## Input

- `standards/categories/*.std.yaml` - Category definitions
- `services.spec.yaml` - Operations to cache

## Output

```
standards/caching/
├── cache.std.yaml         # Cache adjunction
└── invalidation.std.yaml  # Invalidation strategies
```

## Cache Standard

### Schema

```yaml
# standards/caching/cache.std.yaml

standard:
  name: Cache
  description: "Caching as adjunction Forget ⊣ Cache"

# Cache adjunction: Forget ⊣ Cache
adjunction:
  name: "Forget ⊣ Cache"
  
  left_functor:
    name: Forget
    source: CachedDomain
    target: Domain
    description: "Strip cache, return underlying value"
    
    object_map:
      CachedMerchant: Merchant
      CachedProfile: Profile
      CachedProducts: "List[Product]"
      
    morphism_map:
      cached_get: get  # Underlying operation
      
  right_functor:
    name: Cache
    source: Domain
    target: CachedDomain
    description: "Add cache layer to operations"
    
    object_map:
      Merchant: CachedMerchant
      Profile: CachedProfile
      "List[Product]": CachedProducts
      
    morphism_map:
      get: cached_get  # Cached version
      
  unit:
    name: η
    type: "A → Cache(Forget(A))"
    semantics: "Cache lookup - check if value exists in cache"
    implementation: |
      λa. cache.get(key(a)) match {
        Some(cached) → cached
        None → compute(a)
      }
      
  counit:
    name: ε
    type: "Forget(Cache(A)) → A"
    semantics: "Cache hit - return underlying value"
    implementation: |
      λcached. cached.value
      
  triangle_identities:
    left: "(ε ∘ Forget) ∘ (Forget ∘ η) = id_Forget"
    right: "(Cache ∘ ε) ∘ (η ∘ Cache) = id_Cache"

# Cache types
cache_types:
  - name: read_through
    description: "Check cache, fetch on miss, populate cache"
    pattern: |
      def get(key):
        if key in cache:
          return cache[key]
        value = fetch(key)
        cache[key] = value
        return value
    use_for: [get_merchant, get_profile, get_products]
    
  - name: write_through
    description: "Write to cache and storage simultaneously"
    pattern: |
      def put(key, value):
        storage.put(key, value)
        cache[key] = value
    use_for: [update_merchant, update_profile]
    
  - name: write_behind
    description: "Write to cache immediately, async to storage"
    pattern: |
      def put(key, value):
        cache[key] = value
        queue_write(key, value)  # Async
    use_for: [update_analytics]  # Eventual consistency OK
    
  - name: cache_aside
    description: "Application manages cache explicitly"
    pattern: |
      def get(key):
        value = cache.get(key)
        if value is None:
          value = storage.get(key)
          # Application decides whether to cache
        return value
    use_for: [complex_queries]

# Cacheable operations
cacheable:
  # Read operations
  reads:
    - morphism: get_merchant
      cache_key: "merchant:{id}"
      ttl_seconds: 300
      strategy: read_through
      
    - morphism: get_profile
      cache_key: "profile:{id}"
      ttl_seconds: 300
      strategy: read_through
      
    - morphism: list_products
      cache_key: "products:{merchant_id}:{page}:{size}"
      ttl_seconds: 60
      strategy: read_through
      
    - morphism: get_recommendations
      cache_key: "recommendations:{profile_id}"
      ttl_seconds: 600  # 10 minutes
      strategy: read_through
      
  # External API results
  external:
    - morphism: fetch_shop
      cache_key: "shopify:shop:{domain}"
      ttl_seconds: 3600  # 1 hour
      strategy: read_through
      fallback: true  # Use stale on error

# TTL policies
ttl:
  defaults:
    short: 60        # 1 minute
    medium: 300      # 5 minutes
    long: 3600       # 1 hour
    very_long: 86400 # 1 day
    
  by_type:
    merchant: medium
    profile: medium
    analysis: long
    products: short
    recommendations: medium
    external_api: long

# Cache key patterns
keys:
  format: "{entity}:{id}:{variant}"
  
  patterns:
    - entity: merchant
      key: "merchant:{merchant_id}"
      
    - entity: profile
      key: "profile:{profile_id}"
      
    - entity: products
      key: "products:{merchant_id}:page:{page}"
      
    - entity: recommendations
      key: "recs:{profile_id}:v{version}"
      
  rules:
    - max_key_length: 250
    - no_special_chars: true
    - include_version: optional

# Categorical interpretation
categorical:
  # Cache forms a comonad (dual of monad)
  comonad:
    name: CacheComonad
    type_constructor: "Cached[A] = (A, CacheMetadata)"
    
    extract: "cached ↦ cached.value"  # Get underlying value
    duplicate: "cached ↦ Cached(cached)"  # Nested cache
    
  laws:
    - extract_duplicate: "extract ∘ duplicate = id"
    - duplicate_extract: "fmap extract ∘ duplicate = id"
    - duplicate_duplicate: "duplicate ∘ duplicate = fmap duplicate ∘ duplicate"
    
  # Adjunction laws
  adjunction_laws:
    - "Forget(Cache(A)) ≅ A (via counit)"
    - "A → Cache(Forget(A)) (via unit = lookup)"
```

## Invalidation Standard

### Schema

```yaml
# standards/invalidation.std.yaml

standard:
  name: Invalidation
  description: "Cache invalidation as morphism triggers"

# Invalidation strategies
strategies:
  - name: time_based
    description: "Expire after TTL"
    mechanism: |
      cache.set(key, value, ttl=ttl_seconds)
      # Automatically expires
    use_for: [read_heavy, external_data]
    
  - name: write_invalidation
    description: "Invalidate on write"
    mechanism: |
      def update(entity):
        result = storage.update(entity)
        cache.delete(cache_key(entity))
        return result
    use_for: [consistency_critical]
    
  - name: event_based
    description: "Invalidate on domain events"
    mechanism: |
      @on_event(MerchantUpdated)
      def invalidate_merchant(event):
        cache.delete(f"merchant:{event.merchant_id}")
        cache.delete_pattern(f"products:{event.merchant_id}:*")
    use_for: [event_driven_systems]
    
  - name: version_based
    description: "Include version in cache key"
    mechanism: |
      cache_key = f"{entity}:{id}:v{version}"
      # Old versions naturally expire or get overwritten
    use_for: [high_concurrency]

# Invalidation rules
rules:
  # Direct invalidation
  direct:
    - trigger: update_merchant
      invalidates:
        - "merchant:{id}"
        
    - trigger: update_profile
      invalidates:
        - "profile:{id}"
        - "recs:{id}:*"  # Also invalidate recommendations
        
    - trigger: delete_merchant
      invalidates:
        - "merchant:{id}"
        - "products:{id}:*"
        - "profiles:{id}:*"
        
  # Cascade invalidation
  cascade:
    - trigger: update_merchant_settings
      invalidates:
        - "merchant:{merchant_id}"
        - "products:{merchant_id}:*"  # Product display affected
        
    - trigger: complete_analysis
      invalidates:
        - "profile:{profile_id}"
        - "recs:{profile_id}:*"  # New recommendations needed

# Consistency models
consistency:
  - name: strong
    description: "Always consistent with storage"
    strategy: write_invalidation
    trade_off: "Lower cache hit rate"
    use_for: [financial_data, permissions]
    
  - name: eventual
    description: "May be temporarily stale"
    strategy: time_based
    max_staleness: 60  # seconds
    use_for: [product_listings, analytics]
    
  - name: read_your_writes
    description: "User sees their own updates"
    strategy: |
      On write: invalidate for user
      Other users: may see stale data
    use_for: [user_preferences]

# Staleness handling
staleness:
  # Stale-while-revalidate
  swr:
    enabled: true
    stale_ttl: 60       # Serve stale for this long
    refresh_async: true  # Refresh in background
    
  # Stale-if-error
  sie:
    enabled: true
    serve_stale_on:
      - connection_error
      - timeout
      - 5xx_response
    max_stale_seconds: 300

# Cache warming
warming:
  strategies:
    - name: on_startup
      description: "Pre-populate cache on service start"
      entities: [merchants, products]
      
    - name: on_miss
      description: "Async populate related data on miss"
      example: |
        on_cache_miss(merchant):
          async_warm(merchant.products)
          async_warm(merchant.profiles)
          
    - name: scheduled
      description: "Periodic refresh of hot data"
      schedule: "*/5 * * * *"  # Every 5 minutes
      entities: [hot_products]

# Categorical interpretation
categorical:
  # Invalidation as inverse morphism (pseudo-inverse)
  inverse:
    description: |
      For cacheable morphism f: A → Cached[B],
      invalidate(f) is pseudo-inverse: Cached[B] → Unit
      
  # Invalidation triggers as morphism composition
  composition: |
    update: A → B triggers invalidate: Cached[B] → Unit
    Composition: update ; invalidate removes stale data
    
  laws:
    - "After invalidate, next get fetches fresh data"
    - "Invalidation is idempotent"
```

## Validation

### Completeness Checks

```yaml
completeness:
  - all_reads_have_cache_strategy
  - all_writes_have_invalidation
  - all_cached_have_ttl
  - external_apis_have_fallback
```

### Consistency Checks

```yaml
consistency:
  - invalidation_covers_dependencies
  - ttl_appropriate_for_data_type
  - no_orphan_cache_entries
  - cache_keys_unique
```

## Next Skills

Output feeds into:
- `configuration-standard-definer`
- `standards-validator`
