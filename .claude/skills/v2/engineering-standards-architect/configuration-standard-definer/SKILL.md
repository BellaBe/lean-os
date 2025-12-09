---
name: configuration-standard-definer
description: |
  Define configuration standards as categorical structures. Produces configuration
  reader monad, environment handling, feature flags, secret injection, and validation.
  Configuration as Reader monad threading config through computations.
  Input: All other standards, services.spec.yaml
  Output: standards/configuration/*.std.yaml
---

# Configuration Standard Definer

Define configuration patterns as categorical structures.

## Purpose

Transform configuration requirements into formal standards:
1. Configuration reader monad
2. Environment-specific overrides
3. Feature flags (conditional morphisms)
4. Secret management
5. Configuration validation

## Input

- All other standards (extract configurable values)
- `services.spec.yaml` - Operations with configuration

## Output

```
standards/configuration/
├── config.std.yaml         # Configuration reader
└── feature-flags.std.yaml  # Conditional morphisms
```

## Configuration Standard

### Schema

```yaml
# standards/configuration/config.std.yaml

standard:
  name: Configuration
  description: "Configuration as Reader monad"

# Reader monad for configuration
monad:
  name: Reader
  type_constructor: "Reader[C, A] = C → A"
  
  pure: |
    λa. λ_. a  # Ignore config, return value
    
  bind: |
    λma f. λc. f(ma(c))(c)  # Thread config through
    
  ask: |
    λc. c  # Get the config itself
    
  local: |
    λf ma. λc. ma(f(c))  # Modify config locally
    
  laws:
    - left_identity: "pure(a) >>= f ≡ f(a)"
    - right_identity: "m >>= pure ≡ m"
    - associativity: "(m >>= f) >>= g ≡ m >>= (x → f(x) >>= g)"

# Configuration structure
config:
  type: product
  sections:
    - name: app
      fields:
        - name: name
          type: string
          default: "leanos"
          
        - name: version
          type: string
          source: "env:APP_VERSION"
          
        - name: environment
          type: "dev | staging | prod"
          source: "env:ENVIRONMENT"
          default: "dev"
          
        - name: debug
          type: bool
          default: false
          
    - name: server
      fields:
        - name: host
          type: string
          default: "0.0.0.0"
          
        - name: port
          type: int
          default: 8000
          validation: "port >= 1 && port <= 65535"
          
        - name: workers
          type: int
          default: 4
          
    - name: database
      fields:
        - name: url
          type: string
          source: "secret:DATABASE_URL"
          required: true
          
        - name: pool_size
          type: int
          default: 10
          
        - name: pool_timeout
          type: int
          default: 30
          unit: seconds
          
    - name: redis
      fields:
        - name: url
          type: string
          source: "secret:REDIS_URL"
          required: true
          
        - name: default_ttl
          type: int
          default: 300
          unit: seconds
          
    - name: external
      subsections:
        - name: shopify
          fields:
            - name: api_key
              type: string
              source: "secret:SHOPIFY_API_KEY"
              required: true
              
            - name: api_secret
              type: string
              source: "secret:SHOPIFY_API_SECRET"
              required: true
              
            - name: api_version
              type: string
              default: "2024-01"
              
            - name: scopes
              type: "list[string]"
              default: ["read_products", "write_products"]
              
        - name: groq
          fields:
            - name: api_key
              type: string
              source: "secret:GROQ_API_KEY"
              required: true
              
            - name: model
              type: string
              default: "llama-3.2-90b-vision-preview"
              
            - name: timeout
              type: int
              default: 30000
              unit: milliseconds
              
    - name: observability
      fields:
        - name: log_level
          type: "DEBUG | INFO | WARN | ERROR"
          default: "INFO"
          
        - name: metrics_enabled
          type: bool
          default: true
          
        - name: tracing_enabled
          type: bool
          default: true
          
        - name: tracing_sample_rate
          type: float
          default: 0.1
          validation: "rate >= 0 && rate <= 1"

# Environment overrides
environments:
  - name: dev
    overrides:
      app.debug: true
      observability.log_level: DEBUG
      observability.tracing_sample_rate: 1.0
      
  - name: staging
    overrides:
      observability.log_level: INFO
      observability.tracing_sample_rate: 0.5
      
  - name: prod
    overrides:
      app.debug: false
      observability.log_level: WARN
      observability.tracing_sample_rate: 0.1
      server.workers: 8

# Configuration sources (priority order)
sources:
  priority:
    - name: environment_variables
      prefix: "APP_"
      transform: "SCREAMING_SNAKE_CASE"
      priority: 1  # Highest
      
    - name: secrets
      provider: "vault | aws_secrets | env"
      priority: 2
      
    - name: config_file
      format: yaml
      path: "config/{environment}.yaml"
      priority: 3
      
    - name: defaults
      location: "code"
      priority: 4  # Lowest

# Secret management
secrets:
  provider: environment  # Or vault, aws_secrets_manager
  
  required:
    - DATABASE_URL
    - REDIS_URL
    - SHOPIFY_API_KEY
    - SHOPIFY_API_SECRET
    - GROQ_API_KEY
    - JWT_SECRET
    
  rotation:
    enabled: false  # Enable in production
    interval_days: 90
    
  access:
    - service: api
      secrets: [all]
    - service: worker
      secrets: [DATABASE_URL, REDIS_URL, GROQ_API_KEY]

# Configuration validation
validation:
  on_startup: true
  fail_on_missing_required: true
  
  rules:
    - name: required_fields
      check: "All required fields have values"
      
    - name: type_validation
      check: "All values match declared types"
      
    - name: constraint_validation
      check: "All validation constraints pass"
      
    - name: secret_availability
      check: "All secrets are accessible"
      
    - name: url_format
      check: "URL fields are valid URLs"
      
    - name: connection_test
      check: "Database/Redis connections work"
      when: startup

# Categorical interpretation
categorical:
  # Config as product type
  product:
    definition: |
      Config = App × Server × Database × Redis × External × Observability
      
  # Reader as profunctor
  profunctor:
    definition: |
      Reader[C, A] is a profunctor in C
      dimap: (C' → C) → (A → A') → Reader[C, A] → Reader[C', A']
      
  # Config injection as natural transformation
  transformation:
    name: InjectConfig
    type: "Domain ⟹ ConfiguredDomain"
    components: |
      For each operation f: A → B,
      InjectConfig(f): Reader[Config, A] → Reader[Config, B]
```

## Feature Flags Standard

### Schema

```yaml
# standards/configuration/feature-flags.std.yaml

standard:
  name: FeatureFlags
  description: "Feature flags as conditional morphisms (coproduct selection)"

# Feature flag as coproduct selection
definition: |
  Feature flag selects between morphisms:
  flag: Bool → (A → B) + (A → B)
  If flag enabled: use new implementation
  If flag disabled: use old implementation

# Flag structure
flag:
  type: product
  fields:
    - name: key
      type: string
      description: "Unique identifier"
      
    - name: enabled
      type: bool
      default: false
      
    - name: rollout_percentage
      type: int
      range: [0, 100]
      default: 0
      
    - name: targeting
      type: option[TargetingRules]
      
    - name: variants
      type: "option[list[Variant]]"
      description: "For A/B testing"

# Feature flags
flags:
  - key: new_recommendation_engine
    description: "Use ML-based recommendations"
    default: false
    morphisms:
      enabled: generate_ml_recommendations
      disabled: generate_rule_recommendations
    rollout:
      strategy: percentage
      percentage: 10
      
  - key: enhanced_analysis
    description: "Use enhanced photo analysis"
    default: false
    morphisms:
      enabled: analyze_with_enhanced_model
      disabled: analyze_with_standard_model
    targeting:
      rules:
        - attribute: subscription_tier
          operator: in
          values: [Pro, Enterprise]
          
  - key: dark_mode_widget
    description: "Enable dark mode in widget"
    default: false
    client_side: true
    
  - key: rate_limit_v2
    description: "New rate limiting algorithm"
    default: false
    morphisms:
      enabled: apply_token_bucket
      disabled: apply_fixed_window

# Targeting rules
targeting:
  attributes:
    - name: user_id
      type: string
      
    - name: tenant_id
      type: string
      
    - name: subscription_tier
      type: "Free | Pro | Enterprise"
      
    - name: country
      type: string
      
    - name: created_at
      type: datetime
      
  operators:
    - equals
    - not_equals
    - in
    - not_in
    - greater_than
    - less_than
    - contains
    - percentage  # Hash-based percentage

# Rollout strategies
rollout:
  strategies:
    - name: all_or_nothing
      description: "Flag is either on or off globally"
      
    - name: percentage
      description: "Gradual rollout by percentage"
      mechanism: |
        hash(user_id) % 100 < percentage → enabled
        
    - name: targeting
      description: "Enable for specific segments"
      
    - name: scheduled
      description: "Enable at specific time"
      fields:
        - start_time
        - end_time

# Flag evaluation
evaluation:
  order:
    - check_kill_switch
    - check_targeting_rules
    - check_percentage_rollout
    - return_default
    
  caching:
    enabled: true
    ttl_seconds: 60
    
  fallback:
    on_error: return_default
    on_timeout: return_cached

# Morphism wrapping
wrapping:
  pattern: |
    def flagged_operation(input):
      if feature_flags.is_enabled("flag_key", context):
        return new_implementation(input)
      else:
        return old_implementation(input)
        
  decorator: |
    @feature_flag("flag_key")
    def operation(input):
      # New implementation
      pass
      
    @operation.fallback
    def operation_fallback(input):
      # Old implementation
      pass

# Categorical interpretation
categorical:
  # Flag as coproduct elimination
  coproduct:
    definition: |
      Flag selects from coproduct:
      [f, g]: (A → B) + (A → B) → (A → B)
      where flag determines which injection to use
      
  # Conditional morphism
  conditional:
    definition: |
      flag_morphism: Flag × A → B
      Equivalent to: (Flag → A → B)
      
  # Reader composition
  reader_composition: |
    Flags are read from config:
    getFlag: Reader[Config, Bool]
    Operation uses: Reader[Config, A → B]
    
  laws:
    - "Flag evaluation is pure (deterministic given context)"
    - "Same context always gives same flag value"
```

## Validation

### Completeness Checks

```yaml
completeness:
  - all_required_config_specified
  - all_secrets_identified
  - all_flags_have_default
  - environment_overrides_valid
```

### Consistency Checks

```yaml
consistency:
  - no_duplicate_keys
  - types_match_usage
  - validation_rules_valid
  - flag_morphisms_exist
```

## Next Skills

Output feeds into:
- `standards-validator`
