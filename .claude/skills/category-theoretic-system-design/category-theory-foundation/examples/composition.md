# Composition Patterns

Common composition patterns in category-theoretic system design.

## Pattern 1: Service Pipeline

**Structure:** A → B → C → D

**Property:** Associative composition allows flexible grouping

**Example:**
```python
# Request processing pipeline
request_parser: Request → ParsedRequest
validator: ParsedRequest → ValidRequest  
handler: ValidRequest → Response

# All groupings are equivalent:
pipeline1 = compose(handler, compose(validator, parser))
pipeline2 = compose(compose(handler, validator), parser)

# Both produce the same result
assert pipeline1(req) == pipeline2(req)
```

## Pattern 2: Multi-Argument Service (Currying)

**Structure:** (A, B) → C ≅ A → (B → C)

**Property:** Partial application through currying

**Example:**
```python
# Database query service
def query(config: Config, query_string: str) -> Result:
    # Implementation
    pass

# Curry to pre-configure
def create_query_service(config: Config):
    return lambda query_string: query(config, query_string)

# Pre-configured services
prod_query = create_query_service(prod_config)
dev_query = create_query_service(dev_config)
```

## Pattern 3: Optional Service (Maybe Functor)

**Structure:** Maybe a with fmap: (a → b) → Maybe a → Maybe b

**Property:** Transform values that may or may not exist

**Example:**
```python
# Cache service that may not be available
cache_service: Maybe[CacheService]

# Apply transformation regardless of existence
def add_ttl(service):
    # Add time-to-live functionality
    pass

enhanced_cache = fmap(add_ttl, cache_service)
# If cache exists: adds TTL
# If cache is None: remains None
```

See full composition.md for:
- Error handling with Either
- Async composition with Future
- List processing  
- State management
- Reader monad pattern
