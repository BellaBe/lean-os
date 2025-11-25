---
name: functor-generator
description: Detect transformation patterns in ADT paths (multi-tenant, optional, collections, async) and generate functors that preserve structure. Outputs categorical architecture with functor definitions and verified laws.
allowed-tools: Read, Write, Bash
version: 1.0.0
---

# Functor Generator

## Purpose

Analyze ADT paths from validated specifications and generate functors for common transformation patterns. Functors preserve structure while enabling composition, optimization, and parallel execution.

## Input

```
artifacts/engineering/specifications/v{X}/requirements.adt (validated)
```

## Output

```
artifacts/engineering/specifications/v{X}/architecture.categorical
```

## Pattern Detection

### Pattern 1: Multi-Tenant (Reader Functor)

**Signature:** `Reader[Config, F[A]]`

**Detects:**
- `Tenant` appears in product
- `TenantConfig` or `Credentials` present
- Service needs context passed implicitly

**Example:**
```
Input path: Tenant × Platform × Version
Detected: Reader[TenantConfig, Platform → Version → Result]
```

**Functor Definition:**
```yaml
functors:
  tenant_reader:
    type: Reader[TenantConfig, Service]
    structure_preserved: true
    laws_verified:
      identity: "fmap id = id"
      composition: "fmap (g ∘ f) = fmap g ∘ fmap f"
    
    implementation_hint: |
      Pass tenant config through call chain without threading it explicitly
      
      def run_service(tenant: TenantConfig):
          def inner(request: Request) -> Response:
              # tenant is captured in closure
              return process(request, tenant)
          return inner
```

### Pattern 2: Optional Features (Maybe Functor)

**Signature:** `Maybe[A] = Some A + None`

**Detects:**
- "optional" in requirements
- Feature flags
- Nullable fields
- `A + Unit` pattern

**Example:**
```
Input: Optional email, optional address
Detected: Maybe[Email], Maybe[Address]
```

**Functor Definition:**
```yaml
functors:
  optional_feature:
    type: Maybe[Feature]
    structure_preserved: true
    laws_verified:
      identity: true
      composition: true
    
    implementation_hint: |
      Use Option/Optional/Maybe type from standard library
      
      def fmap(f: A -> B, maybe: Maybe[A]) -> Maybe[B]:
          match maybe:
              case Some(a): return Some(f(a))
              case None: return None
```

### Pattern 3: Collections (List Functor)

**Signature:** `List[A]`, `Set[A]`, `Map[K, V]`

**Detects:**
- Plural nouns ("products", "orders")
- "list of", "collection of"
- Aggregation requirements

**Example:**
```
Input: Fetch all products
Detected: List[Product]
```

**Functor Definition:**
```yaml
functors:
  list_functor:
    type: List[Product]
    structure_preserved: true
    laws_verified:
      identity: "map id xs = xs"
      composition: "map (g ∘ f) xs = map g (map f xs)"
    
    implementation_hint: |
      Standard map operation over collections
      
      def fmap(f: A -> B, xs: List[A]) -> List[B]:
          return [f(x) for x in xs]
```

### Pattern 4: Async Operations (IO Functor)

**Signature:** `IO[A]`, `Async[A]`, `Future[A]`

**Detects:**
- "async", "background", "queue"
- HTTP requests
- Database queries
- File I/O

**Example:**
```
Input: Fetch products from external API
Detected: IO[Products]
```

**Functor Definition:**
```yaml
functors:
  async_io:
    type: IO[Result]
    structure_preserved: true
    laws_verified:
      identity: true
      composition: true
    
    implementation_hint: |
      Wrap async operations in IO/Future monad
      
      async def fmap(f: A -> B, io: IO[A]) -> IO[B]:
          result = await io
          return f(result)
```

### Pattern 5: Error Handling (Either Functor)

**Signature:** `Either[Error, Success]`

**Detects:**
- Error handling requirements
- Validation failures
- `Result` or `Try` types
- Success + failure paths

**Example:**
```
Input: Validate user input, may fail
Detected: Either[ValidationError, User]
```

**Functor Definition:**
```yaml
functors:
  error_handler:
    type: Either[Error, Success]
    structure_preserved: true
    laws_verified:
      identity: true
      composition: true
    
    implementation_hint: |
      Biased functor (right-biased for success)
      
      def fmap(f: A -> B, either: Either[E, A]) -> Either[E, B]:
          match either:
              case Right(a): return Right(f(a))
              case Left(e): return Left(e)
```

### Pattern 6: State Management (State Functor)

**Signature:** `State[S, A]`

**Detects:**
- Stateful computation
- Session management
- Transactional operations

**Example:**
```
Input: Shopping cart with add/remove operations
Detected: State[Cart, Result]
```

**Functor Definition:**
```yaml
functors:
  state_handler:
    type: State[CartState, Order]
    structure_preserved: true
    laws_verified:
      identity: true
      composition: true
    
    implementation_hint: |
      Thread state through computation
      
      def fmap(f: A -> B, state: State[S, A]) -> State[S, B]:
          def run(s: S) -> (S, B):
              new_s, a = state.run(s)
              return (new_s, f(a))
          return State(run)
```

## Functor Composition

### Vertical Composition (Sequential)

**Pattern:** Apply functors in sequence

**Example:**
```yaml
composition:
  type: vertical
  functors:
    - Reader[TenantConfig, -]
    - IO[-]
    - Either[Error, -]
  
  result: Reader[TenantConfig, IO[Either[Error, Products]]]
  
  explanation: |
    1. Read tenant config (Reader)
    2. Perform async operation (IO)
    3. Handle errors (Either)
```

**Implementation:**
```python
def fetch_products(tenant: TenantConfig) -> IO[Either[Error, Products]]:
    async def inner():
        try:
            result = await api_call(tenant)
            return Right(result)
        except Exception as e:
            return Left(Error(str(e)))
    return IO(inner)
```

### Horizontal Composition (Parallel)

**Pattern:** Apply functors to independent components

**Example:**
```yaml
composition:
  type: horizontal
  functors:
    - platform_adapter: Platform -> IO[Products]
    - version_handler: Version -> Response
  
  parallelizable: true
  
  explanation: |
    Platform and version handlers are independent
    Can execute in parallel
```

**Implementation:**
```python
async def handle_request(platform: Platform, version: Version):
    # Execute in parallel
    products_task = platform_adapter(platform)
    response_task = version_handler(version)
    
    products, response = await asyncio.gather(products_task, response_task)
    return combine(products, response)
```

## Functor Law Verification

Every generated functor MUST satisfy:

### Law 1: Identity
`fmap id = id`

**Test:**
```python
def test_identity(functor, example_value):
    identity = lambda x: x
    assert functor.fmap(identity, example_value) == example_value
```

### Law 2: Composition
`fmap (g ∘ f) = fmap g ∘ fmap f`

**Test:**
```python
def test_composition(functor, f, g, example_value):
    # Left side: fmap (g ∘ f)
    composed = lambda x: g(f(x))
    left = functor.fmap(composed, example_value)
    
    # Right side: fmap g ∘ fmap f
    right = functor.fmap(g, functor.fmap(f, example_value))
    
    assert left == right
```

## Execution Steps

### Step 1: Load Validated ADT

```bash
ADT_FILE="artifacts/engineering/specifications/v{VERSION}/requirements.adt"
python {baseDir}/scripts/load_adt.py --file "$ADT_FILE"
```

### Step 2: Detect Patterns

```bash
python {baseDir}/scripts/detect_patterns.py \
  --adt "$ADT_FILE" \
  --patterns multi-tenant,optional,collections,async,error-handling,state \
  --output /tmp/detected-patterns.json
```

Expected output:
```json
{
  "patterns": [
    {
      "type": "multi-tenant",
      "confidence": 1.0,
      "evidence": ["Tenant appears in all paths"],
      "functor": "Reader[TenantConfig, -]"
    },
    {
      "type": "async",
      "confidence": 0.9,
      "evidence": ["API calls", "HTTP requests"],
      "functor": "IO[-]"
    }
  ]
}
```

### Step 3: Generate Functors

```bash
python {baseDir}/scripts/generate_functors.py \
  --patterns /tmp/detected-patterns.json \
  --adt "$ADT_FILE" \
  --output artifacts/engineering/specifications/v{VERSION}/architecture.categorical
```

### Step 4: Verify Functor Laws

```bash
python {baseDir}/scripts/verify_functor_laws.py \
  --functors artifacts/engineering/specifications/v{VERSION}/architecture.categorical \
  --iterations 1000 \
  --output artifacts/engineering/proofs/architecture/functor-laws/verification.json
```

Expected output:
```json
{
  "functors_checked": 3,
  "laws_verified": {
    "tenant_reader": {
      "identity": "PASS (1000/1000 tests)",
      "composition": "PASS (1000/1000 tests)"
    },
    "async_io": {
      "identity": "PASS (1000/1000 tests)",
      "composition": "PASS (1000/1000 tests)"
    },
    "error_handler": {
      "identity": "PASS (1000/1000 tests)",
      "composition": "PASS (1000/1000 tests)"
    }
  },
  "all_laws_satisfied": true
}
```

### Step 5: Plan Composition Strategy

```bash
python {baseDir}/scripts/plan_composition.py \
  --functors artifacts/engineering/specifications/v{VERSION}/architecture.categorical \
  --output artifacts/engineering/specifications/v{VERSION}/architecture.categorical
```

Appends composition strategy to categorical architecture:
```yaml
composition_strategy:
  vertical_composition:
    order: [Reader, IO, Either]
    result_type: "Reader[TenantConfig, IO[Either[Error, Products]]]"
  
  horizontal_composition:
    parallelizable_components:
      - platform_adapter
      - version_handler
    performance_gain: "2x speedup (parallel execution)"
```

## Output Format

```yaml
# artifacts/engineering/specifications/v{VERSION}/architecture.categorical

version: "v{VERSION}"
generated_at: "2025-01-15T10:30:00Z"

functors:
  tenant_reader:
    type: "Reader[TenantConfig, Service]"
    pattern: multi-tenant
    structure_preserved: true
    laws_verified:
      identity: true
      composition: true
    
    implementation_hint: |
      Pass tenant config implicitly through call chain
      Use closure or dependency injection
  
  async_io:
    type: "IO[Result]"
    pattern: async
    structure_preserved: true
    laws_verified:
      identity: true
      composition: true
    
    implementation_hint: |
      Wrap async operations in IO/Future monad
      Use async/await syntax
  
  error_handler:
    type: "Either[Error, Success]"
    pattern: error-handling
    structure_preserved: true
    laws_verified:
      identity: true
      composition: true
    
    implementation_hint: |
      Use Result/Either type for error handling
      Right-biased functor (success path)

composition_strategy:
  vertical_composition:
    order: [tenant_reader, async_io, error_handler]
    result_type: "Reader[TenantConfig, IO[Either[Error, Products]]]"
    explanation: |
      1. Inject tenant config (Reader)
      2. Perform async operation (IO)
      3. Handle errors (Either)
  
  horizontal_composition:
    parallelizable:
      - component: platform_adapter
        functor: "Platform → IO[Products]"
      - component: version_handler
        functor: "Version → Response"
    
    performance_optimization:
      strategy: "Parallel execution via asyncio.gather"
      expected_speedup: "2x (platform + version execute concurrently)"

optimization_opportunities:
  - pattern: "Tenant appears in all paths"
    optimization: "Factor out tenant handling, reuse across components"
    benefit: "58% code reduction (12 implementations → 5 components)"
```

## Success Criteria

Functors are complete when:

1. ✅ All patterns detected with confidence >0.7
2. ✅ Functors generated for each pattern
3. ✅ Identity law verified (1000/1000 tests)
4. ✅ Composition law verified (1000/1000 tests)
5. ✅ Composition strategy defined (vertical + horizontal)
6. ✅ Optimization opportunities identified

## Next Steps

After functor generation:
1. Pass to **natural-transformation-engine** for version migrations
2. Use in **curry-howard-prover** for type proofs
3. Apply in **system-optimizer** for optimization