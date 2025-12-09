---
name: code-implementation-generator
description: Generate production Python code from verified maps. Mechanical transformation (maps → code) using skeleton patterns. Generates services, types, composition utilities, state machines, tests (~5000+ lines). Sub-skill of backend-prover Phase 2.
version: 1.0.0
allowed-tools: bash_tool, create_file, view, str_replace
model: claude-sonnet-4-20250514
license: Proprietary - LeanOS Engineering Layer
---

# code-implementation-generator: Maps → Production Code

## Purpose

Generate production-ready Python code from verified maps. This is a **mechanical transformation** - no creative decisions, just map-to-code translation.

**Input:** Verified maps (~300 lines)  
**Output:** Production code (~5000+ lines)  
**Process:** Deterministic transformation

---

## Pre-check: Gate Must Pass

```bash
validation_status=$(jq -r '.status' artifacts/engineering/proofs/backend/map-validation/validation-report.json)

if [ "$validation_status" != "valid" ]; then
    echo "ERROR: Maps not validated. Run composition-map-validator first."
    exit 1
fi

echo "✓ Maps validated. Proceeding with code generation..."
```

---

## Input

**Verified maps:**
```
artifacts/engineering/maps/backend/
├── services/*.map.yaml
├── types.map.yaml
├── composition.map.yaml
├── effects.map.yaml
└── state-machines.map.yaml
```

**Skeleton patterns (embedded in context):**
- Document #2: Complete service skeleton
- Document #3: Skeleton patterns and shared dependencies

---

## Generation Process

### Step 1: Generate Type Definitions

**Input:** `types.map.yaml`  
**Output:** `artifacts/engineering/code/backend/types.py`

```python
# Generated header
"""
Generated from: artifacts/engineering/maps/backend/types.map.yaml
Specification version: v1.2.0
Generated at: 2025-01-15T10:30:00Z

DO NOT EDIT MANUALLY - Regenerate from maps
"""

from dataclasses import dataclass
from uuid import UUID
from typing import List, Optional
from decimal import Decimal
from enum import Enum

# Generate from types.map.yaml
@dataclass
class Tenant:
    """Multi-tenant context"""
    id: UUID
    config: 'TenantConfig'

@dataclass
class Product:
    """Product entity"""
    id: UUID
    title: str
    price: Decimal
    status: 'ProductStatus'

@dataclass
class Products:
    """Product collection"""
    items: List[Product]
    total: int
    cursor: Optional[str] = None

class ProductStatus(Enum):
    """Product status enum"""
    ACTIVE = "active"
    DRAFT = "draft"
    ARCHIVED = "archived"
```

**Generation rules:**
- One class per type in types.map.yaml
- Use `@dataclass` for Product types
- Use `Enum` for Sum types
- Include docstrings from map descriptions
- Add forward references for circular dependencies

---

### Step 2: Generate Service Classes

**Input:** `services/*.map.yaml` + skeleton patterns  
**Output:** `artifacts/engineering/code/backend/services/{service}.py`

**Service structure (from Document #2):**
```python
"""
Generated from: artifacts/engineering/maps/backend/services/catalog_service.map.yaml
Specification version: v1.2.0
Composition verified: true
"""

from sqlalchemy.ext.asyncio import async_sessionmaker, AsyncSession
from shared.observability import ServiceTracer, ServiceMetrics
from shared.utils.logger import ServiceLogger

from ..repositories.catalog_repository import CatalogRepository
from ..schemas.catalog import ProductCreateIn, ProductOut
from ..events.publishers import CatalogEventPublisher
from ..exceptions import ProductNotFoundError

class CatalogService:
    """
    Multi-tenant {domain} data synchronization
    
    Dependencies (from map):
    - db: DatabaseConnection
    - cache: RedisConnection
    - platform_adapter: PlatformAdapter
    """
    
    def __init__(
        self,
        session_factory: async_sessionmaker[AsyncSession],
        cache: RedisConnection,
        platform_adapter: PlatformAdapter,
        publisher: CatalogEventPublisher,
        logger: ServiceLogger,
        tracer: ServiceTracer,
        metrics: ServiceMetrics
    ):
        self.session_factory = session_factory
        self.cache = cache
        self.platform_adapter = platform_adapter
        self.publisher = publisher
        self.logger = logger
        self.tracer = tracer
        self.metrics = metrics
    
    async def sync_products(
        self,
        tenant: Tenant,
        platform: Platform,
        ctx  # RequestContext
    ) -> IO[Either[Error, Products]]:
        """
        Fetches products from platform API, transforms to canonical format,
        saves to tenant database. Composition of 3 morphisms with IO effects.
        Guarantees atomicity through transaction management.
        
        Composition (from map):
          1. platform_adapter.fetch_products: Platform → IO[Either[Error, RawProducts]]
          2. transform_products: RawProducts → Products
          3. db.save_products: Products → IO[Either[Error, Unit]]
        
        Effects: [http, database, cache]
        Error handling:
          - {Platform}APIError: retry_3x_exponential
          - DatabaseError: rollback_transaction
          - ValidationError: return_left
          - NetworkError: circuit_breaker
        """
        
        with self.tracer.start_span("sync_products"):
            self.metrics.increment("sync_products_called")
            
            # Step 1: Platform → IO[Either[Error, RawProducts]]
            try:
                raw_products_result = await self.platform_adapter.fetch_products(
                    platform,
                    retry_policy="exponential_backoff_3x",
                    timeout=30
                )
            except {Platform}APIError as e:
                self.logger.error("API fetch failed", exc_info=True)
                return Left(e)
            except NetworkError as e:
                # Circuit breaker pattern
                if self.circuit_breaker.is_open():
                    return Left(ServiceUnavailableError())
                return Left(e)
            
            if raw_products_result.is_left():
                return raw_products_result  # Short-circuit on error
            
            raw_products = raw_products_result.value
            
            # Step 2: RawProducts → Products (pure function)
            try:
                products = self.transform_products(raw_products)
            except ValidationError as e:
                self.logger.warning("Transform validation failed", extra={"error": str(e)})
                return Left(e)
            
            # Step 3: Products → IO[Either[Error, Unit]]
            async with self.session_factory() as session:
                async with session.begin():
                    try:
                        await session.execute(
                            insert(products_table).values([p.dict() for p in products.items])
                        )
                        await session.commit()
                    except DatabaseError as e:
                        await session.rollback()
                        self.logger.error("Database save failed", exc_info=True)
                        return Left(e)
            
            self.metrics.increment("sync_products_success")
            return Right(products)
    
    def transform_products(self, raw: RawProducts) -> Products:
        """
        Transform raw platform products to canonical format.
        
        Morphism: RawProducts → Products
        Pure function (no effects)
        """
        return Products(
            items=[self._transform_product(p) for p in raw.items],
            total=raw.total,
            cursor=raw.next_cursor
        )
```

**Key generation rules:**
- Class structure matches service map exactly
- Dependencies from map → `__init__` parameters
- Methods from map → class methods
- Composition steps from map → method implementation
- Error handling from map → try/except blocks
- Effects from map → actual IO operations
- Documentation from map → docstrings

---

### Step 3: Generate Composition Utilities

**Input:** `composition.map.yaml`  
**Output:** `artifacts/engineering/code/backend/composition.py`

```python
"""
Generated from: artifacts/engineering/maps/backend/composition.map.yaml
Composition utilities for sequential and parallel execution
"""

import asyncio
from typing import Callable, List, TypeVar, Union
from functools import wraps

A = TypeVar('A')
B = TypeVar('B')
C = TypeVar('C')

async def sequential_composition(
    f: Callable[[A], B],
    g: Callable[[B], C],
    x: A
) -> C:
    """
    Execute composition sequentially: g(f(x))
    
    Guarantees: (g ∘ f)(x) = g(f(x))
    """
    b = await f(x)
    c = await g(b)
    return c

async def parallel_composition(funcs: List[Callable]) -> List:
    """
    Execute functions in parallel
    
    Use for independent operations only
    """
    return await asyncio.gather(*[f() for f in funcs])

def compose(*funcs):
    """
    Compose multiple functions: f1 ∘ f2 ∘ ... ∘ fn
    """
    def composed(x):
        result = x
        for f in reversed(funcs):
            result = f(result)
        return result
    return composed
```

---

### Step 4: Generate State Machines

**Input:** `state-machines.map.yaml`  
**Output:** `artifacts/engineering/code/backend/state_machines/{machine}.py`

```python
"""
Generated from: artifacts/engineering/maps/backend/state-machines.map.yaml
PaymentFlow state machine
"""

from enum import Enum
from dataclasses import dataclass
from typing import Optional

class PaymentFlowState(Enum):
    """Payment processing states"""
    PENDING = "pending"
    PROCESSING = "processing"
    COMPLETED = "completed"
    FAILED = "failed"
    REFUNDED = "refunded"

@dataclass
class PaymentFlow:
    """
    Payment processing state machine
    
    States: pending, processing, completed, failed, refunded
    Initial: pending
    Terminal: [completed, failed, refunded]
    """
    
    state: PaymentFlowState
    payment_id: str
    amount: Decimal
    
    def __init__(self, payment_id: str, amount: Decimal):
        self.state = PaymentFlowState.PENDING
        self.payment_id = payment_id
        self.amount = amount
    
    def start_payment(self, payment_method: PaymentMethod):
        """
        Transition: pending → processing
        Guard: has_valid_payment_method
        """
        if self.state != PaymentFlowState.PENDING:
            raise InvalidTransitionError(f"Cannot start from {self.state}")
        
        if not self._has_valid_payment_method(payment_method):
            raise GuardViolationError("Invalid payment method")
        
        self.state = PaymentFlowState.PROCESSING
    
    def payment_success(self):
        """Transition: processing → completed"""
        if self.state != PaymentFlowState.PROCESSING:
            raise InvalidTransitionError(f"Cannot complete from {self.state}")
        
        self.state = PaymentFlowState.COMPLETED
    
    def payment_failure(self, reason: str):
        """Transition: processing → failed"""
        if self.state != PaymentFlowState.PROCESSING:
            raise InvalidTransitionError(f"Cannot fail from {self.state}")
        
        self.state = PaymentFlowState.FAILED
    
    def initiate_refund(self):
        """
        Transition: completed → refunded
        Guard: within_refund_window
        """
        if self.state != PaymentFlowState.COMPLETED:
            raise InvalidTransitionError(f"Cannot refund from {self.state}")
        
        if not self._within_refund_window():
            raise GuardViolationError("Refund window expired")
        
        self.state = PaymentFlowState.REFUNDED
    
    def _has_valid_payment_method(self, pm: PaymentMethod) -> bool:
        """Guard implementation"""
        return pm.is_valid()
    
    def _within_refund_window(self) -> bool:
        """Guard implementation"""
        # Check refund policy
        return True
```

---

### Step 5: Generate Tests

**Input:** Test specifications from service maps  
**Output:** `artifacts/engineering/code/backend/tests/**/*.py`

```python
"""
Generated from: artifacts/engineering/maps/backend/services/catalog_service.map.yaml
Unit tests for CatalogService
"""

import pytest
from hypothesis import given, strategies as st

from ..services.catalog_service import CatalogService
from ..types import Tenant, Platform, Products

@pytest.mark.asyncio
async def test_sync_products_success():
    """For valid tenant and platform, returns Products"""
    # Arrange
    service = create_catalog_service()
    tenant = create_test_tenant()
    platform = Platform.SHOPIFY
    
    # Act
    result = await service.sync_products(tenant, platform, ctx)
    
    # Assert
    assert result.is_right()
    assert isinstance(result.value, Products)

@pytest.mark.asyncio
async def test_sync_products_api_failure():
    """{Platform}APIError triggers retry with exponential backoff"""
    # Test implementation
    pass

@pytest.mark.asyncio
async def test_sync_products_db_failure():
    """DatabaseError triggers rollback"""
    # Test implementation
    pass

# Property-based test for composition law
@given(
    tenant=st.from_type(Tenant),
    platform=st.sampled_from(Platform)
)
@pytest.mark.asyncio
async def test_composition_associativity(tenant, platform):
    """
    Verify composition associativity:
    (save ∘ transform ∘ fetch)(x) = save(transform(fetch(x)))
    """
    # Property test implementation
    pass
```

---

## Output Structure

```
artifacts/engineering/code/backend/
├── services/
│   ├── __init__.py
│   ├── catalog_service.py          (~400 lines)
│   ├── billing_service.py          (~350 lines)
│   └── auth_service.py             (~300 lines)
│
├── types.py                         (~200 lines)
├── composition.py                   (~150 lines)
│
├── state_machines/
│   ├── __init__.py
│   ├── payment_flow.py             (~180 lines)
│   └── order_flow.py               (~160 lines)
│
├── effects/
│   ├── __init__.py
│   ├── io.py                       (~120 lines)
│   ├── errors.py                   (~100 lines)
│   └── handlers.py                 (~140 lines)
│
└── tests/
    ├── unit/
    │   ├── test_catalog_service.py (~300 lines)
    │   └── test_billing_service.py (~280 lines)
    │
    ├── integration/
    │   └── test_{domain}_sync.py    (~200 lines)
    │
    └── properties/
        └── test_composition_laws.py (~250 lines)

Total: ~5000+ lines
```

---

## Generation Metadata

Each generated file includes header:

```python
"""
Generated from: artifacts/engineering/maps/backend/services/catalog_service.map.yaml
Specification version: v1.2.0
Map verification: PASSED
Composition verified: true
Generated at: 2025-01-15T10:30:00Z

DO NOT EDIT MANUALLY - Regenerate from maps

This code is mechanically generated from verified maps.
Changes to maps will regenerate this file.
"""
```

---

## Success Criteria

✓ All services from maps have Python implementations
✓ Generated code structure matches map structure exactly
✓ Type signatures match map signatures
✓ Composition order preserved from maps
✓ Effects declared match effects used
✓ Error handling follows map strategies
✓ Documentation generated from maps
✓ Tests generated from map specifications
✓ ~5000+ lines generated

---

## Next Step

After code generated, invoke `runtime-monitor-generator` to inject runtime verification guards.

---

## Key Insights

1. **Generation is mechanical** - No creative decisions
2. **Maps are source of truth** - Code follows maps exactly
3. **Skeleton patterns applied** - Shared dependencies from Document #3
4. **Generated code is correct by construction** - Maps already verified
5. **Regeneration is safe** - Deterministic transformation

**Code generation speed:** ~5 seconds for 5000+ lines