---
name: python-excellence
description: Enforces production-quality Python standards. Use when writing, reviewing, or refactoring Python code. Triggers on python, fastapi, async, refactor, code review.
allowed-tools: Read, Edit, Write, Grep, Glob, Bash
---

## Purpose

Enforce high-quality Python code that is clear, performant, testable, and maintainable. Every piece of code should be production-ready from the start.

## When to Apply

- Writing new Python code
- Reviewing existing Python code
- Refactoring or optimizing
- Designing services or APIs
- Any FastAPI, async, or systems work

---

## Core Principles

### 1. Clarity Over Cleverness

```python
# ✅ One-liner when equally readable
users = [u for u in users if u.is_active]

# ❌ Clever but opaque
users = list(filter(lambda u: getattr(u, 'is_active', False), users))

# ✅ Explicit when complexity demands it
active_users = []
for user in users:
    if user.is_active and user.has_verified_email:
        active_users.append(user)
```

### 2. Async by Default

Use async for all I/O-bound operations. Sync only when forced by library constraints.

```python
# ✅ Async I/O
async def fetch_user(user_id: str) -> User:
    async with get_session() as session:
        return await session.get(User, user_id)

# ✅ Parallel independent operations
async def load_dashboard(user_id: str) -> Dashboard:
    user, orders, notifications = await asyncio.gather(
        fetch_user(user_id),
        fetch_orders(user_id),
        fetch_notifications(user_id),
    )
    return Dashboard(user=user, orders=orders, notifications=notifications)
```

### 3. Aggressive Modularization

Each function/class does one thing. If you're writing "and" in a description, split it.

```python
# ❌ Monolithic
def process_order(order_data: dict) -> Order:
    # validates, saves, notifies, logs... 200 lines

# ✅ Composed
async def process_order(order_data: dict) -> Order:
    validated = validate_order(order_data)
    order = await save_order(validated)
    await notify_fulfillment(order)
    return order
```

### 4. Self-Documenting Code

Names should eliminate the need for comments.

```python
# ❌ Needs comment
def calc(a, b, t):  # Calculate discounted price with tax
    return (a - (a * b)) * (1 + t)

# ✅ Self-evident
def calculate_final_price(
    base_price: Decimal,
    discount_rate: Decimal,
    tax_rate: Decimal,
) -> Decimal:
    discounted = base_price * (1 - discount_rate)
    return discounted * (1 + tax_rate)
```

### 5. Dependency Injection

Never hardcode dependencies. Inject them for testability.

```python
# ❌ Hardcoded
class OrderService:
    def __init__(self):
        self.repo = PostgresOrderRepository()
        self.notifier = EmailNotifier()

# ✅ Injected
class OrderService:
    def __init__(
        self,
        repo: OrderRepository,
        notifier: Notifier,
    ):
        self.repo = repo
        self.notifier = notifier
```

### 6. Fail Fast, Log Clearly

Use structured logging. Errors should be immediately obvious.

```python
import structlog

logger = structlog.get_logger()

async def charge_customer(customer_id: str, amount: Decimal) -> Payment:
    logger.info("charging_customer", customer_id=customer_id, amount=str(amount))
    
    if amount <= 0:
        raise ValueError(f"Invalid charge amount: {amount}")
    
    try:
        payment = await payment_gateway.charge(customer_id, amount)
        logger.info("charge_succeeded", payment_id=payment.id)
        return payment
    except PaymentError as e:
        logger.error("charge_failed", customer_id=customer_id, error=str(e))
        raise
```

---

## Performance Guidelines

### Profile Before Optimizing

```bash
# Use cProfile for CPU-bound
python -m cProfile -s cumtime your_script.py

# Use pyinstrument for readable output
pyinstrument your_script.py
```

### Database Access

```python
# ✅ Connection pooling
engine = create_async_engine(
    DATABASE_URL,
    pool_size=20,
    max_overflow=10,
    pool_pre_ping=True,
)

# ✅ Bulk operations
async def upsert_users(users: list[User]) -> None:
    async with get_session() as session:
        await session.execute(
            insert(UserModel)
            .values([u.model_dump() for u in users])
            .on_conflict_do_update(...)
        )
        await session.commit()

# ❌ N+1 queries
for order in orders:
    order.customer = await fetch_customer(order.customer_id)

# ✅ Eager loading
orders = await session.execute(
    select(Order).options(selectinload(Order.customer))
)
```

### Batch I/O Operations

```python
# ❌ Sequential
for event in events:
    await nats.publish("events", event)

# ✅ Batched
await asyncio.gather(*[
    nats.publish("events", event) for event in events
])
```

### Intelligent Caching

```python
from functools import lru_cache
from cachetools import TTLCache

# In-memory for CPU-bound pure functions
@lru_cache(maxsize=1024)
def compute_hash(data: str) -> str:
    return hashlib.sha256(data.encode()).hexdigest()

# TTL cache for external calls
_rate_cache = TTLCache(maxsize=100, ttl=300)

async def get_exchange_rate(currency: str) -> Decimal:
    if currency in _rate_cache:
        return _rate_cache[currency]
    rate = await fetch_rate_from_api(currency)
    _rate_cache[currency] = rate
    return rate
```

### Concurrency Control

```python
# ✅ Bounded concurrency to avoid oversubscription
semaphore = asyncio.Semaphore(10)

async def fetch_with_limit(url: str) -> Response:
    async with semaphore:
        return await http_client.get(url)

results = await asyncio.gather(*[
    fetch_with_limit(url) for url in urls
])
```

---

## Style Enforcement

### Black + Ruff Pipeline

```toml
# pyproject.toml
[tool.black]
line-length = 88
target-version = ["py311"]

[tool.ruff]
line-length = 88
select = ["E", "F", "I", "N", "W", "UP", "B", "C4", "SIM"]
ignore = ["E501"]  # Black handles line length

[tool.ruff.isort]
known-first-party = ["your_package"]
```

```bash
# Pre-commit or CI
black --check .
ruff check .
```

Never manually adjust formatting. Let Black handle it.

---

## Type Hints

Always use type hints. No exceptions.

```python
from typing import Protocol, TypeVar
from collections.abc import Callable, Awaitable

T = TypeVar("T")

# ✅ Complete signatures
async def retry(
    fn: Callable[[], Awaitable[T]],
    max_attempts: int = 3,
    delay: float = 1.0,
) -> T:
    ...

# ✅ Protocol for duck typing
class Repository(Protocol[T]):
    async def get(self, id: str) -> T | None: ...
    async def save(self, entity: T) -> T: ...
```

---

## Error Handling

```python
# ✅ Domain exceptions
class DomainError(Exception):
    """Base for all domain errors."""

class OrderNotFoundError(DomainError):
    def __init__(self, order_id: str):
        self.order_id = order_id
        super().__init__(f"Order not found: {order_id}")

# ✅ Explicit error boundaries
async def get_order(order_id: str) -> Order:
    order = await repo.get(order_id)
    if not order:
        raise OrderNotFoundError(order_id)
    return order

# ✅ FastAPI exception handlers
@app.exception_handler(DomainError)
async def domain_error_handler(request: Request, exc: DomainError):
    return JSONResponse(
        status_code=400,
        content={"error": exc.__class__.__name__, "detail": str(exc)},
    )
```

---

## Anti-Patterns to Reject

| Pattern | Problem | Fix |
|---------|---------|-----|
| `except Exception: pass` | Swallows errors silently | Catch specific, log, re-raise |
| Global mutable state | Untestable, race conditions | Inject dependencies |
| `time.sleep()` in async | Blocks event loop | Use `asyncio.sleep()` |
| String concatenation for SQL | SQL injection | Use parameterized queries |
| `from module import *` | Pollutes namespace | Explicit imports |
| Nested try/except blocks | Hard to follow | Flatten, use context managers |
| Magic numbers/strings | Unclear intent | Named constants |

---

## Output Expectations

When generating Python code:

1. **Type hints on all signatures** — no exceptions
2. **Async for I/O** — sync only when library forces it
3. **Dependency injection** — no hardcoded dependencies
4. **Structured logging** — no print statements
5. **Domain exceptions** — no generic Exception raises
6. **Black-compliant formatting** — 88 char lines
7. **Docstrings only where non-obvious** — code should speak

---

## Boundaries

This skill does **not** cover:
- Framework-specific patterns (see dedicated FastAPI/Django skills)
- Infrastructure/deployment concerns
- Database schema design
- API contract design

Focus: Writing excellent Python code at the function/class/module level.