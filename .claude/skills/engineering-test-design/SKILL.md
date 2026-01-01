---
name: test-design
description: Design test cases, analyze coverage gaps, generate test scaffolds. Use when writing new tests, improving coverage, or reviewing test quality.
allowed-tools: Read, Grep, Glob, Bash
---

# Test Design

Generate effective tests. Coverage analysis and test patterns.

## Type Signature

```
Design : CodeUnit → TestStrategy → [TestCase]

Where:
  CodeUnit     : Function | Class | Module | Endpoint
  TestStrategy : UnitTest | Integration | E2E | Property
  TestCase     : Input × Expected × Assertions × Edge
```

## When to Use

- Writing tests for new code
- Improving coverage on existing code
- Reviewing test quality
- Generating test scaffolds

## Test Hierarchy

```
Unit Tests (70%)
  └── Fast, isolated, mock dependencies
  
Integration Tests (20%)
  └── Real dependencies, database, external services
  
E2E Tests (10%)
  └── Full user flows, browser/API
```

## Test Case Generation

### 1. Identify Inputs

```yaml
function: validate_email(email: str) -> bool

inputs:
  valid:
    - "user@example.com"
    - "user.name+tag@sub.example.co.uk"
  invalid:
    - ""                    # Empty
    - "not-an-email"        # No @
    - "@example.com"        # No local part
    - "user@"               # No domain
    - "user@.com"           # Invalid domain
  edge:
    - "a@b.co"              # Minimum valid
    - "x" * 255 + "@a.com"  # Max length
    - "user@192.168.1.1"    # IP domain
```

### 2. Identify Branches

For each conditional, create test hitting both paths:

```python
# Code
def get_discount(user):
    if user.is_premium:
        return 0.2
    if user.orders > 10:
        return 0.1
    return 0

# Tests needed:
# - is_premium=True → 0.2
# - is_premium=False, orders>10 → 0.1
# - is_premium=False, orders<=10 → 0
```

### 3. Edge Cases Checklist

| Category | Cases |
|----------|-------|
| **Boundaries** | 0, 1, -1, max, max+1 |
| **Empty** | None, "", [], {} |
| **Types** | Wrong type, subtype |
| **Async** | Timeout, cancellation |
| **State** | Uninitialized, already done |
| **Concurrency** | Race, deadlock |

## Stack-Specific Patterns

### Python (pytest + FastAPI)

```python
# tests/test_auth.py
import pytest
from httpx import AsyncClient
from app.main import app

@pytest.fixture
async def client():
    async with AsyncClient(app=app, base_url="http://test") as ac:
        yield ac

@pytest.fixture
def valid_user():
    return {"email": "test@example.com", "password": "secure123"}

class TestLogin:
    async def test_login_success(self, client, valid_user):
        response = await client.post("/auth/login", json=valid_user)
        assert response.status_code == 200
        assert "access_token" in response.json()
    
    async def test_login_invalid_password(self, client, valid_user):
        valid_user["password"] = "wrong"
        response = await client.post("/auth/login", json=valid_user)
        assert response.status_code == 401
    
    @pytest.mark.parametrize("email", [
        "",
        "not-an-email",
        "missing@domain",
    ])
    async def test_login_invalid_email(self, client, email):
        response = await client.post("/auth/login", json={
            "email": email,
            "password": "any"
        })
        assert response.status_code == 422  # Validation error
```

**Fixtures in conftest.py:**

```python
# tests/conftest.py
import pytest
from sqlalchemy.ext.asyncio import create_async_engine, AsyncSession

@pytest.fixture(scope="session")
def event_loop():
    import asyncio
    loop = asyncio.get_event_loop_policy().new_event_loop()
    yield loop
    loop.close()

@pytest.fixture
async def db_session():
    engine = create_async_engine("sqlite+aiosqlite:///:memory:")
    async with AsyncSession(engine) as session:
        yield session
        await session.rollback()
```

### TypeScript/JavaScript (Vitest)

```typescript
// src/auth/auth.service.test.ts
import { describe, it, expect, vi, beforeEach } from 'vitest'
import { AuthService } from './auth.service'
import { UserRepository } from '../user/user.repository'

describe('AuthService', () => {
  let authService: AuthService
  let mockUserRepo: UserRepository

  beforeEach(() => {
    mockUserRepo = {
      findByEmail: vi.fn(),
      create: vi.fn(),
    } as unknown as UserRepository
    
    authService = new AuthService(mockUserRepo)
  })

  describe('login', () => {
    it('should return token for valid credentials', async () => {
      mockUserRepo.findByEmail.mockResolvedValue({
        id: '1',
        email: 'test@example.com',
        passwordHash: 'hashed',
      })

      const result = await authService.login('test@example.com', 'password')

      expect(result.accessToken).toBeDefined()
      expect(mockUserRepo.findByEmail).toHaveBeenCalledWith('test@example.com')
    })

    it('should throw for invalid password', async () => {
      mockUserRepo.findByEmail.mockResolvedValue({
        id: '1',
        email: 'test@example.com',
        passwordHash: 'different',
      })

      await expect(
        authService.login('test@example.com', 'wrong')
      ).rejects.toThrow('Invalid credentials')
    })

    it.each([
      ['', 'password'],
      ['not-email', 'password'],
      ['test@example.com', ''],
    ])('should reject invalid input: email=%s', async (email, password) => {
      await expect(
        authService.login(email, password)
      ).rejects.toThrow()
    })
  })
})
```

### Frontend (React + Testing Library)

```typescript
// src/components/LoginForm.test.tsx
import { render, screen, fireEvent, waitFor } from '@testing-library/react'
import userEvent from '@testing-library/user-event'
import { LoginForm } from './LoginForm'

describe('LoginForm', () => {
  const mockOnSubmit = vi.fn()

  beforeEach(() => {
    mockOnSubmit.mockClear()
  })

  it('should submit with valid data', async () => {
    render(<LoginForm onSubmit={mockOnSubmit} />)

    await userEvent.type(screen.getByLabelText(/email/i), 'test@example.com')
    await userEvent.type(screen.getByLabelText(/password/i), 'password123')
    await userEvent.click(screen.getByRole('button', { name: /login/i }))

    await waitFor(() => {
      expect(mockOnSubmit).toHaveBeenCalledWith({
        email: 'test@example.com',
        password: 'password123',
      })
    })
  })

  it('should show validation error for invalid email', async () => {
    render(<LoginForm onSubmit={mockOnSubmit} />)

    await userEvent.type(screen.getByLabelText(/email/i), 'not-an-email')
    await userEvent.click(screen.getByRole('button', { name: /login/i }))

    expect(await screen.findByText(/invalid email/i)).toBeInTheDocument()
    expect(mockOnSubmit).not.toHaveBeenCalled()
  })
})
```

## Coverage Analysis

### Find Uncovered Code

```bash
# Python
pytest --cov=src --cov-report=term-missing

# Vitest
npx vitest run --coverage
```

### Prioritize Coverage Gaps

| Priority | Criteria |
|----------|----------|
| **Critical** | Auth, payments, data mutations |
| **High** | Core business logic, public APIs |
| **Medium** | Internal utilities, helpers |
| **Low** | Config, constants, types |

### Coverage Commands

```bash
# Python: HTML report
pytest --cov=src --cov-report=html
open htmlcov/index.html

# Vitest: HTML report
npx vitest run --coverage --coverage.reporter=html
open coverage/index.html
```

## Test Scaffold Generation

**Input:** Function signature + docstring
**Output:** Test file with cases

```yaml
scaffold_request:
  file: "src/auth/token.py"
  function: "validate_token"
  signature: "(token: str, secret: str) -> TokenPayload"
  docstring: "Validates JWT token and returns payload. Raises InvalidTokenError."

scaffold_output:
  test_file: "tests/test_token.py"
  cases:
    - test_validate_token_success
    - test_validate_token_expired
    - test_validate_token_invalid_signature
    - test_validate_token_malformed
    - test_validate_token_empty
```

## Output Contract

```yaml
test_design:
  target:
    file: string
    unit: string  # function/class/endpoint
    
  strategy: "unit" | "integration" | "e2e"
  
  cases:
    - name: string
      description: string
      inputs: object
      expected: object
      assertions: [string]
      edge_case: boolean
      
  coverage:
    current: float?
    target: float
    gaps: [string]  # Uncovered lines/branches
    
  scaffold:
    file: string
    content: string  # Generated test code
```

## Quick Reference

| Task | Python | Vitest |
|------|--------|--------|
| Parameterized | `@pytest.mark.parametrize` | `it.each([])` |
| Async | `async def test_` | `async () => {}` |
| Mock | `unittest.mock` / `pytest-mock` | `vi.fn()` / `vi.mock()` |
| Fixture | `@pytest.fixture` | `beforeEach` |
| Skip | `@pytest.mark.skip` | `it.skip` |
| Only | `@pytest.mark.only` | `it.only` |
| Snapshot | `pytest-snapshot` | `expect().toMatchSnapshot()` |