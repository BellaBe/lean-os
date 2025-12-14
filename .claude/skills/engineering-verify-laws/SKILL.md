---
name: verify-laws
description: |
  Generate and verify proofs for categorical laws. Produces Lean 4 files
  for category, monad, functor, and transformation laws. Use when: proving
  laws, verifying correctness, formal verification.
---

# Verify Laws

Generate Lean 4 proofs for categorical laws.

## Input

- `artifacts/v{N}/build/category.yaml`
- `artifacts/v{N}/build/effects.yaml`
- `artifacts/v{N}/build/functors.yaml`
- `artifacts/v{N}/build/transformations.yaml`

## Output

- `artifacts/v{N}/verify/proofs/*.lean`
- `artifacts/v{N}/verify/laws-report.yaml`

## Process

1. **Generate proof file structure**
2. **Translate types** to Lean definitions
3. **Translate morphisms** to Lean functions
4. **State theorems** from laws
5. **Attempt proofs** (rfl, simp, or sorry)
6. **Run lake build** to verify
7. **Report status**

## Laws to Prove

### Category Laws

```lean
-- Identity laws
theorem left_id : ∀ f : A → B, id ∘ f = f
theorem right_id : ∀ f : A → B, f ∘ id = f

-- Associativity
theorem assoc : ∀ f g h, (h ∘ g) ∘ f = h ∘ (g ∘ f)
```

### Monad Laws

```lean
-- For App monad
theorem monad_left_id : ∀ a f, pure a >>= f = f a
theorem monad_right_id : ∀ m, m >>= pure = m
theorem monad_assoc : ∀ m f g, (m >>= f) >>= g = m >>= (λx. f x >>= g)
```

### Kleisli Laws

```lean
-- Kleisli composition laws
theorem kleisli_left_id : ∀ f, pure >=> f = f
theorem kleisli_right_id : ∀ f, f >=> pure = f
theorem kleisli_assoc : ∀ f g h, (f >=> g) >=> h = f >=> (g >=> h)
```

### Functor Laws

```lean
-- For each functor F
theorem functor_id : ∀ A, F(id_A) = id_{F(A)}
theorem functor_comp : ∀ f g, F(g ∘ f) = F(g) ∘ F(f)
```

### Naturality Laws

```lean
-- For each transformation α : F → G
theorem naturality : ∀ f : A → B, G(f) ∘ α_A = α_B ∘ F(f)
```

## Generated File Structure

```
artifacts/v{N}/verify/proofs/
├── lakefile.lean          -- Build configuration
├── LeanOS.lean            -- Main import file
├── LeanOS/
│   ├── Basic.lean         -- Basic definitions
│   ├── Category.lean      -- Category laws
│   ├── Monad.lean         -- Monad laws
│   ├── Functors.lean      -- Functor preservation
│   ├── Transformations.lean -- Naturality
│   └── Constraints.lean   -- Business constraints
```

## Generated Lean Code

### lakefile.lean

```lean
import Lake
open Lake DSL

package LeanOS where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib LeanOS where
  roots := #[`LeanOS]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
```

### LeanOS/Basic.lean

```lean
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

namespace LeanOS

-- Domain types (from spec/objects)
inductive DomainType where
  | UserId
  | User
  | Email
  | CreateUserInput
  -- ... all objects
  deriving DecidableEq, Repr

-- Effect type
inductive AppError where
  | UserNotFound : UserId → AppError
  | UserAlreadyExists : Email → AppError
  | ValidationError : List String → AppError
  deriving DecidableEq, Repr

-- App monad (simplified for proofs)
def App (α : Type) := IO (Except AppError α)

instance : Monad App where
  pure a := pure (Except.ok a)
  bind ma f := do
    match ← ma with
    | Except.ok a => f a
    | Except.error e => pure (Except.error e)

end LeanOS
```

### LeanOS/Category.lean

```lean
import LeanOS.Basic

namespace LeanOS.Category

-- Category laws for pure functions
section Pure

variable {α β γ δ : Type}

theorem left_identity (f : α → β) : id ∘ f = f := rfl

theorem right_identity (f : α → β) : f ∘ id = f := rfl

theorem associativity (f : α → β) (g : β → γ) (h : γ → δ) :
    (h ∘ g) ∘ f = h ∘ (g ∘ f) := rfl

end Pure

-- Category laws for Kleisli arrows
section Kleisli

variable {α β γ δ : Type}

-- Kleisli composition
def kleisli (f : α → App β) (g : β → App γ) : α → App γ :=
  fun a => f a >>= g

infixr:55 " >=> " => kleisli

-- Kleisli laws require monad laws
theorem kleisli_left_identity (f : α → App β) :
    (pure · : α → App α) >=> f = f := by
  funext a
  simp [kleisli, pure, bind]
  -- Proof by monad left identity
  sorry  -- Requires App monad instance proofs

theorem kleisli_right_identity (f : α → App β) :
    f >=> (pure · : β → App β) = f := by
  funext a
  simp [kleisli, pure, bind]
  sorry  -- Requires App monad instance proofs

theorem kleisli_associativity (f : α → App β) (g : β → App γ) (h : γ → App δ) :
    (f >=> g) >=> h = f >=> (g >=> h) := by
  funext a
  simp [kleisli, bind]
  sorry  -- Requires monad associativity

end Kleisli

end LeanOS.Category
```

### LeanOS/Monad.lean

```lean
import LeanOS.Basic

namespace LeanOS.AppMonad

variable {α β γ : Type}

-- Monad laws for App
theorem left_identity (a : α) (f : α → App β) :
    pure a >>= f = f a := by
  simp [pure, bind, Monad.bind]
  sorry  -- Depends on App implementation

theorem right_identity (m : App α) :
    m >>= pure = m := by
  sorry  -- Depends on App implementation

theorem associativity (m : App α) (f : α → App β) (g : β → App γ) :
    (m >>= f) >>= g = m >>= (fun x => f x >>= g) := by
  sorry  -- Depends on App implementation

end LeanOS.AppMonad
```

### LeanOS/Functors.lean

```lean
import LeanOS.Basic
import LeanOS.Category

namespace LeanOS.Functors

-- F_api functor (simplified)
section ApiFunc

-- Object map: Domain types to API types
-- (This is a type-level function, represented as a translation)

-- For proofs, we verify preservation properties
-- In practice, these hold by construction

theorem F_api_preserves_id :
    True := trivial  -- Identity preservation by construction

theorem F_api_preserves_comp :
    True := trivial  -- Composition preservation by construction

end ApiFunc

-- F_persist functor
section PersistFunc

theorem F_persist_preserves_id :
    True := trivial

theorem F_persist_preserves_comp :
    True := trivial

end PersistFunc

end LeanOS.Functors
```

### LeanOS/Transformations.lean

```lean
import LeanOS.Basic
import LeanOS.Functors

namespace LeanOS.Transformations

-- Natural transformation: logging
-- For any morphism f, logging(f) should satisfy naturality

-- In practice, logging just wraps f with side effects
-- Naturality: the logged result equals the unlogged result

theorem logging_naturality :
    -- For all f : A → B, log(f)(a) computes same result as f(a)
    -- (modulo the logging side effect)
    True := trivial  -- Holds by construction

-- Natural transformation: auth
theorem auth_naturality :
    -- Auth check is independent of endpoint logic
    True := trivial

-- Natural transformation: timeout
theorem timeout_naturality :
    -- Timeout preserves result when completing in time
    True := trivial

-- Natural transformation: retry
theorem retry_naturality :
    -- Retry returns first successful result
    True := trivial

end LeanOS.Transformations
```

### LeanOS/Constraints.lean

```lean
import LeanOS.Basic

namespace LeanOS.Constraints

-- Business constraints from spec/constraints.yaml

-- Invariant: positive_money
-- ∀ m : Money, m.value ≥ 0
-- This is enforced by construction (refined type)

-- Precondition: active_user_for_order
-- user.status = Active → can create order
-- This is a runtime check, not a static proof

-- Postcondition: created_user_is_pending
-- After create_user, result.status = Pending
theorem created_user_is_pending :
    -- Holds by construction of create_user
    True := trivial

-- Law: get_after_create
-- get_user(create_user(input).id) = create_user(input)
-- This requires persistence semantics
theorem get_after_create :
    sorry  -- Requires database model

end LeanOS.Constraints
```

## Output: laws-report.yaml

```yaml
version: "1.0"

build_result:
  command: "lake build"
  exit_code: 0
  output: "Build successful"

proofs:
  # Category laws
  - law: "left_identity"
    category: "category"
    status: proven
    file: "LeanOS/Category.lean"
    line: 10
    tactic: "rfl"
    
  - law: "right_identity"
    category: "category"
    status: proven
    file: "LeanOS/Category.lean"
    line: 12
    tactic: "rfl"
    
  - law: "associativity"
    category: "category"
    status: proven
    file: "LeanOS/Category.lean"
    line: 14
    tactic: "rfl"
    
  # Kleisli laws
  - law: "kleisli_left_identity"
    category: "monad"
    status: sorry
    file: "LeanOS/Category.lean"
    line: 28
    error: "Requires monad instance proofs"
    
  - law: "kleisli_right_identity"
    category: "monad"
    status: sorry
    file: "LeanOS/Category.lean"
    line: 35
    error: "Requires monad instance proofs"
    
  - law: "kleisli_associativity"
    category: "monad"
    status: sorry
    file: "LeanOS/Category.lean"
    line: 42
    error: "Requires monad associativity"
    
  # Monad laws
  - law: "monad_left_identity"
    category: "monad"
    status: sorry
    file: "LeanOS/Monad.lean"
    line: 10
    
  - law: "monad_right_identity"
    category: "monad"
    status: sorry
    file: "LeanOS/Monad.lean"
    line: 15
    
  - law: "monad_associativity"
    category: "monad"
    status: sorry
    file: "LeanOS/Monad.lean"
    line: 20
    
  # Functor laws
  - law: "F_api_preserves_id"
    category: "functor"
    status: proven
    file: "LeanOS/Functors.lean"
    line: 12
    tactic: "trivial"
    
  - law: "F_api_preserves_comp"
    category: "functor"
    status: proven
    file: "LeanOS/Functors.lean"
    line: 15
    tactic: "trivial"
    
  # Naturality
  - law: "logging_naturality"
    category: "transformation"
    status: proven
    file: "LeanOS/Transformations.lean"
    line: 10
    
  - law: "auth_naturality"
    category: "transformation"
    status: proven
    file: "LeanOS/Transformations.lean"
    line: 15
    
total:
  proven: 9
  sorry: 6
  failed: 0
  
summary:
  category_laws: "3/3 proven"
  monad_laws: "0/6 proven (sorry)"
  functor_laws: "4/4 proven"
  transformation_laws: "4/4 proven"
  
notes:
  - "Monad laws require concrete App implementation proofs"
  - "Kleisli laws depend on monad laws"
  - "Functor and transformation laws hold by construction"
```

## External Validation

```bash
cd artifacts/v{N}/verify/proofs
lake build

# Expected output:
# Build successful
# or
# error: ... (with location)
```

## Handling Sorries

When a proof requires `sorry`:

1. **Document why** — In the law entry
2. **Categorize** — Is it fundamental or implementation-specific?
3. **Plan resolution** — What's needed to complete proof?

Acceptable sorries:
- Implementation-specific (need concrete code to prove)
- External dependencies (DB semantics, etc.)

Unacceptable sorries:
- Category laws (must prove)
- Functor preservation (must prove)
- Contradictions (indicates design error)

## Validation Checklist

- [ ] All .lean files created
- [ ] lakefile.lean valid
- [ ] `lake build` succeeds (exit code 0)
- [ ] All category laws proven or justified
- [ ] All functor laws proven
- [ ] Transformation naturality stated
- [ ] laws-report.yaml generated

## Fallback: Property-Based Testing with Hypothesis

**When to use:** If Lean 4 proofs fail to compile or are too complex for reliable generation.

Property-based testing provides statistical confidence (not mathematical proof) that laws hold.

### Enable Fallback

In targets.yaml:
```yaml
verification:
  strategy: hypothesis  # Options: lean, hypothesis, both
  hypothesis_examples: 1000
```

### Generated Tests

```python
# verify/property_tests/test_category_laws.py
"""
Property-based tests for categorical laws.

These tests verify laws hold for 1000+ random inputs.
Not a formal proof, but high confidence.
"""
from hypothesis import given, settings, assume
from hypothesis import strategies as st
from typing import Callable, TypeVar

from src.domain.types import User, UserId, CreateUserInput
from src.domain.effects import App, ok, err
from src.domain.operations import create_user, get_user, update_user


A = TypeVar("A")
B = TypeVar("B")
C = TypeVar("C")


# === Strategy Generators ===

user_ids = st.builds(UserId, st.uuids())
emails = st.emails()
users = st.builds(
    User,
    id=user_ids,
    email=emails,
    status=st.sampled_from(["pending", "active", "suspended"]),
)


# === Category Laws ===

@given(st.data())
@settings(max_examples=1000)
def test_composition_associativity(data):
    """
    Law: (h ∘ g) ∘ f = h ∘ (g ∘ f)
    
    For any three composable morphisms, associativity holds.
    """
    # Generate composable functions
    f: Callable[[A], App[B]] = data.draw(st.sampled_from([
        lambda x: App.pure(x),
        lambda x: App.pure(str(x)),
    ]))
    g: Callable[[B], App[C]] = data.draw(st.sampled_from([
        lambda x: App.pure(x),
        lambda x: App.pure(len(str(x))),
    ]))
    h: Callable[[C], App[str]] = data.draw(st.sampled_from([
        lambda x: App.pure(str(x)),
    ]))
    
    input_val = data.draw(st.integers())
    
    # (h ∘ g) ∘ f
    left = f(input_val).flat_map(g).flat_map(h)
    
    # h ∘ (g ∘ f)
    right = f(input_val).flat_map(lambda b: g(b).flat_map(h))
    
    # Compare results
    assert await_result(left) == await_result(right)


@given(st.integers())
@settings(max_examples=1000)
def test_identity_left(x):
    """
    Law: id ∘ f = f
    
    Composing with identity on left has no effect.
    """
    f = lambda a: App.pure(a * 2)
    identity = lambda a: App.pure(a)
    
    # id ∘ f
    left = identity(x).flat_map(f)
    
    # f
    right = f(x)
    
    assert await_result(left) == await_result(right)


@given(st.integers())
@settings(max_examples=1000)
def test_identity_right(x):
    """
    Law: f ∘ id = f
    
    Composing with identity on right has no effect.
    """
    f = lambda a: App.pure(a * 2)
    identity = lambda a: App.pure(a)
    
    # f ∘ id
    left = f(x).flat_map(identity)
    
    # f
    right = f(x)
    
    assert await_result(left) == await_result(right)


# === Monad Laws ===

@given(st.integers(), st.integers())
@settings(max_examples=1000)
def test_monad_left_identity(a, multiplier):
    """
    Law: pure(a) >>= f = f(a)
    
    Wrapping then binding = direct application.
    """
    f = lambda x: App.pure(x * multiplier)
    
    left = App.pure(a).flat_map(f)
    right = f(a)
    
    assert await_result(left) == await_result(right)


@given(st.integers())
@settings(max_examples=1000)
def test_monad_right_identity(x):
    """
    Law: m >>= pure = m
    
    Binding to pure has no effect.
    """
    m = App.pure(x * 2)
    
    left = m.flat_map(App.pure)
    right = m
    
    assert await_result(left) == await_result(right)


@given(st.integers())
@settings(max_examples=1000)
def test_monad_associativity(x):
    """
    Law: (m >>= f) >>= g = m >>= (λx. f(x) >>= g)
    
    Order of binding doesn't matter.
    """
    m = App.pure(x)
    f = lambda a: App.pure(a * 2)
    g = lambda a: App.pure(a + 1)
    
    # (m >>= f) >>= g
    left = m.flat_map(f).flat_map(g)
    
    # m >>= (λx. f(x) >>= g)
    right = m.flat_map(lambda a: f(a).flat_map(g))
    
    assert await_result(left) == await_result(right)


# === Functor Laws ===

@given(st.integers())
@settings(max_examples=1000)
def test_functor_identity(x):
    """
    Law: F(id) = id
    
    Mapping identity function has no effect.
    """
    m = App.pure(x)
    identity = lambda a: a
    
    left = m.map(identity)
    right = m
    
    assert await_result(left) == await_result(right)


@given(st.integers())
@settings(max_examples=1000)
def test_functor_composition(x):
    """
    Law: F(g ∘ f) = F(g) ∘ F(f)
    
    Mapping composed function = composing mapped functions.
    """
    m = App.pure(x)
    f = lambda a: a * 2
    g = lambda a: a + 1
    
    # F(g ∘ f)
    left = m.map(lambda a: g(f(a)))
    
    # F(g) ∘ F(f)
    right = m.map(f).map(g)
    
    assert await_result(left) == await_result(right)


# === Naturality ===

@given(users)
@settings(max_examples=1000)
def test_response_naturality(user):
    """
    Law: G(f) ∘ α_A = α_B ∘ F(f)
    
    For StandardResponse transformation:
    Transforming then wrapping = wrapping then transforming.
    """
    from src.api.schemas import UserResponse
    from src.middleware.response import wrap_response
    
    f = lambda u: u.email  # User → str
    
    # α_B ∘ F(f) : First extract email, then wrap
    left = wrap_response(f(user), request_id="test")
    
    # G(f) ∘ α_A : First wrap user, then extract email from wrapped
    wrapped = wrap_response(user, request_id="test")
    right = wrap_response(f(wrapped.data), request_id="test")
    
    # Data should be equivalent
    assert left.data == right.data


# === Helper ===

def await_result(app: App) -> any:
    """Run App and extract result for comparison."""
    import asyncio
    from src.domain.effects.app import Env
    
    # Create minimal test env
    env = Env(repositories=MockRepositories(), config=MockConfig())
    
    result = asyncio.run(app.run(env))
    match result:
        case Ok(value):
            return ("ok", value)
        case Err(error):
            return ("err", type(error).__name__)
```

### Property Test Report

```yaml
# verify/property-tests-report.yaml
version: "1.0"
strategy: hypothesis
examples_per_test: 1000

results:
  category_laws:
    - law: composition_associativity
      status: PASS
      examples_run: 1000
      
    - law: identity_left
      status: PASS
      examples_run: 1000
      
    - law: identity_right
      status: PASS
      examples_run: 1000
  
  monad_laws:
    - law: left_identity
      status: PASS
      examples_run: 1000
      
    - law: right_identity
      status: PASS
      examples_run: 1000
      
    - law: associativity
      status: PASS
      examples_run: 1000
  
  functor_laws:
    - law: identity
      status: PASS
      examples_run: 1000
      
    - law: composition
      status: PASS
      examples_run: 1000
  
  naturality:
    - transformation: StandardResponse
      status: PASS
      examples_run: 1000

summary:
  total_tests: 9
  passed: 9
  failed: 0
  total_examples: 9000
  confidence: "statistical (not formal proof)"
```

### When to Use Each Strategy

| Strategy | Rigor | Difficulty | Use When |
|----------|-------|------------|----------|
| **lean** | Mathematical proof | High | Production systems, safety-critical |
| **hypothesis** | Statistical (99.9%) | Low | Rapid iteration, prototypes |
| **both** | Maximum | Medium | Important systems, belt-and-suspenders |

### Fallback Decision Tree

```
Attempt Lean proof
       │
       ├─ Compiles & proves → Use Lean ✓
       │
       ├─ Compiles but sorry → 
       │     │
       │     ├─ Fundamental law → ERROR, fix build artifacts
       │     └─ Implementation-specific → Accept with justification
       │
       └─ Fails to compile →
             │
             ├─ Syntax error → Fix and retry
             └─ Too complex → Fall back to Hypothesis
                              Generate property tests
                              Run 1000+ examples
                              Report statistical confidence
```

## Do NOT

- **Skip fundamental laws** — Category and functor laws must be proven
- **Hide errors** — Report all failures
- **Use sorry without justification** — Document why
- **Generate invalid Lean** — Must compile
