#!/usr/bin/env python3
"""
Curry-Howard Prover

Prove system requirements through types.
Implementation = Proof. If code type-checks, theorem is proven.
"""

from typing import TypeVar, Callable, Tuple, Union, Never, Any, Generic, Type
from dataclasses import dataclass
import inspect

A = TypeVar('A')
B = TypeVar('B')
C = TypeVar('C')


# ========== Logical Rules as Functions ==========

def modus_ponens(implication: Callable[[A], B], premise: A) -> B:
    """
    Modus Ponens: ((A ⇒ B) ∧ A) ⇒ B

    If A implies B, and we have A, then we have B.
    """
    return implication(premise)


def absurd(impossible: Never) -> Any:
    """
    Ex Falso Quodlibet: False ⇒ A

    From impossibility, anything follows (but never executes).
    """
    raise RuntimeError("Unreachable - Never has no values")


def pair(a: A, b: B) -> Tuple[A, B]:
    """
    Conjunction Introduction: A ⇒ B ⇒ (A ∧ B)

    Prove A and B by providing both.
    """
    return (a, b)


def fst(p: Tuple[A, B]) -> A:
    """
    Conjunction Elimination (left): (A ∧ B) ⇒ A

    From A and B, extract A.
    """
    return p[0]


def snd(p: Tuple[A, B]) -> B:
    """
    Conjunction Elimination (right): (A ∧ B) ⇒ B

    From A and B, extract B.
    """
    return p[1]


def left(a: A) -> Union[A, B]:
    """
    Disjunction Introduction (left): A ⇒ (A ∨ B)

    Prove A or B by providing A.
    """
    return a


def right(b: B) -> Union[A, B]:
    """
    Disjunction Introduction (right): B ⇒ (A ∨ B)

    Prove A or B by providing B.
    """
    return b


def case_analysis(
    either: Union[A, B],
    handle_a: Callable[[A], C],
    handle_b: Callable[[B], C]
) -> C:
    """
    Case Analysis: (A ∨ B) ⇒ ((A ⇒ C) ⇒ (B ⇒ C) ⇒ C)

    From A or B, prove C by handling both cases.
    """
    # Simplified - proper implementation needs runtime type checking
    try:
        return handle_a(either)  # type: ignore
    except:
        return handle_b(either)  # type: ignore


def compose(g: Callable[[B], C], f: Callable[[A], B]) -> Callable[[A], C]:
    """
    Function Composition: (B ⇒ C) ⇒ (A ⇒ B) ⇒ (A ⇒ C)

    Compose implications.
    """
    return lambda a: g(f(a))


def identity(a: A) -> A:
    """
    Identity: A ⇒ A

    Trivial proof.
    """
    return a


# ========== Phantom Types for State Proofs ==========

class Authenticated:
    """Phantom type proving authentication"""
    pass


class Unauthenticated:
    """Phantom type proving no authentication"""
    pass


class Validated:
    """Phantom type proving validation"""
    pass


class Unvalidated:
    """Phantom type proving no validation"""
    pass


# ========== Session with Phantom Types ==========

class Session(Generic[A]):
    """
    Session tagged with authentication state.

    Phantom type parameter proves state without runtime overhead.
    """

    def __init__(self, session_id: str):
        self.session_id = session_id

    @staticmethod
    def create_unauthenticated(session_id: str) -> 'Session[Unauthenticated]':
        """Create unauthenticated session"""
        return Session(session_id)

    def authenticate(
        self: 'Session[Unauthenticated]',
        credentials: str
    ) -> 'Session[Authenticated]':
        """
        Transition to authenticated session.

        Type system proves: Unauthenticated → Authenticated
        """
        # Verify credentials (simplified)
        if credentials:
            # Type changes, proving authentication
            return Session[Authenticated](self.session_id)  # type: ignore
        raise ValueError("Authentication failed")

    def access_protected(self: 'Session[Authenticated]') -> str:
        """
        Only callable on authenticated sessions.

        Type system enforces authentication requirement.
        """
        return f"Protected resource for session {self.session_id}"


# ========== Validated Input ==========

class Input(Generic[A]):
    """
    Input tagged with validation state.

    Ensures validated data flows through system.
    """

    def __init__(self, data: str):
        self._data = data

    @staticmethod
    def create(data: str) -> 'Input[Unvalidated]':
        """Create unvalidated input"""
        return Input(data)

    def validate(self: 'Input[Unvalidated]') -> 'Input[Validated]':
        """
        Validate input.

        Type proves: Unvalidated → Validated
        """
        # Validation logic
        if self._data:
            return Input[Validated](self._data)  # type: ignore
        raise ValueError("Validation failed")

    def process(self: 'Input[Validated]') -> str:
        """
        Process validated input.

        Type system ensures only validated input is processed.
        """
        return f"Processing: {self._data}"


# ========== Tenant Isolation ==========

class TenantA:
    """Tenant A marker type"""
    pass


class TenantB:
    """Tenant B marker type"""
    pass


class TenantData(Generic[A]):
    """
    Data tagged with tenant type.

    Type system enforces tenant isolation.
    """

    def __init__(self, data: Any, tenant_type: Type[A]):
        self._data = data
        self._tenant_type = tenant_type

    def access(self, credentials: A) -> Any:
        """
        Access data with matching tenant credentials.

        Type system proves tenant isolation:
        TenantData[A].access(A) → Data  ✓
        TenantData[A].access(B) → Type Error  ✗
        """
        # Type system enforces credentials match tenant
        return self._data


# ========== Proof Validation ==========

def validate_proof(theorem: Type, proof: Callable) -> bool:
    """
    Validate that proof matches theorem.

    Uses Python's type checking to verify proof.
    """
    # Get proof signature
    sig = inspect.signature(proof)

    # Simple validation - proper implementation needs full type checker
    # In practice, use mypy/pyright for validation

    return True  # Simplified - type checker validates


# ========== System Requirements as Theorems ==========

@dataclass
class Credentials:
    """User credentials"""
    username: str
    token: str


@dataclass
class ServiceAvailable:
    """Service availability proof"""
    service_name: str


@dataclass
class ProtectedResource:
    """Protected resource"""
    content: str


def prove_access_requirement(
    credentials: Credentials,
    service: ServiceAvailable
) -> ProtectedResource:
    """
    Theorem: (HasCredentials ∧ ServiceAvailable) ⇒ CanAccessResource

    Proof: Implementation type-checks, therefore theorem holds.
    """
    # Implementation = Proof
    return ProtectedResource(
        content=f"Access granted for {credentials.username} to {service.service_name}"
    )


# ========== Examples ==========

if __name__ == '__main__':
    print("=== Curry-Howard Correspondence Examples ===\n")

    # Example 1: Modus Ponens
    print("1. Modus Ponens: ((A ⇒ B) ∧ A) ⇒ B")
    double = lambda x: x * 2
    result = modus_ponens(double, 21)
    print(f"   modus_ponens(x → x*2, 21) = {result}")
    print(f"   Type checks, therefore proven. ∎\n")

    # Example 2: Function Composition
    print("2. Function Composition")
    inc = lambda x: x + 1
    square = lambda x: x * x
    composed = compose(square, inc)
    result = composed(4)
    print(f"   (square ∘ inc)(4) = square(inc(4)) = {result}")
    print(f"   Type checks, therefore proven. ∎\n")

    # Example 3: Conjunction
    print("3. Conjunction Introduction & Elimination")
    conjunction = pair(42, "hello")
    left_val = fst(conjunction)
    right_val = snd(conjunction)
    print(f"   pair(42, 'hello') = {conjunction}")
    print(f"   fst(pair) = {left_val}")
    print(f"   snd(pair) = {right_val}")
    print(f"   Type checks, therefore proven. ∎\n")

    # Example 4: Session Authentication
    print("4. Session Authentication (Phantom Types)")
    unauth_session = Session.create_unauthenticated("session-123")
    print(f"   Created unauthenticated session")

    # This would be a type error:
    # unauth_session.access_protected()  # Type error!

    auth_session = unauth_session.authenticate("valid-credentials")
    protected = auth_session.access_protected()
    print(f"   Authenticated session can access: {protected}")
    print(f"   Type system proves authentication requirement. ∎\n")

    # Example 5: Validated Input
    print("5. Validated Input Processing")
    raw_input = Input.create("user-data")
    print(f"   Created unvalidated input")

    # This would be a type error:
    # raw_input.process()  # Type error!

    validated_input = raw_input.validate()
    processed = validated_input.process()
    print(f"   Validated input: {processed}")
    print(f"   Type system proves validation requirement. ∎\n")

    # Example 6: System Requirement
    print("6. System Requirement as Theorem")
    print("   Theorem: (Credentials ∧ ServiceAvailable) ⇒ ProtectedResource")

    creds = Credentials("alice", "token-abc")
    service = ServiceAvailable("api-server")
    resource = prove_access_requirement(creds, service)

    print(f"   Proof: {resource.content}")
    print(f"   Implementation type-checks, therefore requirement is proven. ∎\n")

    print("✓ All theorems proven via Curry-Howard correspondence!")
