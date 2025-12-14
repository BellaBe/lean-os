---
name: build-category
description: |
  Formalize domain as a category. Defines objects, morphisms, composition,
  identity, and laws from spec artifacts. Use when: building category
  structure, formalizing domain, preparing for verification.
---

# Build Category

Formalize the domain category from spec artifacts.

## Categorical Foundation

A category C consists of:
- **Objects**: ob(C) — The types
- **Morphisms**: hom(A, B) — Functions between types
- **Composition**: ∘ — How morphisms chain
- **Identity**: id_A — Identity morphism for each object
- **Laws**: Associativity and identity laws

## Input

- `artifacts/v{N}/spec/objects.yaml`
- `artifacts/v{N}/spec/morphisms.yaml`

## Output

`artifacts/v{N}/build/category.yaml`

## Process

1. **Collect objects** from spec/objects.yaml
2. **Collect morphisms** from spec/morphisms.yaml
3. **Define identity** morphisms
4. **Define composition** operators
5. **State laws** to be proven

## Category Definition

```
Domain Category:
  Objects:     All types from spec/objects.yaml
  Morphisms:   All operations from spec/morphisms.yaml
  Composition: Pure (∘) for pure morphisms
               Kleisli (>=>) for effectful morphisms
  Identity:    id_A: A → A for each object A
```

## Output Format

```yaml
version: "1.0"
category:
  name: "Domain"
  description: "The domain category containing all business types and operations"
  
  # ========================================
  # Objects (from spec/objects.yaml)
  # ========================================
  objects:
    # List all object IDs
    - "UserId"
    - "User"
    - "Email"
    - "UserStatus"
    - "CreateUserInput"
    - "RegistrationInput"
    - "Money"
    - "OrderId"
    - "Order"
    # ... all objects
    
  # ========================================
  # Morphisms (from spec/morphisms.yaml)
  # ========================================
  morphisms:
    # Generator morphisms
    - id: "validate_email"
      hom: "String → Either[ValidationError, Email]"
      effects: ["Either[ValidationError, _]"]
      generator: true
      
    - id: "create_user"
      hom: "CreateUserInput → IO[Either[UserError, User]]"
      effects: ["IO", "Either[UserError, _]"]
      generator: true
      
    - id: "get_user"
      hom: "UserId → IO[Either[UserError, User]]"
      effects: ["IO", "Either[UserError, _]"]
      generator: true
      
    - id: "build_welcome_email"
      hom: "User → EmailMessage"
      effects: []
      generator: true
      
    - id: "send_email"
      hom: "EmailMessage → IO[Either[EmailError, Unit]]"
      effects: ["IO", "Either[EmailError, _]"]
      generator: true
      
    # Derived morphisms (compositions)
    - id: "send_welcome_email"
      hom: "User → IO[Either[EmailError, Unit]]"
      effects: ["IO", "Either[EmailError, _]"]
      generator: false
      composed_of: ["build_welcome_email", "send_email"]
      
    - id: "register_user"
      hom: "RegistrationInput → IO[Either[RegistrationError, User]]"
      effects: ["IO", "Either[RegistrationError, _]"]
      generator: false
      composed_of: ["validate_email", "validate_password", "check_email_not_exists", "create_user", "send_welcome_email"]
      
  # ========================================
  # Identity
  # ========================================
  identity:
    description: "Identity morphism for each object"
    pattern: "id_A: A → A"
    implementation: "λx. x"
    
    # Objects that appear as both domain and codomain need explicit identity
    # (for composition to be well-defined)
    objects_with_identity:
      - "User"
      - "Email"
      - "Order"
      - "UserId"
      # ... objects used in compositions
      
  # ========================================
  # Composition
  # ========================================
  composition:
    pure:
      description: "Standard function composition"
      operator: "∘"
      signature: "(g: B → C) → (f: A → B) → (A → C)"
      implementation: "λg. λf. λx. g(f(x))"
      notation: "g ∘ f"
      
    kleisli:
      description: "Kleisli composition for effectful morphisms"
      operator: ">=>"
      signature: "(f: A → M[B]) → (g: B → M[C]) → (A → M[C])"
      implementation: "λf. λg. λx. f(x).flatMap(g)"
      notation: "f >=> g"
      note: "Note: Kleisli composition is left-to-right (f then g)"
      
  # ========================================
  # Laws
  # ========================================
  laws:
    # Identity laws
    - name: "left_identity"
      kind: "identity"
      statement: "id ∘ f = f"
      formal: "∀ (f: A → B). id_B ∘ f = f"
      status: stated
      
    - name: "right_identity"
      kind: "identity"
      statement: "f ∘ id = f"
      formal: "∀ (f: A → B). f ∘ id_A = f"
      status: stated
      
    # Associativity
    - name: "associativity"
      kind: "composition"
      statement: "(h ∘ g) ∘ f = h ∘ (g ∘ f)"
      formal: "∀ (f: A → B) (g: B → C) (h: C → D). (h ∘ g) ∘ f = h ∘ (g ∘ f)"
      status: stated
      
    # Kleisli laws
    - name: "kleisli_left_identity"
      kind: "identity"
      statement: "return >=> f = f"
      formal: "∀ (f: A → M[B]). return >=> f = f"
      status: stated
      
    - name: "kleisli_right_identity"
      kind: "identity"
      statement: "f >=> return = f"
      formal: "∀ (f: A → M[B]). f >=> return = f"
      status: stated
      
    - name: "kleisli_associativity"
      kind: "composition"
      statement: "(f >=> g) >=> h = f >=> (g >=> h)"
      formal: "∀ (f: A → M[B]) (g: B → M[C]) (h: C → M[D]). (f >=> g) >=> h = f >=> (g >=> h)"
      status: stated
      
  # ========================================
  # Named Compositions (derived morphisms expanded)
  # ========================================
  named_compositions:
    - id: "send_welcome_email"
      chain: ["build_welcome_email", "send_email"]
      chain_types:
        - "User → EmailMessage"
        - "EmailMessage → IO[Either[EmailError, Unit]]"
      composed_type: "User → IO[Either[EmailError, Unit]]"
      composition_type: kleisli
      
    - id: "register_user"
      chain: ["validate_email", "validate_password", "check_email_not_exists", "create_user", "send_welcome_email"]
      chain_types:
        - "String → Either[ValidationError, Email]"
        - "String → Either[ValidationError, HashedPassword]"
        - "Email → IO[Either[UserError, Email]]"
        - "CreateUserInput → IO[Either[UserError, User]]"
        - "User → IO[Either[EmailError, Unit]]"
      composed_type: "RegistrationInput → IO[Either[RegistrationError, User]]"
      composition_type: kleisli
      
  # ========================================
  # Validation
  # ========================================
  validation:
    objects:
      total: 15
      from_spec: 15
      complete: true
      
    morphisms:
      total: 12
      generators: 8
      derived: 4
      from_spec: 12
      complete: true
      
    compositions:
      all_type_check: true
      errors: []
```

## Type Checking Compositions

For each derived morphism, verify the chain types align:

```
Chain: [f₁, f₂, f₃]

f₁: A₁ → M[A₂]
f₂: A₂ → M[A₃]  ← domain(f₂) must equal unwrapped codomain(f₁)
f₃: A₃ → M[A₄]  ← domain(f₃) must equal unwrapped codomain(f₂)

Result: A₁ → M[A₄]
```

If types don't align, report error:

```yaml
validation:
  compositions:
    all_type_check: false
    errors:
      - composition: "register_user"
        position: 3
        expected_domain: "Email"
        actual_domain: "CreateUserInput"
        message: "Type mismatch at position 3"
```

## Identity Generation

For each object A that appears as:
- Domain of some morphism, AND
- Codomain of some morphism

Generate identity:

```yaml
identity:
  objects_with_identity:
    - "User"      # create_user: _ → User, update_user: User → _
    - "Email"     # validate_email: _ → Email, check_exists: Email → _
```

## Composition Operator Selection

| Morphism Types | Operator | Example |
|----------------|----------|---------|
| Both pure | ∘ | `format ∘ validate` |
| Either effectful | >=> | `create_user >=> send_email` |
| Mixed (adapter) | Lift + >=> | `lift(pure) >=> effectful` |

## Validation Rules

1. **Objects complete**: All spec objects in category
2. **Morphisms complete**: All spec morphisms in category
3. **Compositions valid**: All chains type-check
4. **Identity defined**: For all objects in compositions
5. **Laws stated**: All fundamental laws listed

## Validation Checklist

- [ ] All objects from spec/objects.yaml present
- [ ] All morphisms from spec/morphisms.yaml present
- [ ] All composed_of chains type-check
- [ ] Identity morphisms defined for relevant objects
- [ ] Category laws stated with status: stated
- [ ] Kleisli laws stated if effectful morphisms exist

## Do NOT

- **Add implementation details** — Just structure
- **Skip derived morphisms** — They're morphisms too
- **Assume laws proven** — Status is "stated" until verify phase
- **Mix categories** — This is ONLY the domain category
