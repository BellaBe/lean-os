

# Composition Validation Example

## Problem

Services don't compose correctly:

```python
# Service chain
ServiceA: Request → User
ServiceB: Profile → Recommendations  # User ≠ Profile!

# Attempt to compose
result = compose(ServiceB, ServiceA)  # ERROR: Types don't align!
```

## Validation

```python
from scripts.validate import Architecture, Service, validate

arch = Architecture(
    services=[
        Service("ServiceA", "Request", "User"),
        Service("ServiceB", "Profile", "Recommendations"),
    ],
    types={"Request", "User", "Profile", "Recommendations"},
    identities={},
    compositions=[]
)

report = validate(arch, checks=['composition'])
print(report)
```

## Output

```
Architecture Validation Report
========================================

Status: ✗ FAILED

Violations:
✗ Composition: Services don't compose (type mismatch)
  ServiceA: Request → User
  ServiceB: Profile → Recommendations
  User ≠ Profile

  Fix: Add adapter service or fix types
```

## Fix Option 1: Add Adapter

```python
# Add adapter service
arch.services.append(
    Service("getUserProfile", "User", "Profile")
)

# Now composition works:
# ServiceB ∘ getUserProfile ∘ ServiceA
# Request → User → Profile → Recommendations
```

## Fix Option 2: Correct Types

```python
# Fix ServiceB to accept User instead of Profile
ServiceB_fixed = Service("ServiceB", "User", "Recommendations")

# Now composes directly:
# ServiceB_fixed ∘ ServiceA
# Request → User → Recommendations
```

## Validated Architecture

```python
arch_fixed = Architecture(
    services=[
        Service("id_Request", "Request", "Request"),
        Service("id_User", "User", "User"),
        Service("id_Recommendations", "Recommendations", "Recommendations"),
        Service("ServiceA", "Request", "User"),
        Service("getUserProfile", "User", "Profile"),
        Service("ServiceB", "Profile", "Recommendations"),
    ],
    types={"Request", "User", "Profile", "Recommendations"},
    identities={
        "Request": Service("id_Request", "Request", "Request"),
        "User": Service("id_User", "User", "User"),
        "Recommendations": Service("id_Recommendations", "Recommendations", "Recommendations"),
    },
    compositions=[
        # ServiceB ∘ getUserProfile
        (
            Service("getUserProfile", "User", "Profile"),
            Service("ServiceB", "Profile", "Recommendations"),
            Service("ServiceB_getUserProfile", "User", "Recommendations")
        ),
        # (ServiceB ∘ getUserProfile) ∘ ServiceA
        (
            Service("ServiceA", "Request", "User"),
            Service("ServiceB_getUserProfile", "User", "Recommendations"),
            Service("getRecommendations", "Request", "Recommendations")
        ),
    ]
)

report = validate(arch_fixed)
print(report)
# ✓ All checks passed
```

## Benefits

- **Caught at validation** instead of runtime failure
- **Clear fix suggestions** from validator
- **Type safety** enforced mathematically
