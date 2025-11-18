# Multi-Tenant Reader Functor Example

## Use Case

Multi-tenant SaaS application where each tenant has different configuration (API keys, database connections, feature flags).

## Problem

Hardcoded configuration makes multi-tenancy impossible:

```python
# BAD: Hardcoded configuration
def send_notification(user_id: str, message: str):
    api_key = "hardcoded_sendgrid_key"
    return sendgrid.send(api_key, user_id, message)

# Can't use different keys for different tenants!
```

## Solution: Reader Functor

Transform service to accept configuration:

```python
from functor_generator import Reader

# Define configuration type
class TenantConfig:
    def __init__(self, sendgrid_key: str, db_url: str):
        self.sendgrid_key = sendgrid_key
        self.db_url = db_url

# Original service becomes Reader
def send_notification_reader(user_id: str, message: str) -> Reader[TenantConfig, bool]:
    def run(config: TenantConfig):
        return sendgrid.send(config.sendgrid_key, user_id, message)
    return Reader(run)

# Create tenant-specific configurations
tenant_a_config = TenantConfig(
    sendgrid_key="tenant_a_key",
    db_url="postgres://tenant_a"
)

tenant_b_config = TenantConfig(
    sendgrid_key="tenant_b_key",
    db_url="postgres://tenant_b"
)

# Use with different tenants
send_to_a = send_notification_reader("user123", "Hello")
send_to_b = send_notification_reader("user456", "World")

result_a = send_to_a.apply_config(tenant_a_config)  # Uses tenant A key
result_b = send_to_b.apply_config(tenant_b_config)  # Uses tenant B key
```

## Composition with Reader

Services compose naturally:

```python
def get_user_reader(user_id: str) -> Reader[TenantConfig, User]:
    def run(config):
        return database.query(config.db_url, user_id)
    return Reader(run)

def send_to_user_reader(user_id: str, message: str) -> Reader[TenantConfig, bool]:
    # Compose: get user, then send notification
    user_reader = get_user_reader(user_id)
    
    def run(config):
        user = user_reader.apply_config(config)
        if user.notifications_enabled:
            return send_notification_reader(user_id, message).apply_config(config)
        return False
    return Reader(run)

# Use with any tenant configuration
result = send_to_user_reader("user123", "Important!").apply_config(tenant_a_config)
```

## Benefits

1. **Type Safety**: Configuration type checked
2. **Testability**: Easy to inject test config
3. **Composition**: Services compose naturally
4. **Reusability**: Same code for all tenants

## Validation

Reader functor laws verified:

```python
from validate_functor import validate_reader_functor

# Verify functor laws hold
assert validate_reader_functor()  # True
```
