# standard_spec.py
from dataclasses import dataclass
from enum import Enum


class AuthMethod(str, Enum):
    NONE = "none"
    JWT = "jwt"
    API_KEY = "api_key"
    OAUTH = "oauth"


@dataclass
class AuthSpec:
    method: AuthMethod = AuthMethod.JWT
    required: bool = True
    jwt_algorithm: str = "HS256"
    api_key_header: str = "X-API-Key"
    oauth_scope: str = "default"


@dataclass
class ValidationSpec:
    enabled: bool = True
    max_request_size: int = 10 * 1024 * 1024
    max_string_length: int = 10_000
    sanitize_html: bool = False  # off to avoid extra deps


@dataclass
class ResponseFormatSpec:
    enabled: bool = True
    version: str = "1.0.0"
    include_request_id: bool = True
    include_trace_id: bool = True
    include_timestamp: bool = True


@dataclass
class ErrorHandlingSpec:
    enabled: bool = True
    retry_enabled: bool = True
    circuit_breaker_enabled: bool = True
    max_retries: int = 3
    failure_threshold: int = 5
    recovery_timeout: int = 60


@dataclass
class ObservabilitySpec:
    enabled: bool = True
    trace_header: str = "X-Trace-Id"
    metrics_enabled: bool = True


@dataclass
class RateLimitSpec:
    enabled: bool = True
    requests_per_minute: int = 60
    per_user: bool = True
    per_api_key: bool = True


@dataclass
class StandardizationSpec:
    auth: AuthSpec = AuthSpec()
    validation: ValidationSpec = ValidationSpec()
    response: ResponseFormatSpec = ResponseFormatSpec()
    errors: ErrorHandlingSpec = ErrorHandlingSpec()
    observability: ObservabilitySpec = ObservabilitySpec()
    rate_limit: RateLimitSpec = RateLimitSpec()
    version: str = "1.0.0"
