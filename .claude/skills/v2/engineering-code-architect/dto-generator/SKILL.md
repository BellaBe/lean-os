---
name: dto-generator
description: |
  Generate DTOs from HTTP functor maps. Creates Pydantic request/response models
  that implement the HTTP functor object mapping. Includes to_domain and from_domain
  transformations for each DTO.
  Input: maps/functors/http.map.yaml, entities
  Output: generated/python/src/{project}/application/dtos/*.py
---

# DTO Generator

Generate DTOs implementing HTTP functor object mapping.

## Purpose

Transform HTTP functor maps into DTO classes:
1. Generate request DTOs (HTTP → Domain)
2. Generate response DTOs (Domain → HTTP)
3. Implement to_domain/from_domain transformations
4. Add Pydantic validation

## Input

- `maps/functors/http.map.yaml` - HTTP functor definition
- `generated/.../domain/entities/*.py` - Domain entities

## Output

```
generated/python/src/{project}/application/dtos/
├── __init__.py
├── requests.py
└── responses.py
```

## HTTP Functor Object Mapping

### Mathematical Foundation

```
HTTP Functor object mapping:

F: Domain → HTTP on objects:
  Merchant → (CreateMerchantRequest, UpdateMerchantRequest, MerchantResponse)
  
to_domain: Request → DomainDTO
  - Converts HTTP request to domain DTO
  - Part of HTTP functor (inverse direction)
  
from_domain: Entity → Response
  - Converts domain entity to HTTP response
  - Part of HTTP functor (forward direction)

Certificate: functor.cert.yaml#http_functor_id
```

## Generated Code

### Request DTOs

```python
# generated/python/src/{project}/application/dtos/requests.py

from __future__ import annotations
from datetime import datetime
from typing import Optional, List
from uuid import UUID

from pydantic import BaseModel, Field, field_validator, ConfigDict

from ...domain.entities.subscription import SubscriptionTier
from ...domain.entities.settings import MerchantSettings


class CreateMerchantRequest(BaseModel):
    """
    Request DTO for creating a merchant.
    
    HTTP Functor object mapping:
    - HTTP representation of CreateMerchantDTO
    - to_domain converts to domain DTO
    
    Certificate: functor.cert.yaml#http_functor_id
    """
    
    model_config = ConfigDict(
        str_strip_whitespace=True,
        json_schema_extra={
            "example": {
                "shop_domain": "example.myshopify.com"
            }
        }
    )
    
    shop_domain: str = Field(
        ...,
        description="Shopify shop domain",
        min_length=1,
        max_length=255,
        pattern=r"^[a-z0-9-]+\.myshopify\.com$"
    )
    
    @field_validator("shop_domain")
    @classmethod
    def validate_shop_domain(cls, v: str) -> str:
        """Validate Shopify domain format."""
        if not v.endswith(".myshopify.com"):
            raise ValueError("Must be a valid Shopify domain")
        return v.lower()
    
    def to_domain(self) -> CreateMerchantDTO:
        """
        HTTP Functor: Request → DomainDTO.
        
        Transforms HTTP request to domain DTO.
        """
        from .domain_dtos import CreateMerchantDTO
        return CreateMerchantDTO(
            shop_domain=self.shop_domain
        )


class UpdateMerchantRequest(BaseModel):
    """
    Request DTO for updating a merchant.
    
    All fields optional for partial updates (PATCH semantics).
    """
    
    model_config = ConfigDict(str_strip_whitespace=True)
    
    subscription_tier: Optional[SubscriptionTier] = Field(
        None,
        description="New subscription tier"
    )
    settings: Optional[dict] = Field(
        None,
        description="Merchant settings"
    )
    
    def to_domain(self) -> UpdateMerchantDTO:
        """HTTP Functor: Request → DomainDTO."""
        from .domain_dtos import UpdateMerchantDTO
        return UpdateMerchantDTO(
            subscription_tier=self.subscription_tier,
            settings=MerchantSettings.from_dict(self.settings) if self.settings else None
        )


class CreateProfileRequest(BaseModel):
    """Request DTO for creating a profile."""
    
    model_config = ConfigDict(str_strip_whitespace=True)
    
    merchant_id: UUID = Field(..., description="Parent merchant ID")
    name: str = Field(..., min_length=1, max_length=255)
    preferences: Optional[dict] = Field(default_factory=dict)
    
    def to_domain(self) -> CreateProfileDTO:
        from .domain_dtos import CreateProfileDTO
        from ...domain.value_objects.identifiers import MerchantId
        return CreateProfileDTO(
            merchant_id=MerchantId(self.merchant_id),
            name=self.name,
            preferences=self.preferences or {}
        )


class CreateAnalysisRequest(BaseModel):
    """Request DTO for creating an analysis."""
    
    model_config = ConfigDict(str_strip_whitespace=True)
    
    profile_id: UUID = Field(..., description="Profile to analyze")
    photo_url: Optional[str] = Field(None, description="URL of photo to analyze")
    
    # For multipart upload, photo_data would come separately
    
    def to_domain(self) -> CreateAnalysisDTO:
        from .domain_dtos import CreateAnalysisDTO
        from ...domain.value_objects.identifiers import ProfileId
        return CreateAnalysisDTO(
            profile_id=ProfileId(self.profile_id),
            photo_url=self.photo_url,
            photo_data=None  # Set separately if multipart
        )
```

### Response DTOs

```python
# generated/python/src/{project}/application/dtos/responses.py

from __future__ import annotations
from datetime import datetime
from typing import Optional, List, Generic, TypeVar
from uuid import UUID

from pydantic import BaseModel, Field, ConfigDict

from ...domain.entities.merchant import Merchant
from ...domain.entities.profile import Profile
from ...domain.entities.analysis import Analysis, AnalysisStatus
from ...domain.entities.subscription import SubscriptionTier

T = TypeVar("T")


class MerchantResponse(BaseModel):
    """
    Response DTO for merchant data.
    
    HTTP Functor object mapping:
    - HTTP representation of Merchant entity
    - from_domain converts from domain entity
    
    Certificate: functor.cert.yaml#http_functor_id
    """
    
    model_config = ConfigDict(
        from_attributes=True,
        json_schema_extra={
            "example": {
                "id": "123e4567-e89b-12d3-a456-426614174000",
                "shop_domain": "example.myshopify.com",
                "subscription_tier": "free",
                "created_at": "2024-01-15T12:00:00Z"
            }
        }
    )
    
    id: UUID
    shop_domain: str
    subscription_tier: SubscriptionTier
    settings: dict
    created_at: datetime
    updated_at: datetime
    
    @classmethod
    def from_domain(cls, merchant: Merchant) -> MerchantResponse:
        """
        HTTP Functor: Entity → Response.
        
        Transforms domain entity to HTTP response.
        Preserves structure while changing representation.
        
        Certificate: functor.cert.yaml#http_functor_comp
        """
        return cls(
            id=merchant.id,
            shop_domain=str(merchant.shop_domain),
            subscription_tier=merchant.subscription_tier,
            settings=merchant.settings.to_dict(),
            created_at=merchant.created_at,
            updated_at=merchant.updated_at,
        )


class MerchantListResponse(BaseModel):
    """Paginated list of merchants."""
    
    items: List[MerchantResponse]
    offset: int
    limit: int
    total: int


class ProfileResponse(BaseModel):
    """Response DTO for profile data."""
    
    model_config = ConfigDict(from_attributes=True)
    
    id: UUID
    merchant_id: UUID
    name: str
    preferences: dict
    created_at: datetime
    
    @classmethod
    def from_domain(cls, profile: Profile) -> ProfileResponse:
        """HTTP Functor: Entity → Response."""
        return cls(
            id=profile.id,
            merchant_id=profile.merchant_id,
            name=profile.name,
            preferences=profile.preferences,
            created_at=profile.created_at,
        )


class ProfileListResponse(BaseModel):
    """Paginated list of profiles."""
    
    items: List[ProfileResponse]
    offset: int
    limit: int
    total: int


class AnalysisResponse(BaseModel):
    """Response DTO for analysis data."""
    
    model_config = ConfigDict(from_attributes=True)
    
    id: UUID
    profile_id: UUID
    photo_url: str
    status: AnalysisStatus
    results: Optional[dict] = None
    created_at: datetime
    completed_at: Optional[datetime] = None
    
    @classmethod
    def from_domain(cls, analysis: Analysis) -> AnalysisResponse:
        """HTTP Functor: Entity → Response."""
        return cls(
            id=analysis.id,
            profile_id=analysis.profile_id,
            photo_url=analysis.photo_url,
            status=analysis.status,
            results=analysis.results,
            created_at=analysis.created_at,
            completed_at=analysis.completed_at,
        )


class AnalysisListResponse(BaseModel):
    """Paginated list of analyses."""
    
    items: List[AnalysisResponse]
    offset: int
    limit: int
    total: int


class ErrorResponse(BaseModel):
    """Standard error response."""
    
    detail: str
    code: Optional[str] = None
    
    model_config = ConfigDict(
        json_schema_extra={
            "example": {
                "detail": "Merchant not found",
                "code": "MERCHANT_NOT_FOUND"
            }
        }
    )


class HealthResponse(BaseModel):
    """Health check response."""
    
    status: str = "healthy"
    version: str
    timestamp: datetime
```

### Domain DTOs (Internal)

```python
# generated/python/src/{project}/application/dtos/domain_dtos.py

from __future__ import annotations
from dataclasses import dataclass
from typing import Optional

from ...domain.value_objects.identifiers import MerchantId, ProfileId
from ...domain.entities.subscription import SubscriptionTier
from ...domain.entities.settings import MerchantSettings


@dataclass(frozen=True)
class CreateMerchantDTO:
    """
    Domain DTO for merchant creation.
    
    Pure domain representation - no HTTP concerns.
    """
    shop_domain: str


@dataclass(frozen=True)
class UpdateMerchantDTO:
    """Domain DTO for merchant updates."""
    subscription_tier: Optional[SubscriptionTier] = None
    settings: Optional[MerchantSettings] = None


@dataclass(frozen=True)
class CreateProfileDTO:
    """Domain DTO for profile creation."""
    merchant_id: MerchantId
    name: str
    preferences: dict


@dataclass(frozen=True)
class CreateAnalysisDTO:
    """Domain DTO for analysis creation."""
    profile_id: ProfileId
    photo_url: Optional[str] = None
    photo_data: Optional[bytes] = None
```

## Template Structure

```python
# Request DTO template

from __future__ import annotations
from typing import Optional
from uuid import UUID

from pydantic import BaseModel, Field, field_validator, ConfigDict


class {{ Create }}Request(BaseModel):
    """
    Request DTO for creating {{ entity }}.
    
    HTTP Functor: {{ Create }}Request → Create{{ Entity }}DTO
    """
    
    model_config = ConfigDict(str_strip_whitespace=True)
    
    {% for field in fields %}
    {{ field.name }}: {{ field.http_type }} = Field(
        {{ field.default }},
        description="{{ field.description }}"
        {% if field.constraints %}, {{ field.constraints }}{% endif %}
    )
    {% endfor %}
    
    def to_domain(self) -> Create{{ Entity }}DTO:
        """HTTP Functor: Request → DomainDTO."""
        from .domain_dtos import Create{{ Entity }}DTO
        return Create{{ Entity }}DTO(
            {% for field in fields %}
            {{ field.name }}={{ field.transform }},
            {% endfor %}
        )
```

## Validation Checks

```yaml
validation:
  dtos_generated:
    check: "All entities have request/response DTOs"
    
  transformations_exist:
    check: "to_domain and from_domain implemented"
    
  validation_rules:
    check: "Pydantic validators match domain constraints"
```

## Next Skills

Output feeds into:
- `handler-generator`
