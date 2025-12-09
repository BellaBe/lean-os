---
name: service-generator
description: |
  Generate application services from module maps. Creates service classes that
  compose repository and external client operations using Kleisli composition.
  Implements morphisms as async methods returning Result types.
  Input: maps/modules/services.map.yaml, repositories, clients
  Output: generated/python/src/{project}/application/services/*.py
---

# Service Generator

Generate application services from module maps.

## Purpose

Transform module maps into service implementations:
1. Generate service classes for each aggregate
2. Implement morphisms as async methods
3. Compose operations using Kleisli patterns
4. Wire repository and client dependencies

## Input

- `maps/modules/services.map.yaml` - Service structure
- `maps/kleisli/*.map.yaml` - Effect composition patterns
- `generated/.../ports/repositories.py` - Repository interfaces
- `generated/.../ports/external.py` - External client interfaces

## Output

```
generated/python/src/{project}/application/
├── services/
│   ├── __init__.py
│   ├── merchant_service.py
│   ├── profile_service.py
│   └── analysis_service.py
└── ports/
    ├── repositories.py  # (from repository-generator)
    └── external.py      # External client interfaces
```

## Service Generation Rules

### Morphism → Method Mapping

```yaml
# From services.map.yaml
services:
  MerchantService:
    aggregate: Merchant
    dependencies:
      - MerchantRepository
      - ShopifyClient
    morphisms:
      - name: create_merchant
        signature: "CreateMerchantDTO → IO[Either[MerchantError, Merchant]]"
        steps:
          - validate_input
          - check_shop_exists
          - persist_merchant
          
      - name: get_merchant
        signature: "MerchantId → IO[Either[MerchantError, Option[Merchant]]]"
        steps:
          - fetch_from_repository
```

Generated Python:

```python
# generated/python/src/{project}/application/services/merchant_service.py

from __future__ import annotations
from dataclasses import dataclass
from typing import Optional, List
import logging

from ..ports.repositories import IMerchantRepository
from ..ports.external import IShopifyClient
from ..dtos.requests import CreateMerchantDTO, UpdateMerchantDTO
from ...domain.entities.merchant import Merchant
from ...domain.value_objects.identifiers import MerchantId, new_merchant_id
from ...domain.value_objects.result import Result, Success, Failure, bind_result
from ...domain.value_objects.shop import ShopDomain
from ...domain.entities.subscription import SubscriptionTier
from ...domain.entities.settings import MerchantSettings

logger = logging.getLogger(__name__)


class MerchantError:
    """Error types for merchant operations."""
    pass


@dataclass(frozen=True)
class MerchantNotFound(MerchantError):
    id: MerchantId


@dataclass(frozen=True)
class ShopNotFound(MerchantError):
    domain: str


@dataclass(frozen=True)
class MerchantAlreadyExists(MerchantError):
    domain: str


@dataclass(frozen=True)
class ValidationError(MerchantError):
    message: str


@dataclass
class MerchantService:
    """
    Application service for Merchant operations.
    
    Categorical interpretation:
    - Morphisms in Kleisli[IO[Either[MerchantError, _]]]
    - Composition follows monad laws
    
    Certificates:
    - monad.cert.yaml#io_associativity
    - kleisli.cert.yaml#kleisli_assoc
    """
    
    repository: IMerchantRepository
    shopify_client: IShopifyClient
    
    async def create_merchant(
        self, 
        dto: CreateMerchantDTO
    ) -> Result[MerchantError, Merchant]:
        """
        Create a new merchant.
        
        Morphism: CreateMerchantDTO → IO[Either[MerchantError, Merchant]]
        
        Composition:
        1. validate_input: DTO → Either[ValidationError, ValidatedDTO]
        2. verify_shop: ValidatedDTO → IO[Either[ShopNotFound, ShopData]]
        3. create_entity: ShopData → Merchant
        4. persist: Merchant → IO[Either[PersistError, Merchant]]
        
        Certificate: composition.cert.yaml#kleisli_io_assoc
        """
        # Step 1: Validate input (pure)
        validation_result = self._validate_create_dto(dto)
        if isinstance(validation_result, Failure):
            return validation_result
        
        # Step 2: Verify shop exists with Shopify (IO)
        shop_result = await self.shopify_client.get_shop(dto.shop_domain)
        if isinstance(shop_result, Failure):
            return Failure(ShopNotFound(dto.shop_domain))
        
        # Step 3: Create domain entity (pure)
        merchant = Merchant(
            id=new_merchant_id(),
            shop_domain=ShopDomain(dto.shop_domain),
            subscription_tier=SubscriptionTier.FREE,
            settings=MerchantSettings.default(),
            created_at=datetime.utcnow(),
            updated_at=datetime.utcnow(),
        )
        
        # Step 4: Persist via repository (IO)
        persist_result = await self.repository.create(merchant)
        if isinstance(persist_result, Failure):
            return Failure(MerchantAlreadyExists(dto.shop_domain))
        
        logger.info(f"Created merchant {merchant.id} for {dto.shop_domain}")
        return persist_result
    
    async def get_merchant(
        self, 
        id: MerchantId
    ) -> Result[MerchantError, Optional[Merchant]]:
        """
        Get merchant by ID.
        
        Morphism: MerchantId → IO[Either[MerchantError, Option[Merchant]]]
        
        Direct repository counit (ε) application.
        """
        return await self.repository.get(id)
    
    async def update_merchant(
        self,
        id: MerchantId,
        dto: UpdateMerchantDTO
    ) -> Result[MerchantError, Merchant]:
        """
        Update existing merchant.
        
        Morphism: (MerchantId, UpdateDTO) → IO[Either[MerchantError, Merchant]]
        
        Composition: get ∘ modify ∘ persist
        Uses associativity from composition.cert.yaml
        """
        # Get current (ε)
        get_result = await self.repository.get(id)
        if isinstance(get_result, Failure):
            return get_result
        
        merchant = get_result.value
        if merchant is None:
            return Failure(MerchantNotFound(id))
        
        # Apply modifications (pure)
        updated = merchant.with_updated(
            subscription_tier=dto.subscription_tier or merchant.subscription_tier,
            settings=dto.settings or merchant.settings,
        )
        
        # Persist (η)
        return await self.repository.update(updated)
    
    async def delete_merchant(
        self,
        id: MerchantId
    ) -> Result[MerchantError, bool]:
        """
        Delete merchant.
        
        Morphism: MerchantId → IO[Either[MerchantError, Bool]]
        """
        return await self.repository.delete(id)
    
    async def list_merchants(
        self,
        offset: int = 0,
        limit: int = 100
    ) -> Result[MerchantError, List[Merchant]]:
        """
        List all merchants with pagination.
        
        Morphism: (offset, limit) → IO[Either[MerchantError, List[Merchant]]]
        """
        return await self.repository.list(offset, limit)
    
    def _validate_create_dto(
        self, 
        dto: CreateMerchantDTO
    ) -> Result[MerchantError, CreateMerchantDTO]:
        """
        Validate creation DTO.
        
        Pure function: DTO → Either[ValidationError, DTO]
        """
        if not dto.shop_domain:
            return Failure(ValidationError("shop_domain is required"))
        
        if not dto.shop_domain.endswith(".myshopify.com"):
            return Failure(ValidationError("Invalid Shopify domain format"))
        
        return Success(dto)
```

### Kleisli Composition Patterns

```python
# generated/python/src/{project}/application/services/analysis_service.py

from __future__ import annotations
from dataclasses import dataclass
from typing import Optional, List
import logging

from ..ports.repositories import IAnalysisRepository, IProfileRepository
from ..ports.external import IGroqClient, IPhotoStorage
from ..dtos.requests import CreateAnalysisDTO
from ...domain.entities.analysis import Analysis, AnalysisStatus
from ...domain.value_objects.identifiers import AnalysisId, ProfileId, new_analysis_id
from ...domain.value_objects.result import Result, Success, Failure, bind_result

logger = logging.getLogger(__name__)


@dataclass
class AnalysisService:
    """
    Service for photo analysis operations.
    
    Demonstrates complex Kleisli composition:
    - Multiple external calls
    - Effect sequencing
    - Error short-circuiting
    
    Certificate: monad.cert.yaml#io_associativity
    """
    
    analysis_repository: IAnalysisRepository
    profile_repository: IProfileRepository
    groq_client: IGroqClient
    photo_storage: IPhotoStorage
    
    async def create_and_analyze(
        self,
        dto: CreateAnalysisDTO
    ) -> Result[AnalysisError, Analysis]:
        """
        Create analysis and run AI analysis.
        
        Kleisli composition chain:
        
        validate
          ↓ (>>=)
        verify_profile
          ↓ (>>=)
        upload_photo
          ↓ (>>=)
        create_analysis
          ↓ (>>=)
        run_ai_analysis
          ↓ (>>=)
        update_with_results
        
        Each step: A → IO[Either[E, B]]
        Composition: Kleisli fish operator (>=>)
        
        Certificate: kleisli.cert.yaml#kleisli_assoc
        """
        # The composition is associative, so we can structure as we prefer
        # (a >=> b) >=> c = a >=> (b >=> c)
        
        # Step 1: Validate
        validated = self._validate_dto(dto)
        if isinstance(validated, Failure):
            return validated
        
        # Step 2: Verify profile exists
        profile_result = await self.profile_repository.get(dto.profile_id)
        if isinstance(profile_result, Failure):
            return Failure(AnalysisError.profile_fetch_failed())
        if profile_result.value is None:
            return Failure(AnalysisError.profile_not_found(dto.profile_id))
        
        # Step 3: Upload photo to storage
        upload_result = await self.photo_storage.upload(
            dto.photo_data,
            f"analysis/{new_analysis_id()}"
        )
        if isinstance(upload_result, Failure):
            return Failure(AnalysisError.upload_failed(upload_result.error))
        photo_url = upload_result.value
        
        # Step 4: Create analysis record
        analysis = Analysis(
            id=new_analysis_id(),
            profile_id=dto.profile_id,
            photo_url=photo_url,
            status=AnalysisStatus.PENDING,
            results=None,
            created_at=datetime.utcnow(),
        )
        
        create_result = await self.analysis_repository.create(analysis)
        if isinstance(create_result, Failure):
            return Failure(AnalysisError.persist_failed())
        analysis = create_result.value
        
        # Step 5: Run AI analysis (can be async/background)
        ai_result = await self.groq_client.analyze_photo(photo_url)
        if isinstance(ai_result, Failure):
            # Update status to failed
            failed_analysis = analysis.with_status(AnalysisStatus.FAILED)
            await self.analysis_repository.update(failed_analysis)
            return Failure(AnalysisError.ai_analysis_failed())
        
        # Step 6: Update with results
        completed_analysis = analysis.with_results(
            results=ai_result.value,
            status=AnalysisStatus.COMPLETED
        )
        
        return await self.analysis_repository.update(completed_analysis)
    
    async def get_analysis(
        self,
        id: AnalysisId
    ) -> Result[AnalysisError, Optional[Analysis]]:
        """Simple counit application."""
        return await self.analysis_repository.get(id)
    
    async def get_by_profile(
        self,
        profile_id: ProfileId
    ) -> Result[AnalysisError, List[Analysis]]:
        """Query analyses for a profile."""
        return await self.analysis_repository.get_by_profile(profile_id)
    
    def _validate_dto(
        self,
        dto: CreateAnalysisDTO
    ) -> Result[AnalysisError, CreateAnalysisDTO]:
        """Pure validation."""
        if not dto.profile_id:
            return Failure(AnalysisError.validation("profile_id required"))
        if not dto.photo_data:
            return Failure(AnalysisError.validation("photo_data required"))
        return Success(dto)
```

## External Port Interfaces

```python
# generated/python/src/{project}/application/ports/external.py

from __future__ import annotations
from abc import ABC, abstractmethod
from typing import Optional

from ...domain.value_objects.result import Result


class IShopifyClient(ABC):
    """
    Port for Shopify API integration.
    
    Categorical: Domain ⊣ External adjunction interface
    """
    
    @abstractmethod
    async def get_shop(self, domain: str) -> Result[str, dict]:
        """Fetch shop data from Shopify."""
        ...
    
    @abstractmethod
    async def get_products(
        self, 
        domain: str,
        limit: int = 50
    ) -> Result[str, list]:
        """Fetch products from shop."""
        ...


class IGroqClient(ABC):
    """Port for Groq AI API integration."""
    
    @abstractmethod
    async def analyze_photo(self, photo_url: str) -> Result[str, dict]:
        """Run AI analysis on photo."""
        ...


class IPhotoStorage(ABC):
    """Port for photo storage."""
    
    @abstractmethod
    async def upload(self, data: bytes, path: str) -> Result[str, str]:
        """Upload photo, return URL."""
        ...
    
    @abstractmethod
    async def delete(self, path: str) -> Result[str, bool]:
        """Delete photo."""
        ...
```

## Template Structure

```python
# Service template

from __future__ import annotations
from dataclasses import dataclass
from typing import Optional, List
import logging

{% for port in ports %}
from ..ports.{{ port.module }} import {{ port.interface }}
{% endfor %}
from ..dtos.requests import {{ dtos.create }}, {{ dtos.update }}
from ...domain.entities.{{ entity_lower }} import {{ entity }}
from ...domain.value_objects.identifiers import {{ entity }}Id
from ...domain.value_objects.result import Result, Success, Failure

logger = logging.getLogger(__name__)


@dataclass
class {{ entity }}Service:
    """
    Application service for {{ entity }} operations.
    
    Categorical: Morphisms in Kleisli[IO[Either[{{ entity }}Error, _]]]
    Certificate: monad.cert.yaml#io_associativity
    """
    
    {% for dep in dependencies %}
    {{ dep.name }}: {{ dep.type }}
    {% endfor %}
    
    {% for morphism in morphisms %}
    {{ morphism.implementation }}
    {% endfor %}
```

## Validation Checks

```yaml
validation:
  services_generated:
    check: "All aggregate roots have services"
    
  morphisms_implemented:
    check: "All specified morphisms have implementations"
    
  dependencies_injected:
    check: "All ports properly injected"
    
  effects_handled:
    check: "All async operations return Result"
```

## Next Skills

Output feeds into:
- `handler-generator`
