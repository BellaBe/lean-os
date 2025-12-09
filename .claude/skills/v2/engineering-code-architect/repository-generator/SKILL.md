---
name: repository-generator
description: |
  Generate repository implementations from adjunction maps. Creates SQLAlchemy-based
  repositories that implement the Free ⊣ Repository adjunction. Includes database
  models and port interfaces.
  Input: maps/adjunctions/repository.map.yaml, entities
  Output: generated/python/src/{project}/infrastructure/repositories/*.py
---

# Repository Generator

Generate repositories implementing Free ⊣ Repository adjunction.

## Purpose

Transform adjunction maps into repository implementations:
1. Generate port interfaces (abstract repositories)
2. Generate SQLAlchemy database models
3. Generate concrete repository implementations
4. Implement unit (η) and counit (ε) operations

## Input

- `maps/adjunctions/repository.map.yaml` - Repository adjunction maps
- `generated/.../domain/entities/*.py` - Generated entities
- `maps/primitives/*.map.yaml` - Type mappings

## Output

```
generated/python/src/{project}/
├── application/
│   └── ports/
│       ├── __init__.py
│       └── repositories.py    # Port interfaces
└── infrastructure/
    ├── models/
    │   ├── __init__.py
    │   └── database.py        # SQLAlchemy models
    └── repositories/
        ├── __init__.py
        ├── base.py            # Base repository
        ├── merchant_repository.py
        ├── profile_repository.py
        └── analysis_repository.py
```

## Adjunction Implementation

### Mathematical Foundation

```
Free ⊣ Repository adjunction:

  Free: Storage → Domain     (to_domain)
  Repository: Domain → Storage  (from_domain)
  
  Unit η: Domain → Repository(Free(Domain))
    - Save entity, get back stored version
    - η_A: A → R(F(A))
    
  Counit ε: Free(Repository(Domain)) → Domain
    - Load stored entity, convert to domain
    - ε_A: F(R(A)) → A
    
  Triangle identities ensure round-trip correctness:
    - (ε ∘ Free) ∘ (Free ∘ η) = id  (save then load = identity)
    - (Repository ∘ ε) ∘ (η ∘ Repository) = id
```

## Generation Rules

### Port Interface (Abstract Repository)

```yaml
# From repository.map.yaml
ports:
  MerchantRepository:
    entity: Merchant
    operations:
      - create: "η component - persist entity"
      - get: "ε component - retrieve entity"
      - update: "ε ∘ modify ∘ η"
      - delete: "annihilate"
      - list: "query multiple"
```

Generated Python:

```python
# generated/python/src/{project}/application/ports/repositories.py

from __future__ import annotations
from abc import ABC, abstractmethod
from typing import Optional, List
from uuid import UUID

from ...domain.entities.merchant import Merchant
from ...domain.entities.profile import Profile
from ...domain.entities.analysis import Analysis
from ...domain.value_objects.identifiers import MerchantId, ProfileId, AnalysisId
from ...domain.value_objects.result import Result


class IMerchantRepository(ABC):
    """
    Port interface for Merchant persistence.
    
    Categorical interpretation:
    - Defines the adjunction interface
    - Implementations provide Free ⊣ Repository
    
    Certificate: adjunction.cert.yaml#repository_adjunction_exists
    """
    
    @abstractmethod
    async def create(self, merchant: Merchant) -> Result[str, Merchant]:
        """
        Unit (η) component: Persist merchant to storage.
        
        Categorical: η_Merchant: Merchant → Storage[Merchant]
        Invariant: create(m).get(id) ≅ m
        """
        ...
    
    @abstractmethod
    async def get(self, id: MerchantId) -> Result[str, Optional[Merchant]]:
        """
        Counit (ε) component: Retrieve merchant from storage.
        
        Categorical: ε_Merchant: StoredMerchant → Merchant
        """
        ...
    
    @abstractmethod
    async def update(self, merchant: Merchant) -> Result[str, Merchant]:
        """
        Update: ε ∘ modify ∘ η composition.
        
        Categorical: Get current, apply changes, persist
        """
        ...
    
    @abstractmethod
    async def delete(self, id: MerchantId) -> Result[str, bool]:
        """
        Delete: Annihilate the stored entity.
        """
        ...
    
    @abstractmethod
    async def list(
        self,
        offset: int = 0,
        limit: int = 100
    ) -> Result[str, List[Merchant]]:
        """
        List: Query multiple entities.
        """
        ...


class IProfileRepository(ABC):
    """Port interface for Profile persistence."""
    
    @abstractmethod
    async def create(self, profile: Profile) -> Result[str, Profile]:
        ...
    
    @abstractmethod
    async def get(self, id: ProfileId) -> Result[str, Optional[Profile]]:
        ...
    
    @abstractmethod
    async def get_by_merchant(
        self, 
        merchant_id: MerchantId
    ) -> Result[str, List[Profile]]:
        ...
    
    @abstractmethod
    async def update(self, profile: Profile) -> Result[str, Profile]:
        ...
    
    @abstractmethod
    async def delete(self, id: ProfileId) -> Result[str, bool]:
        ...


class IAnalysisRepository(ABC):
    """Port interface for Analysis persistence."""
    
    @abstractmethod
    async def create(self, analysis: Analysis) -> Result[str, Analysis]:
        ...
    
    @abstractmethod
    async def get(self, id: AnalysisId) -> Result[str, Optional[Analysis]]:
        ...
    
    @abstractmethod
    async def get_by_profile(
        self,
        profile_id: ProfileId
    ) -> Result[str, List[Analysis]]:
        ...
```

### SQLAlchemy Models (Storage Objects)

```python
# generated/python/src/{project}/infrastructure/models/database.py

from __future__ import annotations
from datetime import datetime
from typing import Optional, List
from uuid import UUID

from sqlalchemy import String, DateTime, ForeignKey, JSON, Enum as SQLEnum
from sqlalchemy.orm import DeclarativeBase, Mapped, mapped_column, relationship
from sqlalchemy.dialects.postgresql import UUID as PGUUID

from ...domain.entities.merchant import Merchant
from ...domain.entities.subscription import SubscriptionTier
from ...domain.value_objects.identifiers import MerchantId


class Base(DeclarativeBase):
    """SQLAlchemy declarative base."""
    pass


class MerchantModel(Base):
    """
    Storage model for Merchant.
    
    Categorical interpretation:
    - Object in Storage category
    - Repository functor maps Merchant → MerchantModel
    
    Implements:
    - from_domain: Repository functor (Domain → Storage)
    - to_domain: Free functor (Storage → Domain)
    """
    
    __tablename__ = "merchants"
    
    id: Mapped[UUID] = mapped_column(PGUUID(as_uuid=True), primary_key=True)
    shop_domain: Mapped[str] = mapped_column(String(255), unique=True, index=True)
    subscription_tier: Mapped[str] = mapped_column(
        SQLEnum(SubscriptionTier), 
        default=SubscriptionTier.FREE
    )
    settings: Mapped[dict] = mapped_column(JSON, default=dict)
    created_at: Mapped[datetime] = mapped_column(DateTime, default=datetime.utcnow)
    updated_at: Mapped[datetime] = mapped_column(
        DateTime, 
        default=datetime.utcnow,
        onupdate=datetime.utcnow
    )
    
    # Relationships
    profiles: Mapped[List["ProfileModel"]] = relationship(
        back_populates="merchant",
        cascade="all, delete-orphan"
    )
    
    @classmethod
    def from_domain(cls, merchant: Merchant) -> MerchantModel:
        """
        Repository functor: Domain → Storage.
        
        Categorical: R(Merchant) = MerchantModel
        """
        return cls(
            id=merchant.id,
            shop_domain=str(merchant.shop_domain),
            subscription_tier=merchant.subscription_tier,
            settings=merchant.settings.to_dict(),
            created_at=merchant.created_at,
            updated_at=merchant.updated_at,
        )
    
    def to_domain(self) -> Merchant:
        """
        Free functor: Storage → Domain.
        
        Categorical: F(MerchantModel) = Merchant
        Certificate: adjunction.cert.yaml#repository_left_triangle
        """
        from ...domain.entities.merchant import Merchant
        from ...domain.value_objects.identifiers import MerchantId
        from ...domain.value_objects.shop import ShopDomain
        from ...domain.entities.settings import MerchantSettings
        
        return Merchant(
            id=MerchantId(self.id),
            shop_domain=ShopDomain(self.shop_domain),
            subscription_tier=self.subscription_tier,
            settings=MerchantSettings.from_dict(self.settings),
            created_at=self.created_at,
            updated_at=self.updated_at,
        )


class ProfileModel(Base):
    """Storage model for Profile."""
    
    __tablename__ = "profiles"
    
    id: Mapped[UUID] = mapped_column(PGUUID(as_uuid=True), primary_key=True)
    merchant_id: Mapped[UUID] = mapped_column(
        PGUUID(as_uuid=True),
        ForeignKey("merchants.id", ondelete="CASCADE"),
        index=True
    )
    name: Mapped[str] = mapped_column(String(255))
    preferences: Mapped[dict] = mapped_column(JSON, default=dict)
    created_at: Mapped[datetime] = mapped_column(DateTime, default=datetime.utcnow)
    
    merchant: Mapped["MerchantModel"] = relationship(back_populates="profiles")
    
    @classmethod
    def from_domain(cls, profile) -> ProfileModel:
        return cls(
            id=profile.id,
            merchant_id=profile.merchant_id,
            name=profile.name,
            preferences=profile.preferences.to_dict(),
            created_at=profile.created_at,
        )
    
    def to_domain(self):
        from ...domain.entities.profile import Profile
        from ...domain.value_objects.identifiers import ProfileId, MerchantId
        
        return Profile(
            id=ProfileId(self.id),
            merchant_id=MerchantId(self.merchant_id),
            name=self.name,
            preferences=self.preferences,
            created_at=self.created_at,
        )
```

### Concrete Repository Implementation

```python
# generated/python/src/{project}/infrastructure/repositories/merchant_repository.py

from __future__ import annotations
from typing import Optional, List
import logging

from sqlalchemy import select, delete
from sqlalchemy.ext.asyncio import AsyncSession
from sqlalchemy.exc import IntegrityError

from ...application.ports.repositories import IMerchantRepository
from ...domain.entities.merchant import Merchant
from ...domain.value_objects.identifiers import MerchantId
from ...domain.value_objects.result import Result, Success, Failure
from ..models.database import MerchantModel

logger = logging.getLogger(__name__)


class SqlMerchantRepository(IMerchantRepository):
    """
    SQLAlchemy implementation of Merchant repository.
    
    Implements Free ⊣ Repository adjunction:
    - create: Unit (η) - persist domain entity
    - get: Counit (ε) - retrieve and convert to domain
    - update: η ∘ modify ∘ ε - round-trip with modification
    - delete: Annihilate stored entity
    
    Certificates:
    - adjunction.cert.yaml#repository_adjunction_exists
    - adjunction.cert.yaml#repository_left_triangle
    - adjunction.cert.yaml#repository_right_triangle
    """
    
    def __init__(self, session: AsyncSession) -> None:
        self._session = session
    
    async def create(self, merchant: Merchant) -> Result[str, Merchant]:
        """
        Unit (η): Domain → Storage[Domain].
        
        Apply Repository functor, persist, apply Free functor.
        Triangle identity ensures: to_domain(from_domain(m)) ≅ m
        """
        try:
            # Apply Repository functor: Merchant → MerchantModel
            model = MerchantModel.from_domain(merchant)
            
            self._session.add(model)
            await self._session.flush()
            await self._session.refresh(model)
            
            # Apply Free functor: MerchantModel → Merchant
            # This completes the η application
            return Success(model.to_domain())
            
        except IntegrityError as e:
            logger.error(f"Integrity error creating merchant: {e}")
            return Failure(f"Merchant with domain already exists")
        except Exception as e:
            logger.exception(f"Error creating merchant: {e}")
            return Failure(str(e))
    
    async def get(self, id: MerchantId) -> Result[str, Optional[Merchant]]:
        """
        Counit (ε): Storage[Domain] → Domain.
        
        Query storage, apply Free functor to result.
        """
        try:
            stmt = select(MerchantModel).where(MerchantModel.id == id)
            result = await self._session.execute(stmt)
            model = result.scalar_one_or_none()
            
            if model is None:
                return Success(None)
            
            # Apply Free functor: MerchantModel → Merchant
            return Success(model.to_domain())
            
        except Exception as e:
            logger.exception(f"Error getting merchant {id}: {e}")
            return Failure(str(e))
    
    async def update(self, merchant: Merchant) -> Result[str, Merchant]:
        """
        Update: ε ∘ modify ∘ η composition.
        
        1. Get current (ε)
        2. Apply modification (external)
        3. Persist (η)
        
        Associativity from composition.cert.yaml ensures correct sequencing.
        """
        try:
            stmt = select(MerchantModel).where(MerchantModel.id == merchant.id)
            result = await self._session.execute(stmt)
            model = result.scalar_one_or_none()
            
            if model is None:
                return Failure(f"Merchant {merchant.id} not found")
            
            # Apply Repository functor updates
            model.shop_domain = str(merchant.shop_domain)
            model.subscription_tier = merchant.subscription_tier
            model.settings = merchant.settings.to_dict()
            model.updated_at = merchant.updated_at
            
            await self._session.flush()
            await self._session.refresh(model)
            
            # Apply Free functor
            return Success(model.to_domain())
            
        except IntegrityError as e:
            logger.error(f"Integrity error updating merchant: {e}")
            return Failure(f"Update violates constraints")
        except Exception as e:
            logger.exception(f"Error updating merchant: {e}")
            return Failure(str(e))
    
    async def delete(self, id: MerchantId) -> Result[str, bool]:
        """
        Delete: Annihilate the stored entity.
        
        Removes from storage category entirely.
        """
        try:
            stmt = delete(MerchantModel).where(MerchantModel.id == id)
            result = await self._session.execute(stmt)
            return Success(result.rowcount > 0)
            
        except Exception as e:
            logger.exception(f"Error deleting merchant {id}: {e}")
            return Failure(str(e))
    
    async def list(
        self,
        offset: int = 0,
        limit: int = 100
    ) -> Result[str, List[Merchant]]:
        """List merchants with pagination."""
        try:
            stmt = (
                select(MerchantModel)
                .offset(offset)
                .limit(limit)
                .order_by(MerchantModel.created_at.desc())
            )
            result = await self._session.execute(stmt)
            models = result.scalars().all()
            
            # Apply Free functor to each
            return Success([m.to_domain() for m in models])
            
        except Exception as e:
            logger.exception(f"Error listing merchants: {e}")
            return Failure(str(e))
```

## Template Structure

```python
# Base template for repositories

from __future__ import annotations
from typing import Optional, List
import logging

from sqlalchemy import select, delete
from sqlalchemy.ext.asyncio import AsyncSession
from sqlalchemy.exc import IntegrityError

from ...application.ports.repositories import I{{ entity }}Repository
from ...domain.entities.{{ entity_lower }} import {{ entity }}
from ...domain.value_objects.identifiers import {{ entity }}Id
from ...domain.value_objects.result import Result, Success, Failure
from ..models.database import {{ entity }}Model

logger = logging.getLogger(__name__)


class Sql{{ entity }}Repository(I{{ entity }}Repository):
    """
    SQLAlchemy implementation of {{ entity }} repository.
    
    Implements Free ⊣ Repository adjunction.
    
    Certificates:
    - adjunction.cert.yaml#repository_adjunction_exists
    """
    
    def __init__(self, session: AsyncSession) -> None:
        self._session = session
    
    {% for operation in operations %}
    {{ operation.code }}
    {% endfor %}
```

## Validation Checks

```yaml
validation:
  ports_defined:
    check: "All entities have port interfaces"
    
  models_match_entities:
    check: "Model fields correspond to entity fields"
    
  adjunction_implemented:
    check: "from_domain and to_domain exist"
    
  crud_complete:
    check: "All CRUD operations implemented"
```

## Next Skills

Output feeds into:
- `service-generator`
