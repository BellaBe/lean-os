---
name: module-mapper
description: |
  Map categorical structures to module/service organization. Produces service structure,
  repository layout, handler organization, and dependency graph. Categories become
  packages/namespaces with proper layering (onion/hexagonal/clean architecture).
  Input: All other maps, specifications, standards
  Output: maps/modules/*.map.yaml
---

# Module Mapper

Map categorical structure to module organization.

## Purpose

Transform categories into service architecture:
1. Domain categories → Service modules
2. Functors → Adapter/mapper modules
3. Adjunctions → Repository modules
4. HTTP category → Handler modules
5. Dependency injection → Module graph

## Input

- All maps from previous mappers
- `specifications/v{X}/services.spec.yaml` - Service definitions
- `standards/categories/*.std.yaml` - Category structure

## Output

```
maps/modules/
├── services.map.yaml      # Service layer structure
├── repositories.map.yaml  # Repository layer structure
└── handlers.map.yaml      # HTTP handler structure
```

## Architecture Pattern

### Onion Architecture Mapping

```yaml
architecture:
  pattern: onion
  description: |
    Categories map to onion layers:
    - Domain category → Core domain layer
    - Storage adjunction → Repository interfaces + implementations
    - External functor → External adapter interfaces + implementations
    - HTTP functor → API layer
    
  layers:
    # Innermost: pure domain
    domain:
      categorical: "Domain category objects and pure morphisms"
      contains:
        - entities
        - value_objects
        - domain_services
        - domain_events
      dependencies: none
      
    # Application layer
    application:
      categorical: "Kleisli morphisms with effects"
      contains:
        - use_cases
        - application_services
        - ports (interfaces)
      dependencies: [domain]
      
    # Infrastructure layer
    infrastructure:
      categorical: "Functor implementations"
      contains:
        - repositories
        - external_clients
        - adapters
      dependencies: [domain, application]
      
    # API layer
    api:
      categorical: "HTTP functor"
      contains:
        - handlers
        - routes
        - middleware
        - dtos
      dependencies: [application]
```

## Services Mapping

### Schema

```yaml
# maps/modules/services.map.yaml

services:
  # Service module pattern
  pattern:
    categorical: |
      For each aggregate root in Domain category,
      create a service module with morphisms as methods.
      
    structure: |
      {module}/
      ├── __init__.py
      ├── domain/
      │   ├── entities.py      # Domain objects
      │   ├── value_objects.py # Value objects
      │   └── events.py        # Domain events
      ├── application/
      │   ├── services.py      # Application services
      │   ├── dtos.py          # Data transfer objects
      │   └── ports/           # Interface definitions
      │       ├── repositories.py
      │       └── external.py
      └── infrastructure/
          ├── repositories.py  # Repository implementations
          ├── external.py      # External client implementations
          └── models.py        # ORM models

  # Service mappings
  mappings:
    - aggregate: Merchant
      module: merchant
      categorical: "Objects and morphisms related to Merchant"
      services:
        - name: MerchantService
          morphisms:
            - create_merchant
            - get_merchant
            - update_merchant
            - delete_merchant
          ports:
            - MerchantRepository
            - ShopifyClient
            
    - aggregate: Profile
      module: profile
      categorical: "Profile aggregate operations"
      services:
        - name: ProfileService
          morphisms:
            - create_profile
            - get_profile
            - update_profile
          ports:
            - ProfileRepository
            
    - aggregate: Analysis
      module: analysis
      categorical: "Analysis aggregate operations"
      services:
        - name: AnalysisService
          morphisms:
            - create_analysis
            - analyze_photo
            - get_analysis
          ports:
            - AnalysisRepository
            - GroqClient
            - PhotoStorage

  # Implementation targets
  targets:
    python:
      service_template: |
        from dataclasses import dataclass
        from returns.result import Result, Success, Failure
        
        from {module}.domain.entities import {Entity}
        from {module}.application.ports.repositories import {Entity}Repository
        from {module}.application.dtos import (
            Create{Entity}Input,
            Update{Entity}Input,
        )
        
        
        @dataclass
        class {Entity}Service:
            """
            Application service for {Entity} aggregate.
            
            Categorical interpretation:
            - Methods are morphisms in Kleisli[IO[Either[E, _]]]
            - Dependencies are ports (adjunction interfaces)
            """
            repository: {Entity}Repository
            
            async def create(
                self, 
                input: Create{Entity}Input
            ) -> Result[{Entity}, Create{Entity}Error]:
                """Morphism: Create{Entity}Input → IO[Either[E, {Entity}]]"""
                entity = {Entity}.from_input(input)
                return await self.repository.create(entity)
                
            async def get(
                self, 
                id: {Entity}Id
            ) -> Result[{Entity}, NotFoundError]:
                """Morphism: {Entity}Id → IO[Either[NotFound, {Entity}]]"""
                return await self.repository.get(id)
                
            async def update(
                self,
                id: {Entity}Id,
                input: Update{Entity}Input,
            ) -> Result[{Entity}, UpdateError]:
                """Morphism: ({Entity}Id, Patch) → IO[Either[E, {Entity}]]"""
                existing = await self.repository.get(id)
                if isinstance(existing, Failure):
                    return Failure(UpdateError.not_found(id))
                    
                updated = existing.unwrap().apply_update(input)
                return await self.repository.update(updated)
                
      port_template: |
        from abc import ABC, abstractmethod
        from returns.result import Result
        
        from {module}.domain.entities import {Entity}
        
        
        class {Entity}Repository(ABC):
            """
            Port for {Entity} persistence.
            
            Categorical interpretation:
            - Interface for Repository adjunction
            - Concrete implementations provide the functor
            """
            
            @abstractmethod
            async def create(
                self, 
                entity: {Entity}
            ) -> Result[{Entity}, CreateError]:
                """Unit: {Entity} → Stored[{Entity}]"""
                ...
                
            @abstractmethod
            async def get(
                self, 
                id: {Entity}Id
            ) -> Result[{Entity}, NotFoundError]:
                """Counit: {Entity}Id → {Entity}"""
                ...
                
            @abstractmethod
            async def update(
                self, 
                entity: {Entity}
            ) -> Result[{Entity}, UpdateError]:
                """Unit after modification"""
                ...
                
    typescript:
      service_template: |
        import { Either, left, right } from 'fp-ts/Either';
        import { {Entity} } from '../domain/entities';
        import { {Entity}Repository } from './ports/repositories';
        
        export class {Entity}Service {
          constructor(private readonly repository: {Entity}Repository) {}
          
          async create(
            input: Create{Entity}Input
          ): Promise<Either<Create{Entity}Error, {Entity}>> {
            const entity = {Entity}.fromInput(input);
            return this.repository.create(entity);
          }
          
          async get(
            id: {Entity}Id
          ): Promise<Either<NotFoundError, {Entity}>> {
            return this.repository.get(id);
          }
        }
```

## Repositories Mapping

### Schema

```yaml
# maps/modules/repositories.map.yaml

repositories:
  # Repository pattern from adjunction
  pattern:
    categorical: |
      Repository implements the Repository adjunction:
      Free ⊣ Repository
      
      - from_domain: Apply Repository functor (Domain → Storage)
      - to_domain: Apply Free functor (Storage → Domain)
      
    interface: "Defined in application/ports/repositories.py"
    implementation: "Defined in infrastructure/repositories.py"
    
  # Repository mappings
  mappings:
    - entity: Merchant
      repository: MerchantRepository
      model: MerchantModel
      operations:
        - create
        - get
        - update
        - delete
        - list
        
    - entity: Profile
      repository: ProfileRepository
      model: ProfileModel
      operations:
        - create
        - get
        - update
        - list_by_merchant
        
  # Implementation targets
  targets:
    python:
      repository_template: |
        from sqlalchemy import select, delete
        from sqlalchemy.ext.asyncio import AsyncSession
        from returns.result import Result, Success, Failure
        
        from {module}.application.ports.repositories import {Entity}Repository
        from {module}.domain.entities import {Entity}
        from {module}.infrastructure.models import {Entity}Model
        
        
        class Sql{Entity}Repository({Entity}Repository):
            """
            SQLAlchemy implementation of {Entity}Repository.
            
            Implements the Free ⊣ Repository adjunction:
            - from_domain (η): Domain → Storage
            - to_domain (ε): Storage → Domain
            """
            
            def __init__(self, session: AsyncSession):
                self.session = session
                
            async def create(
                self, 
                entity: {Entity}
            ) -> Result[{Entity}, CreateError]:
                """Apply unit η, then counit ε"""
                try:
                    model = {Entity}Model.from_domain(entity)  # η
                    self.session.add(model)
                    await self.session.flush()
                    return Success(model.to_domain())  # ε
                except IntegrityError as e:
                    return Failure(CreateError.from_exception(e))
                    
            async def get(
                self, 
                id: {Entity}Id
            ) -> Result[{Entity}, NotFoundError]:
                """Apply counit ε directly"""
                query = select({Entity}Model).where({Entity}Model.id == id)
                result = await self.session.execute(query)
                row = result.scalar_one_or_none()
                
                if row is None:
                    return Failure(NotFoundError('{entity}', id))
                    
                return Success(row.to_domain())  # ε
                
            async def update(
                self, 
                entity: {Entity}
            ) -> Result[{Entity}, UpdateError]:
                """η ∘ modify ∘ ε pattern"""
                query = select({Entity}Model).where(
                    {Entity}Model.id == entity.id
                )
                result = await self.session.execute(query)
                row = result.scalar_one_or_none()
                
                if row is None:
                    return Failure(UpdateError.not_found(entity.id))
                    
                row.update_from_domain(entity)
                await self.session.flush()
                return Success(row.to_domain())
                
            async def delete(
                self, 
                id: {Entity}Id
            ) -> Result[None, DeleteError]:
                """Remove from storage category"""
                query = delete({Entity}Model).where({Entity}Model.id == id)
                result = await self.session.execute(query)
                
                if result.rowcount == 0:
                    return Failure(DeleteError.not_found(id))
                    
                return Success(None)
```

## Handlers Mapping

### Schema

```yaml
# maps/modules/handlers.map.yaml

handlers:
  # Handler pattern from HTTP functor
  pattern:
    categorical: |
      Handlers implement the HTTP functor:
      Domain → HTTP
      
      Each domain morphism maps to an HTTP endpoint.
      Request/Response DTOs are the functor object map.
      
  # Handler mappings
  mappings:
    - service: MerchantService
      router: merchant_router
      prefix: "/api/v{version}/merchants"
      handlers:
        - morphism: create_merchant
          method: POST
          path: ""
          request: CreateMerchantRequest
          response: MerchantResponse
          
        - morphism: get_merchant
          method: GET
          path: "/{id}"
          response: MerchantResponse
          
        - morphism: update_merchant
          method: PATCH
          path: "/{id}"
          request: UpdateMerchantRequest
          response: MerchantResponse
          
        - morphism: delete_merchant
          method: DELETE
          path: "/{id}"
          
  # Implementation targets
  targets:
    python:
      router_template: |
        from fastapi import APIRouter, Depends, HTTPException
        
        from {module}.application.services import {Entity}Service
        from {module}.api.dtos import (
            Create{Entity}Request,
            Update{Entity}Request,
            {Entity}Response,
        )
        from core.dependencies import get_{entity}_service
        from core.auth import get_current_user
        
        router = APIRouter(prefix="/api/v1/{entities}", tags=["{entities}"])
        
        
        @router.post("", response_model={Entity}Response, status_code=201)
        async def create_{entity}(
            request: Create{Entity}Request,
            current_user: Identity = Depends(get_current_user),
            service: {Entity}Service = Depends(get_{entity}_service),
        ) -> {Entity}Response:
            """
            HTTP functor application: create_{entity}.
            
            Transform: HTTP request → Domain → HTTP response
            """
            result = await service.create(request.to_domain())
            
            match result:
                case Success(entity):
                    return {Entity}Response.from_domain(entity)
                case Failure(error):
                    raise HTTPException(
                        status_code=error.status_code,
                        detail=error.message,
                    )
                    
        @router.get("/{id}", response_model={Entity}Response)
        async def get_{entity}(
            id: UUID,
            current_user: Identity = Depends(get_current_user),
            service: {Entity}Service = Depends(get_{entity}_service),
        ) -> {Entity}Response:
            """HTTP functor application: get_{entity}."""
            result = await service.get({Entity}Id(id))
            
            match result:
                case Success(entity):
                    return {Entity}Response.from_domain(entity)
                case Failure(NotFoundError()):
                    raise HTTPException(status_code=404, detail="Not found")
                    
        @router.patch("/{id}", response_model={Entity}Response)
        async def update_{entity}(
            id: UUID,
            request: Update{Entity}Request,
            current_user: Identity = Depends(get_current_user),
            service: {Entity}Service = Depends(get_{entity}_service),
        ) -> {Entity}Response:
            """HTTP functor application: update_{entity}."""
            result = await service.update(
                {Entity}Id(id), 
                request.to_domain()
            )
            
            match result:
                case Success(entity):
                    return {Entity}Response.from_domain(entity)
                case Failure(error):
                    raise HTTPException(
                        status_code=error.status_code,
                        detail=error.message,
                    )
```

## Dependency Graph

```yaml
dependency_graph:
  description: |
    Module dependencies form a DAG respecting layer boundaries.
    
  structure:
    # API layer depends on Application
    api:
      depends_on: [application]
      provides: [handlers, routers, middleware]
      
    # Application layer depends on Domain
    application:
      depends_on: [domain]
      provides: [services, ports, dtos]
      
    # Infrastructure implements ports
    infrastructure:
      depends_on: [domain, application]
      provides: [repositories, clients, models]
      
    # Domain has no dependencies
    domain:
      depends_on: []
      provides: [entities, value_objects, events]
      
  # Dependency injection
  injection:
    pattern: "Constructor injection via factory functions"
    targets:
      python:
        template: |
          # dependencies.py
          from functools import lru_cache
          
          @lru_cache
          def get_database() -> AsyncEngine:
              return create_async_engine(settings.database_url)
              
          async def get_session() -> AsyncSession:
              engine = get_database()
              async with AsyncSession(engine) as session:
                  yield session
                  
          async def get_{entity}_repository(
              session: AsyncSession = Depends(get_session)
          ) -> {Entity}Repository:
              return Sql{Entity}Repository(session)
              
          async def get_{entity}_service(
              repository: {Entity}Repository = Depends(get_{entity}_repository)
          ) -> {Entity}Service:
              return {Entity}Service(repository)
```

## Validation

### Completeness Checks

```yaml
completeness:
  - all_aggregates_have_modules
  - all_services_have_handlers
  - all_ports_have_implementations
  - dependency_graph_complete
```

### Consistency Checks

```yaml
consistency:
  - no_circular_dependencies
  - layer_boundaries_respected
  - naming_conventions_followed
```

## Next Skills

Output feeds into:
- `maps-validator`
