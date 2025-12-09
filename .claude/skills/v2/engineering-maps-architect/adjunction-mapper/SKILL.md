---
name: adjunction-mapper
description: |
  Map categorical adjunctions to paired operation implementations. Produces repository
  patterns (Free ⊣ Repository), cache patterns (Forget ⊣ Cache), and external API
  patterns. Adjunctions become paired create/retrieve, cache/fetch operations.
  Input: standards/categories/*.std.yaml, primitives maps
  Output: maps/adjunctions/*.map.yaml
---

# Adjunction Mapper

Map adjunctions to bidirectional operation pairs.

## Purpose

Transform adjunctions into implementation patterns:
1. Free ⊣ Repository (persistence)
2. Forget ⊣ Cache (caching)
3. Domain ⊣ External (API integration)
4. Unit and counit as paired operations

## Input

- `standards/categories/storage.std.yaml` - Repository adjunction
- `standards/caching/cache.std.yaml` - Cache adjunction
- `standards/categories/external.std.yaml` - External adjunction
- `maps/primitives/*.map.yaml` - Type mappings

## Output

```
maps/adjunctions/
├── repository.map.yaml  # Free ⊣ Repository
├── cache.map.yaml       # Forget ⊣ Cache
└── external.map.yaml    # Domain ⊣ External
```

## Adjunction Structure

### Abstract Pattern

```yaml
adjunction_pattern:
  # L ⊣ R means L is left adjoint to R
  structure:
    left_adjoint: "L: C → D"
    right_adjoint: "R: D → C"
    unit: "η: Id_C → R∘L"
    counit: "ε: L∘R → Id_D"
    
  # Triangle identities
  laws:
    left_triangle: "(ε∘L) ∘ (L∘η) = id_L"
    right_triangle: "(R∘ε) ∘ (η∘R) = id_R"
    
  # Implementation pattern
  implementation:
    unit: "embed/wrap operation"
    counit: "extract/unwrap operation"
    round_trip: "η followed by ε gives back (almost) original"
```

## Repository Adjunction

### Schema

```yaml
# maps/adjunctions/repository.map.yaml

adjunction:
  name: "Free ⊣ Repository"
  description: "Persistence as adjunction"
  
  structure:
    left_adjoint:
      name: Free
      source: Storage
      target: Domain
      meaning: "Lift stored data to domain model"
      
    right_adjoint:
      name: Repository
      source: Domain
      target: Storage
      meaning: "Store domain model"
      
    unit:
      name: η
      type: "A → Repository(Free(A))"
      meaning: "Create and immediately retrieve"
      implementation: "save then load pattern"
      
    counit:
      name: ε
      type: "Free(Repository(A)) → A"
      meaning: "Load stored entity"
      implementation: "get by ID pattern"

  # CRUD as adjunction operations
  operations:
    create:
      categorical: "η component: A → Stored[A]"
      abstract:
        input: DomainEntity
        output: "IO[Either[CreateError, StoredEntity]]"
        semantics: "Apply unit, store in database"
        
    read:
      categorical: "ε component: Id → A"
      abstract:
        input: EntityId
        output: "IO[Either[NotFound, DomainEntity]]"
        semantics: "Apply counit, retrieve from database"
        
    update:
      categorical: "ε ; modify ; η"
      abstract:
        input: "(EntityId, Patch)"
        output: "IO[Either[UpdateError, DomainEntity]]"
        semantics: "Read, modify, write back"
        
    delete:
      categorical: "annihilate stored representation"
      abstract:
        input: EntityId
        output: "IO[Either[DeleteError, Unit]]"
        semantics: "Remove from storage"

  # Implementation targets
  targets:
    python:
      pattern: repository_class
      template: |
        class {Entity}Repository:
            def __init__(self, session: AsyncSession):
                self.session = session
                
            async def create(self, entity: {Entity}) -> Result[{Entity}, CreateError]:
                """Unit: Domain → Storage → Domain"""
                try:
                    db_entity = {Entity}Model.from_domain(entity)
                    self.session.add(db_entity)
                    await self.session.flush()
                    return Success(db_entity.to_domain())
                except IntegrityError as e:
                    return Failure(CreateError.from_exception(e))
                    
            async def get(self, id: {Entity}Id) -> Result[{Entity}, NotFound]:
                """Counit: Id → Storage → Domain"""
                query = select({Entity}Model).where({Entity}Model.id == id)
                result = await self.session.execute(query)
                row = result.scalar_one_or_none()
                if row is None:
                    return Failure(NotFound('{entity}', id))
                return Success(row.to_domain())
                
            async def update(
                self, 
                id: {Entity}Id, 
                patch: {Entity}Patch
            ) -> Result[{Entity}, UpdateError]:
                """Counit ; modify ; Unit"""
                existing = await self.get(id)
                if isinstance(existing, Failure):
                    return Failure(UpdateError.not_found(id))
                updated = existing.unwrap().apply_patch(patch)
                return await self.save(updated)
                
            async def delete(self, id: {Entity}Id) -> Result[None, DeleteError]:
                """Remove from storage"""
                query = delete({Entity}Model).where({Entity}Model.id == id)
                result = await self.session.execute(query)
                if result.rowcount == 0:
                    return Failure(DeleteError.not_found(id))
                return Success(None)
                
    typescript:
      pattern: repository_class
      template: |
        class {Entity}Repository {
          constructor(private readonly prisma: PrismaClient) {}
          
          async create(entity: {Entity}): Promise<Either<CreateError, {Entity}>> {
            try {
              const result = await this.prisma.{entity}.create({
                data: toPrisma(entity),
              });
              return right(fromPrisma(result));
            } catch (e) {
              return left(CreateError.from(e));
            }
          }
          
          async get(id: {Entity}Id): Promise<Either<NotFound, {Entity}>> {
            const result = await this.prisma.{entity}.findUnique({
              where: { id },
            });
            if (!result) {
              return left(new NotFound('{entity}', id));
            }
            return right(fromPrisma(result));
          }
          
          async update(
            id: {Entity}Id, 
            patch: {Entity}Patch
          ): Promise<Either<UpdateError, {Entity}>> {
            try {
              const result = await this.prisma.{entity}.update({
                where: { id },
                data: patch,
              });
              return right(fromPrisma(result));
            } catch (e) {
              return left(UpdateError.from(e));
            }
          }
          
          async delete(id: {Entity}Id): Promise<Either<DeleteError, void>> {
            try {
              await this.prisma.{entity}.delete({ where: { id } });
              return right(undefined);
            } catch (e) {
              return left(DeleteError.from(e));
            }
          }
        }

  # Model mapping (Free functor)
  model_mapping:
    description: "Free functor maps stored representation to domain"
    targets:
      python:
        pattern: |
          class {Entity}Model(Base):
              __tablename__ = '{entities}'
              
              id: Mapped[UUID] = mapped_column(primary_key=True)
              # ... fields
              
              @classmethod
              def from_domain(cls, entity: {Entity}) -> '{Entity}Model':
                  """Repository functor application"""
                  return cls(
                      id=entity.id,
                      # ... map fields
                  )
                  
              def to_domain(self) -> {Entity}:
                  """Free functor application"""
                  return {Entity}(
                      id={Entity}Id(self.id),
                      # ... map fields
                  )
```

## Cache Adjunction

### Schema

```yaml
# maps/adjunctions/cache.map.yaml

adjunction:
  name: "Forget ⊣ Cache"
  description: "Caching as adjunction"
  
  structure:
    left_adjoint:
      name: Forget
      source: CachedDomain
      target: Domain
      meaning: "Strip cache, return underlying value"
      
    right_adjoint:
      name: Cache
      source: Domain
      target: CachedDomain
      meaning: "Add cache layer"
      
    unit:
      name: η
      type: "A → Cache(Forget(A))"
      meaning: "Cache lookup - check if cached"
      implementation: "cache.get(key)"
      
    counit:
      name: ε
      type: "Forget(Cache(A)) → A"
      meaning: "Cache hit - extract value"
      implementation: "return cached.value"

  # Cache operations
  operations:
    get_or_compute:
      categorical: "η with fallback to compute"
      abstract:
        input: Key
        compute: "Key → IO[A]"
        output: "IO[A]"
        semantics: "Check cache, compute on miss, cache result"
        
    invalidate:
      categorical: "annihilate cached value"
      abstract:
        input: Key
        output: "IO[Unit]"
        semantics: "Remove from cache"
        
    warm:
      categorical: "pre-populate cache"
      abstract:
        input: "(Key, A)"
        output: "IO[Unit]"
        semantics: "Store in cache without computation"

  # Implementation targets
  targets:
    python:
      pattern: cached_repository
      template: |
        class Cached{Entity}Repository:
            def __init__(
                self, 
                repository: {Entity}Repository,
                cache: RedisCache,
            ):
                self.repository = repository
                self.cache = cache
                self.ttl = 300  # 5 minutes
                
            async def get(self, id: {Entity}Id) -> Result[{Entity}, NotFound]:
                """Unit application with fallback"""
                # Check cache (η)
                cache_key = f"{entity}:{id}"
                cached = await self.cache.get(cache_key)
                
                if cached is not None:
                    # Counit: extract from cache
                    return Success({Entity}.from_json(cached))
                    
                # Cache miss: compute from repository
                result = await self.repository.get(id)
                
                if isinstance(result, Success):
                    # Populate cache for next time
                    await self.cache.set(
                        cache_key, 
                        result.unwrap().to_json(),
                        ttl=self.ttl
                    )
                    
                return result
                
            async def invalidate(self, id: {Entity}Id) -> None:
                """Remove from cache on update/delete"""
                await self.cache.delete(f"{entity}:{id}")
                
            async def update(
                self,
                id: {Entity}Id,
                patch: {Entity}Patch
            ) -> Result[{Entity}, UpdateError]:
                """Update with cache invalidation"""
                result = await self.repository.update(id, patch)
                if isinstance(result, Success):
                    await self.invalidate(id)
                return result
                
    typescript:
      pattern: cached_repository
      template: |
        class Cached{Entity}Repository {
          constructor(
            private readonly repository: {Entity}Repository,
            private readonly cache: Redis,
            private readonly ttl = 300,
          ) {}
          
          async get(id: {Entity}Id): Promise<Either<NotFound, {Entity}>> {
            const cacheKey = `{entity}:${id}`;
            const cached = await this.cache.get(cacheKey);
            
            if (cached) {
              return right(JSON.parse(cached) as {Entity});
            }
            
            const result = await this.repository.get(id);
            
            if (isRight(result)) {
              await this.cache.set(cacheKey, JSON.stringify(result.right), 'EX', this.ttl);
            }
            
            return result;
          }
          
          async invalidate(id: {Entity}Id): Promise<void> {
            await this.cache.del(`{entity}:${id}`);
          }
        }
```

## External Adjunction

### Schema

```yaml
# maps/adjunctions/external.map.yaml

adjunction:
  name: "Domain ⊣ External"
  description: "External API integration as adjunction"
  
  structure:
    left_adjoint:
      name: ToDomain
      source: External
      target: Domain
      meaning: "Convert external response to domain model"
      
    right_adjoint:
      name: ToExternal
      source: Domain
      target: External
      meaning: "Convert domain request to external format"
      
    unit:
      name: η
      type: "DomainRequest → Domain(External(DomainRequest))"
      meaning: "Send request, convert response back to domain"
      
    counit:
      name: ε
      type: "External(Domain(ExternalResponse)) → ExternalResponse"
      meaning: "Pass through external response"

  # API client operations
  operations:
    call:
      categorical: "η application with effect"
      abstract:
        input: DomainRequest
        output: "IO[Either[ApiError, DomainResponse]]"
        semantics: "Convert to external, call API, convert response"

  # Implementation targets
  targets:
    python:
      pattern: api_client
      template: |
        class {External}Client:
            def __init__(self, http_client: httpx.AsyncClient, config: Config):
                self.http = http_client
                self.config = config
                
            async def {operation}(
                self, 
                request: {DomainRequest}
            ) -> Result[{DomainResponse}, {External}Error]:
                """Adjunction: Domain → External → Domain"""
                try:
                    # ToExternal functor
                    external_request = self._to_external(request)
                    
                    # Execute external call
                    response = await self.http.{method}(
                        self._build_url(external_request),
                        headers=self._headers(),
                        json=external_request.to_dict(),
                    )
                    response.raise_for_status()
                    
                    # ToDomain functor
                    return Success(self._to_domain(response.json()))
                    
                except httpx.HTTPStatusError as e:
                    return Failure({External}Error.from_response(e.response))
                except httpx.RequestError as e:
                    return Failure({External}Error.connection_error(e))
                    
            def _to_external(self, request: {DomainRequest}) -> ExternalRequest:
                """ToExternal functor application"""
                return ExternalRequest(...)
                
            def _to_domain(self, data: dict) -> {DomainResponse}:
                """ToDomain functor application"""
                return {DomainResponse}(...)
```

## Validation

### Completeness Checks

```yaml
completeness:
  - all_adjunctions_have_unit_counit
  - all_crud_operations_mapped
  - all_cache_operations_mapped
  - all_external_clients_mapped
```

### Consistency Checks

```yaml
consistency:
  - triangle_identities_implementable
  - functor_laws_preserved
  - error_types_consistent
```

## Next Skills

Output feeds into:
- `monad-mapper`
- `module-mapper`
