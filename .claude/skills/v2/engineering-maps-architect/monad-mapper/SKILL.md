---
name: monad-mapper
description: |
  Map monads to effect handler implementations. Produces IO monad (async), Either monad
  (error handling), Reader monad (dependency injection), Transaction monad patterns.
  Monads become effect wrappers with bind/flatMap operations.
  Input: standards/transactions/*.std.yaml, kleisli maps, adjunction maps
  Output: maps/monads/*.map.yaml
---

# Monad Mapper

Map monads to effect handling implementations.

## Purpose

Transform monads into composable effect handlers:
1. IO monad (async/await, side effects)
2. Either monad (error handling)
3. Reader monad (dependency injection)
4. Transaction monad (database transactions)
5. Composed monads (monad transformers)

## Input

- `standards/transactions/*.std.yaml` - Transaction monad
- `standards/configuration/*.std.yaml` - Reader monad
- `maps/kleisli/*.map.yaml` - Effect patterns
- `maps/adjunctions/*.map.yaml` - Adjunction patterns

## Output

```
maps/monads/
├── io.map.yaml          # IO monad
├── either.map.yaml      # Error handling
├── reader.map.yaml      # Dependency injection
└── transaction.map.yaml # Database transactions
```

## Monad Structure

### Abstract Pattern

```yaml
monad_pattern:
  structure:
    type_constructor: "M: Type → Type"
    pure: "A → M[A]"
    bind: "M[A] → (A → M[B]) → M[B]"
    
  laws:
    left_identity: "pure(a) >>= f ≡ f(a)"
    right_identity: "m >>= pure ≡ m"
    associativity: "(m >>= f) >>= g ≡ m >>= (x → f(x) >>= g)"
    
  derived:
    map: "M[A] → (A → B) → M[B]"
    flatten: "M[M[A]] → M[A]"
    ap: "M[A → B] → M[A] → M[B]"
```

## IO Monad

### Schema

```yaml
# maps/monads/io.map.yaml

monad:
  name: IO
  description: "Side effects as values"
  
  abstract:
    type_constructor: "IO[A]"
    semantics: "Description of computation with side effects"
    pure: "Wrap pure value in IO"
    bind: "Sequence IO operations"
    
  targets:
    python:
      representation: "Coroutine[Any, Any, A]"
      syntax: "async/await"
      
      pure:
        pattern: |
          async def pure(value: A) -> A:
              """Lift pure value into IO."""
              return value
              
      bind:
        pattern: |
          async def bind(
              ma: Coroutine[Any, Any, A],
              f: Callable[[A], Coroutine[Any, Any, B]]
          ) -> B:
              """Sequence IO operations."""
              a = await ma
              return await f(a)
              
        usage: |
          # Direct syntax
          result = await first_io()
          final = await second_io(result)
          
          # Or with helper
          final = await bind(first_io(), second_io)
          
      composition:
        pattern: |
          async def compose_io(*operations):
              """Compose multiple IO operations."""
              result = None
              for op in operations:
                  if callable(op):
                      result = await op(result) if result else await op()
                  else:
                      result = await op
              return result
              
      parallel:
        pattern: |
          async def parallel_io(*operations) -> tuple:
              """Run IO operations in parallel."""
              return await asyncio.gather(*operations)
              
    typescript:
      representation: "Promise<A>"
      syntax: "async/await"
      
      pure:
        pattern: |
          function pure<A>(value: A): Promise<A> {
            return Promise.resolve(value);
          }
          
      bind:
        pattern: |
          async function bind<A, B>(
            ma: Promise<A>,
            f: (a: A) => Promise<B>
          ): Promise<B> {
            const a = await ma;
            return f(a);
          }
          
      alternative:
        library: "fp-ts/Task"
        import: "import { Task, chain } from 'fp-ts/Task'"
        usage: |
          pipe(
            firstTask,
            chain(secondTask),
            chain(thirdTask),
          )
```

## Either Monad

### Schema

```yaml
# maps/monads/either.map.yaml

monad:
  name: Either
  description: "Computations that may fail"
  
  abstract:
    type_constructor: "Either[E, A]"
    constructors:
      left: "E → Either[E, A]"
      right: "A → Either[E, A]"
    semantics: "Right for success, Left for failure"
    
  targets:
    python:
      representation: "Result[A, E]"
      library: "returns"
      import: "from returns.result import Result, Success, Failure"
      
      constructors:
        right: "Success(value)"
        left: "Failure(error)"
        
      pure:
        pattern: |
          def pure(value: A) -> Result[A, E]:
              return Success(value)
              
      bind:
        pattern: |
          def bind(
              ma: Result[A, E],
              f: Callable[[A], Result[B, E]]
          ) -> Result[B, E]:
              match ma:
                  case Success(value):
                      return f(value)
                  case Failure(error):
                      return Failure(error)
                      
        usage: |
          result = (
              first_operation()
              .bind(second_operation)
              .bind(third_operation)
          )
          
          # Or with pattern matching
          match result:
              case Success(value):
                  handle_success(value)
              case Failure(error):
                  handle_error(error)
                  
      utilities:
        map: |
          result.map(lambda x: x + 1)
          
        map_error: |
          result.alt(lambda e: DifferentError(e))
          
        unwrap: |
          result.unwrap()  # Raises on Failure
          
        value_or: |
          result.value_or(default)
          
    typescript:
      representation: "Either<E, A>"
      library: "fp-ts"
      import: "import { Either, left, right, chain, map } from 'fp-ts/Either'"
      
      constructors:
        right: "right(value)"
        left: "left(error)"
        
      bind:
        pattern: |
          import { pipe } from 'fp-ts/function';
          import { chain } from 'fp-ts/Either';
          
          pipe(
            firstOperation(),
            chain(secondOperation),
            chain(thirdOperation),
          )
          
      fold:
        pattern: |
          import { fold } from 'fp-ts/Either';
          
          pipe(
            result,
            fold(
              (error) => handleError(error),
              (value) => handleSuccess(value),
            ),
          )
```

## Reader Monad

### Schema

```yaml
# maps/monads/reader.map.yaml

monad:
  name: Reader
  description: "Dependency injection as monad"
  
  abstract:
    type_constructor: "Reader[R, A] = R → A"
    semantics: "Computation requiring environment R"
    pure: "Ignore environment, return value"
    bind: "Thread environment through"
    ask: "Get the environment itself"
    
  targets:
    python:
      # Pattern 1: Explicit parameter threading
      explicit:
        description: "Pass dependencies as parameters"
        pattern: |
          @dataclass
          class Dependencies:
              db: Database
              cache: Cache
              http: HttpClient
              config: Config
              
          async def operation(deps: Dependencies) -> Result[A, E]:
              # Use deps.db, deps.cache, etc.
              pass
              
          async def composed(deps: Dependencies) -> Result[B, E]:
              result_a = await operation_a(deps)
              if isinstance(result_a, Failure):
                  return result_a
              return await operation_b(deps, result_a.unwrap())
              
      # Pattern 2: FastAPI Depends
      fastapi:
        description: "Use FastAPI dependency injection"
        pattern: |
          def get_database() -> Database:
              return Database(settings.database_url)
              
          def get_service(
              db: Database = Depends(get_database),
              cache: Cache = Depends(get_cache),
          ) -> MyService:
              return MyService(db, cache)
              
          @router.get("/items/{id}")
          async def get_item(
              id: ItemId,
              service: MyService = Depends(get_service),
          ):
              return await service.get(id)
              
      # Pattern 3: Context variables
      context_vars:
        description: "Use contextvars for implicit threading"
        pattern: |
          from contextvars import ContextVar
          
          current_deps: ContextVar[Dependencies] = ContextVar('deps')
          
          @asynccontextmanager
          async def with_dependencies(deps: Dependencies):
              token = current_deps.set(deps)
              try:
                  yield
              finally:
                  current_deps.reset(token)
                  
          def get_deps() -> Dependencies:
              return current_deps.get()
              
          async def operation() -> Result[A, E]:
              deps = get_deps()
              # Use deps
              
    typescript:
      # Pattern 1: Explicit parameter
      explicit:
        pattern: |
          interface Dependencies {
            db: Database;
            cache: Cache;
            http: HttpClient;
          }
          
          function operation(deps: Dependencies): Promise<A> {
            return deps.db.query(...);
          }
          
      # Pattern 2: fp-ts Reader
      fp_ts:
        import: "import { Reader, ask, chain } from 'fp-ts/Reader'"
        pattern: |
          const getUser: Reader<Dependencies, Promise<User>> = 
            pipe(
              ask<Dependencies>(),
              map((deps) => deps.db.getUser(id)),
            );
```

## Transaction Monad

### Schema

```yaml
# maps/monads/transaction.map.yaml

monad:
  name: Transaction
  description: "Database transactions as monad"
  
  abstract:
    type_constructor: "Transaction[A] = Connection → IO[Either[TxError, A]]"
    semantics: "Computation within transaction context"
    pure: "Wrap value in transaction"
    bind: "Sequence operations in same transaction"
    
    operations:
      begin: "Start transaction"
      commit: "Persist changes"
      rollback: "Discard changes"
      
  targets:
    python:
      # SQLAlchemy async pattern
      sqlalchemy:
        pattern: |
          from sqlalchemy.ext.asyncio import AsyncSession
          from contextlib import asynccontextmanager
          
          @asynccontextmanager
          async def transaction(session: AsyncSession):
              """
              Transaction monad implementation.
              
              Pure: session contains the value
              Bind: operations share session
              """
              try:
                  yield session
                  await session.commit()
              except Exception:
                  await session.rollback()
                  raise
                  
          async def transactional_operation(
              session: AsyncSession
          ) -> Result[A, E]:
              """Operation within transaction context."""
              async with transaction(session):
                  # All operations here share the transaction
                  result1 = await repo1.create(session, entity1)
                  result2 = await repo2.create(session, entity2)
                  return Success((result1, result2))
                  
      # Unit of Work pattern
      unit_of_work:
        pattern: |
          class UnitOfWork:
              """Transaction monad as unit of work."""
              
              def __init__(self, session_factory):
                  self.session_factory = session_factory
                  
              @asynccontextmanager
              async def __call__(self):
                  session = self.session_factory()
                  try:
                      yield session
                      await session.commit()
                  except Exception:
                      await session.rollback()
                      raise
                  finally:
                      await session.close()
                      
          # Usage
          async with uow() as session:
              # Monadic bind - operations share transaction
              await merchant_repo.create(session, merchant)
              await profile_repo.create(session, profile)
              
    typescript:
      prisma:
        pattern: |
          async function withTransaction<A>(
            prisma: PrismaClient,
            operation: (tx: Prisma.TransactionClient) => Promise<A>
          ): Promise<A> {
            return prisma.$transaction(operation);
          }
          
          // Usage
          const result = await withTransaction(prisma, async (tx) => {
            const merchant = await tx.merchant.create({ data: merchantData });
            const profile = await tx.profile.create({ data: profileData });
            return { merchant, profile };
          });

  # Composed: Transaction[Either[E, A]]
  composed:
    abstract: "Transaction with error handling"
    targets:
      python:
        pattern: |
          async def transactional(
              session: AsyncSession,
              operation: Callable[..., Result[A, E]]
          ) -> Result[A, E]:
              """Transaction monad composed with Either."""
              try:
                  async with transaction(session):
                      return await operation()
              except Exception as e:
                  return Failure(TransactionError.from_exception(e))
```

## Monad Transformers

### Schema

```yaml
monad_transformers:
  description: "Stack multiple effects"
  
  # IO[Either[E, A]] - most common
  io_either:
    abstract: "Async operation that may fail"
    targets:
      python:
        type: "Coroutine[Any, Any, Result[A, E]]"
        pattern: |
          async def operation() -> Result[A, E]:
              try:
                  result = await async_call()
                  return Success(result)
              except SomeError as e:
                  return Failure(e)
                  
      typescript:
        type: "TaskEither<E, A>"
        import: "import { TaskEither, tryCatch } from 'fp-ts/TaskEither'"
        pattern: |
          const operation: TaskEither<Error, A> = tryCatch(
            () => asyncCall(),
            (e) => e as Error,
          );

  # Reader[R, IO[Either[E, A]]] - full stack
  reader_io_either:
    abstract: "Async operation with dependencies that may fail"
    targets:
      python:
        pattern: |
          async def operation(deps: Dependencies) -> Result[A, E]:
              result = await deps.service.call()
              return result
              
          # Compose multiple
          async def composed(deps: Dependencies) -> Result[B, E]:
              result_a = await operation_a(deps)
              if isinstance(result_a, Failure):
                  return result_a
              return await operation_b(deps, result_a.unwrap())
```

## Validation

### Completeness Checks

```yaml
completeness:
  - all_monads_have_pure_bind
  - all_effects_have_monad_mapping
  - transformers_compose_correctly
```

### Consistency Checks

```yaml
consistency:
  - monad_laws_implementable
  - bind_type_checks
  - composition_associative
```

## Next Skills

Output feeds into:
- `module-mapper`
- `maps-validator`
