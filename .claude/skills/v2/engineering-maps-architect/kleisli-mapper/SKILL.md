---
name: kleisli-mapper
description: |
  Map Kleisli composition patterns to effect handling implementations. Produces effect
  type mappings, composition operators, and interpreter patterns. Handles IO, Either,
  and composed effects like IO[Either[E, A]].
  Input: services.spec.yaml, standards/categories/*.std.yaml, primitives maps
  Output: maps/kleisli/*.map.yaml
---

# Kleisli Mapper

Map effectful morphisms to composable implementations.

## Purpose

Transform Kleisli categories into effect handling patterns:
1. Map effect types to monadic representations
2. Define Kleisli composition operators
3. Create effect interpreters
4. Handle effect stacking (monad transformers)

## Input

- `specifications/v{X}/services.spec.yaml` - Morphisms with effects
- `standards/categories/*.std.yaml` - Category definitions
- `maps/primitives/*.map.yaml` - Type mappings

## Output

```
maps/kleisli/
├── effects.map.yaml       # Effect type mappings
└── interpreters.map.yaml  # Effect interpreters
```

## Effects Mapping

### Schema

```yaml
# maps/kleisli/effects.map.yaml

effects:
  # Effect type definitions
  effect_types:
    # IO effect (side effects)
    - name: IO
      categorical: "Kleisli[IO]"
      abstract:
        kind: effect
        represents: "side effects, async operations"
        laws:
          - "IO(a).flatMap(f) = f(a)"  # Left identity simplified
          - "io.flatMap(IO) = io"       # Right identity
          - "(io >>= f) >>= g = io >>= (x => f(x) >>= g)"  # Associativity
      targets:
        python:
          type: "Coroutine[Any, Any, {A}]"
          syntax: "async/await"
          wrapper: |
            async def {name}({params}) -> {A}:
                {body}
          composition: |
            result = await first()
            return await second(result)
            
        typescript:
          type: "Promise<{A}>"
          syntax: "async/await"
          wrapper: |
            async function {name}({params}): Promise<{A}> {
              {body}
            }
          composition: |
            const result = await first();
            return second(result);
            
        go:
          type: "{A}"
          syntax: "goroutines/channels"
          note: "Go uses explicit error returns, not monadic IO"
          
    # Either effect (errors)
    - name: Either
      categorical: "Kleisli[Either[E, _]]"
      abstract:
        kind: effect
        represents: "fallible computations"
        type_params: [E, A]
        constructors:
          - "Left: E → Either[E, A]"
          - "Right: A → Either[E, A]"
        laws:
          - "Right(a).flatMap(f) = f(a)"
          - "Left(e).flatMap(f) = Left(e)"
      targets:
        python:
          type: "Either[{E}, {A}]"
          import: "from returns.result import Result, Success, Failure"
          alternative: "Result[{A}, {E}]"
          left: "Failure({e})"
          right: "Success({a})"
          composition: |
            match result:
                case Success(value):
                    return f(value)
                case Failure(error):
                    return Failure(error)
                    
        typescript:
          type: "Either<{E}, {A}>"
          import: "import { Either, left, right } from 'fp-ts/Either'"
          left: "left({e})"
          right: "right({a})"
          composition: |
            import { pipe } from 'fp-ts/function';
            import { chain } from 'fp-ts/Either';
            pipe(result, chain(f))
            
        go:
          type: "({A}, error)"
          note: "Go uses tuple return (value, error)"
          composition: |
            result, err := first()
            if err != nil {
              return nil, err
            }
            return second(result)

    # Reader effect (dependency injection)
    - name: Reader
      categorical: "Kleisli[Reader[R, _]]"
      abstract:
        kind: effect
        represents: "dependency injection"
        type_params: [R, A]
        type_constructor: "R → A"
      targets:
        python:
          pattern: "function parameter"
          example: |
            def operation(deps: Dependencies) -> A:
                return deps.service.do_thing()
                
        typescript:
          pattern: "function parameter"
          example: |
            function operation(deps: Dependencies): A {
              return deps.service.doThing();
            }

  # Composed effects
  composed_effects:
    # IO[Either[E, A]] - the most common pattern
    - name: IOEither
      composition: "IO ∘ Either"
      abstract:
        kind: composed_effect
        outer: IO
        inner: Either
        type: "IO[Either[{E}, {A}]]"
        
      targets:
        python:
          type: "Coroutine[Any, Any, Result[{A}, {E}]]"
          pattern: |
            async def {name}({params}) -> Result[{A}, {E}]:
                try:
                    result = await operation()
                    return Success(result)
                except {E} as e:
                    return Failure(e)
                    
        typescript:
          type: "Promise<Either<{E}, {A}>>"
          import: "import { TaskEither } from 'fp-ts/TaskEither'"
          alternative: "TaskEither<{E}, {A}>"
          pattern: |
            async function {name}({params}): Promise<Either<{E}, {A}>> {
              try {
                const result = await operation();
                return right(result);
              } catch (e) {
                return left(e as {E});
              }
            }

  # Kleisli composition
  kleisli_composition:
    # Kleisli arrow: A → M[B]
    arrow:
      abstract: "f: A → M[B]"
      composition: "(g <=< f)(a) = f(a) >>= g"
      
    # Fish operator (Kleisli composition)
    fish:
      symbol: "<=<"
      type: "(B → M[C]) → (A → M[B]) → (A → M[C])"
      
    targets:
      python:
        # Using returns library
        pattern: |
          from returns.pipeline import flow
          from returns.pointfree import bind
          
          result = flow(
              input,
              first_operation,
              bind(second_operation),
              bind(third_operation),
          )
          
        # Direct async
        async_pattern: |
          async def composed(input: A) -> Result[C, E]:
              result1 = await first(input)
              if isinstance(result1, Failure):
                  return result1
              result2 = await second(result1.unwrap())
              if isinstance(result2, Failure):
                  return result2
              return await third(result2.unwrap())
              
      typescript:
        pattern: |
          import { pipe } from 'fp-ts/function';
          import { chain } from 'fp-ts/TaskEither';
          
          const composed = pipe(
            first(input),
            chain(second),
            chain(third),
          );
```

## Interpreters Mapping

### Schema

```yaml
# maps/kleisli/interpreters.map.yaml

interpreters:
  # Interpreter pattern
  pattern: |
    Kleisli morphisms are descriptions of computations.
    Interpreters execute these descriptions in a specific context.
    
  # IO interpreter
  io_interpreter:
    abstract:
      input: "IO[A]"
      output: "A (with side effects executed)"
      
    targets:
      python:
        pattern: "asyncio.run() or await"
        example: |
          import asyncio
          
          async def main():
              result = await io_operation()
              return result
              
          if __name__ == "__main__":
              asyncio.run(main())
              
      typescript:
        pattern: "Promise resolution"
        example: |
          async function main() {
            const result = await ioOperation();
            return result;
          }
          
          main().catch(console.error);

  # Either interpreter
  either_interpreter:
    abstract:
      input: "Either[E, A]"
      output: "A (or throw/handle E)"
      
    strategies:
      - name: throw_on_error
        description: "Convert Left to exception"
        
      - name: default_on_error
        description: "Provide default value for Left"
        
      - name: handle_error
        description: "Pattern match and handle"
        
    targets:
      python:
        throw_on_error: |
          result.unwrap()  # Raises on Failure
          
        default_on_error: |
          result.value_or(default)
          
        handle_error: |
          match result:
              case Success(value):
                  handle_success(value)
              case Failure(error):
                  handle_error(error)
                  
      typescript:
        throw_on_error: |
          import { getOrElseW } from 'fp-ts/Either';
          const value = pipe(result, getOrElseW((e) => { throw e; }));
          
        default_on_error: |
          import { getOrElse } from 'fp-ts/Either';
          const value = pipe(result, getOrElse(() => defaultValue));
          
        handle_error: |
          import { fold } from 'fp-ts/Either';
          pipe(result, fold(handleError, handleSuccess));

  # Composed effect interpreter
  io_either_interpreter:
    abstract:
      input: "IO[Either[E, A]]"
      output: "A (with effects, handling errors)"
      
    targets:
      python:
        pattern: |
          async def run_with_error_handling():
              result = await io_either_operation()
              match result:
                  case Success(value):
                      return value
                  case Failure(error):
                      logger.error(f"Operation failed: {error}")
                      raise ApplicationError(error)
                      
      typescript:
        pattern: |
          import { fold } from 'fp-ts/TaskEither';
          
          const program = pipe(
            ioEitherOperation(),
            fold(
              (error) => T.of(handleError(error)),
              (value) => T.of(handleSuccess(value)),
            ),
          );
          
          await program();

  # Service layer interpreter
  service_interpreter:
    description: |
      At service boundaries, interpret effects into 
      HTTP responses, database operations, etc.
      
    patterns:
      - name: http_handler
        description: "Interpret to HTTP response"
        abstract: |
          handler: Request → IO[Either[Error, Response]]
          interpreter: IO[Either[Error, Response]] → HttpResponse
          
      - name: repository
        description: "Interpret to database operations"
        abstract: |
          repository: Query → IO[Either[DbError, Result]]
          interpreter: IO[Either[DbError, Result]] → SQL execution
```

## Composition Patterns

```yaml
composition_patterns:
  # Sequential composition
  sequential:
    description: "Chain operations in sequence"
    pattern: "a >>= f >>= g >>= h"
    
  # Parallel composition
  parallel:
    description: "Run independent operations in parallel"
    abstract: "(IO[A], IO[B]) → IO[(A, B)]"
    targets:
      python:
        pattern: |
          async def parallel(*operations):
              return await asyncio.gather(*operations)
              
      typescript:
        pattern: |
          const [a, b] = await Promise.all([opA(), opB()]);

  # Error recovery
  recovery:
    description: "Handle errors and recover"
    abstract: "IO[Either[E, A]] → (E → IO[A]) → IO[A]"
    targets:
      python:
        pattern: |
          result = await operation()
          if isinstance(result, Failure):
              return await fallback(result.failure())
          return result.unwrap()
```

## Validation

### Completeness Checks

```yaml
completeness:
  - all_effect_types_mapped
  - all_morphisms_have_effect_handlers
  - composition_operators_defined
  - interpreters_for_all_effects
```

### Consistency Checks

```yaml
consistency:
  - kleisli_laws_implementable
  - composition_type_checks
  - interpreter_types_match
```

## Next Skills

Output feeds into:
- `monad-mapper`
- `module-mapper`
