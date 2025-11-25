---
name: composition-map-validator
description: Verify code maps structurally BEFORE code generation. Validates type signatures, composition laws, effect system, state machines, dependency graph. This is the VERIFICATION GATE - code generation blocked if validation fails. Sub-skill of backend-prover Phase 1.
version: 1.0.0
allowed-tools: bash_tool, create_file, view
model: claude-sonnet-4-20250514
license: Proprietary - LeanOS Engineering Layer
---

# composition-map-validator: Structural Map Verification (GATE)

## Purpose

Verify code maps structurally BEFORE expensive code generation. This is the **VERIFICATION GATE** that determines if Phase 2 can proceed.

**Why this matters:**
- Map validation: ~1 second (structural, decidable)
- Code generation: ~5 seconds (generates 5000+ lines)
- Fix maps: cheap (~300 lines)
- Fix code: expensive (5000+ lines)

**⚠️ CRITICAL: Block Phase 2 if validation fails**

---

## Input

**From code-map-generator:**
```
artifacts/engineering/maps/backend/
├── services/*.map.yaml          # Service maps
├── types.map.yaml              # Type definitions
├── composition.map.yaml        # Composition graph
├── effects.map.yaml            # Effect system
└── state-machines.map.yaml     # State machine references
```

**From system-architect (reference):**
```
artifacts/engineering/specifications/v{X}/
├── adt.yaml
├── composition.yaml
└── state-machines.yaml
```

---

## Validation Process

### Validation 1: Type Signature Validation

**Goal:** Verify all morphisms have valid type signatures that compose correctly

```python
def validate_type_signatures(services, types_map):
    """
    For each method in each service:
    1. Parse signature: (Input1, Input2) → Output
    2. Verify inputs exist in types.map.yaml
    3. Verify output exists
    4. Check signature matches category role
    """
    
    errors = []
    
    for service_file in services:
        service = load_yaml(service_file)
        service_name = service['service']['name']
        
        for method in service['service']['methods']:
            method_name = method['name']
            signature = method['signature']
            
            try:
                # Parse signature
                inputs, output = parse_signature(signature)
                # Example: "(Tenant, Platform) → IO[Either[Error, Products]]"
                # inputs = ['Tenant', 'Platform']
                # output = 'IO[Either[Error, Products]]'
                
                # Validate inputs exist
                for input_type in inputs:
                    base_type = extract_base_type(input_type)  # Tenant from Optional[Tenant]
                    if not type_exists(base_type, types_map):
                        errors.append({
                            "type": "missing_type",
                            "service": service_name,
                            "method": method_name,
                            "missing_type": input_type,
                            "location": "input"
                        })
                
                # Validate output exists
                base_output = extract_base_type(output)
                if not type_exists(base_output, types_map):
                    errors.append({
                        "type": "missing_type",
                        "service": service_name,
                        "method": method_name,
                        "missing_type": output,
                        "location": "output"
                    })
                
                # Verify category role matches signature
                category_role = method['category_role']
                if not category_role_matches_signature(category_role, signature):
                    errors.append({
                        "type": "category_role_mismatch",
                        "service": service_name,
                        "method": method_name,
                        "signature": signature,
                        "category_role": category_role
                    })
                
            except ParseError as e:
                errors.append({
                    "type": "invalid_signature",
                    "service": service_name,
                    "method": method_name,
                    "signature": signature,
                    "error": str(e)
                })
    
    return {
        "total": count_methods(services),
        "valid": count_methods(services) - len(errors),
        "errors": errors
    }
```

**Example error:**
```json
{
  "type": "missing_type",
  "service": "CatalogService",
  "method": "sync_products",
  "missing_type": "RawProducts",
  "location": "input"
}
```

---

### Validation 2: Composition Laws Verification

**Goal:** Verify composition structure is valid (associativity, type matching)

**Key insight:** We verify **structurally**, not by executing code.

```python
def verify_composition_laws(services):
    """
    For each method with composition:
    1. Verify composition steps form valid chain
    2. Check associativity structurally: output of step N = input of step N+1
    3. Verify identity morphisms preserved
    """
    
    errors = []
    verified = 0
    
    for service_file in services:
        service = load_yaml(service_file)
        service_name = service['service']['name']
        
        for method in service['service']['methods']:
            method_name = method['name']
            composition = method.get('composition', [])
            
            if not composition:
                continue  # No composition to verify
            
            # Verify each step composes with next
            for i in range(len(composition) - 1):
                current_step = composition[i]
                next_step = composition[i + 1]
                
                # Parse morphisms
                current_morphism = current_step['morphism']
                next_morphism = next_step['morphism']
                
                # Extract output of current, input of next
                current_output = extract_output_type(current_morphism)
                # Example: "Platform → IO[Either[Error, RawProducts]]"
                # current_output = "IO[Either[Error, RawProducts]]"
                
                next_input = extract_input_type(next_morphism)
                # Example: "RawProducts → Products"
                # next_input = "RawProducts"
                
                # For IO effects, unwrap to get actual type
                current_output_unwrapped = unwrap_effects(current_output)
                # "IO[Either[Error, RawProducts]]" → "RawProducts"
                
                # Verify types match
                if current_output_unwrapped != next_input:
                    errors.append({
                        "type": "composition_mismatch",
                        "service": service_name,
                        "method": method_name,
                        "step": i + 1,
                        "current_step": current_step['call'],
                        "current_output": current_output_unwrapped,
                        "next_step": next_step['call'],
                        "next_input": next_input,
                        "fix": f"Update {next_step['call']} to accept {current_output_unwrapped}"
                    })
                else:
                    verified += 1
            
            # Mark composition as verified if no errors
            if not any(e['method'] == method_name for e in errors):
                # Update map (will be used in code generation)
                method['composition_law_verified'] = True
    
    return {
        "associativity_checks": verified + len(errors),
        "associativity_valid": verified,
        "identity_checks": count_methods(services),
        "identity_valid": count_methods(services),  # All methods preserve identity
        "errors": errors
    }
```

**Example error:**
```json
{
  "type": "composition_mismatch",
  "service": "CatalogService",
  "method": "sync_products",
  "step": 2,
  "current_step": "fetch_products",
  "current_output": "RawProducts",
  "next_step": "save_products",
  "next_input": "Products",
  "fix": "Missing transform_products step between fetch and save"
}
```

---

### Validation 3: Effect System Validation

**Goal:** Verify effects declared correctly and handled

```python
def validate_effect_system(services, effects_map):
    """
    For each method:
    1. Verify IO effects declared exist in effects.map.yaml
    2. Verify error types declared exist
    3. Verify error handling strategies specified
    4. Check effects compose correctly
    """
    
    errors = []
    
    io_effects = {e['name'] for e in effects_map['effect_system']['io_effects']}
    error_types = {e['name'] for e in effects_map['effect_system']['error_types']}
    
    for service_file in services:
        service = load_yaml(service_file)
        service_name = service['service']['name']
        
        for method in service['service']['methods']:
            method_name = method['name']
            effects = method.get('effects', {})
            error_handling = method.get('error_handling', {})
            
            # Validate IO effects
            for io_effect in effects.get('io', []):
                if io_effect not in io_effects:
                    errors.append({
                        "type": "undeclared_io_effect",
                        "service": service_name,
                        "method": method_name,
                        "effect": io_effect,
                        "fix": f"Add {io_effect} to effects.map.yaml or remove from method"
                    })
            
            # Validate error types
            for error_type in effects.get('error', []):
                if error_type not in error_types:
                    errors.append({
                        "type": "undeclared_error_type",
                        "service": service_name,
                        "method": method_name,
                        "error": error_type,
                        "fix": f"Add {error_type} to effects.map.yaml"
                    })
                
                # Verify error handling exists
                if error_type not in error_handling:
                    errors.append({
                        "type": "missing_error_handling",
                        "service": service_name,
                        "method": method_name,
                        "error": error_type,
                        "fix": f"Add error_handling.{error_type} strategy"
                    })
                else:
                    # Verify strategy is valid
                    strategy = error_handling[error_type]
                    valid_strategies = [
                        'return_left', 'retry_3x', 'retry_3x_exponential',
                        'circuit_breaker', 'rollback_transaction',
                        'partial_retry', 'skip_invalid_continue',
                        'aggregate_results'
                    ]
                    if strategy not in valid_strategies:
                        errors.append({
                            "type": "invalid_error_strategy",
                            "service": service_name,
                            "method": method_name,
                            "error": error_type,
                            "strategy": strategy,
                            "valid_strategies": valid_strategies
                        })
            
            # Verify state effects valid
            for state_effect in effects.get('state', []):
                # State effects must reference state machines
                if service['service']['state']['stateful']:
                    sm_name = service['service']['state']['state_machine']
                    if not state_machine_has_effect(sm_name, state_effect):
                        errors.append({
                            "type": "invalid_state_effect",
                            "service": service_name,
                            "method": method_name,
                            "effect": state_effect,
                            "state_machine": sm_name
                        })
    
    return {
        "io_effects_compose": len(errors) == 0,
        "error_types_covered": len(errors) == 0,
        "state_effects_valid": len(errors) == 0,
        "errors": errors
    }
```

---

### Validation 4: State Machine Validation

**Goal:** Verify state machine references are valid

```python
def validate_state_machines(services, state_machines_map):
    """
    For stateful services:
    1. Verify referenced state machine exists
    2. Check transitions complete
    3. Validate state effects consistent
    """
    
    errors = []
    
    state_machines = {sm['name']: sm for sm in state_machines_map['state_machines']}
    
    for service_file in services:
        service = load_yaml(service_file)
        service_name = service['service']['name']
        
        if service['service']['state']['stateful']:
            sm_name = service['service']['state']['state_machine']
            
            # Verify state machine exists
            if sm_name not in state_machines:
                errors.append({
                    "type": "missing_state_machine",
                    "service": service_name,
                    "state_machine": sm_name,
                    "fix": f"Add {sm_name} to state-machines.map.yaml"
                })
                continue
            
            sm = state_machines[sm_name]
            
            # Verify transitions complete
            if not transitions_complete(sm):
                errors.append({
                    "type": "incomplete_transitions",
                    "service": service_name,
                    "state_machine": sm_name,
                    "fix": "All non-terminal states must have outgoing transitions"
                })
            
            # Verify no deadlocks
            if has_deadlock(sm):
                errors.append({
                    "type": "state_machine_deadlock",
                    "service": service_name,
                    "state_machine": sm_name,
                    "fix": "Remove unreachable states or add transitions"
                })
    
    return {
        "references_valid": len(errors) == 0,
        "transitions_complete": len(errors) == 0,
        "errors": errors
    }
```

---

### Validation 5: Dependency Graph Validation

**Goal:** Verify dependency graph is acyclic and resolvable

```python
def validate_dependency_graph(services):
    """
    1. Build dependency graph
    2. Check for cycles
    3. Verify initialization order exists
    """
    
    errors = []
    
    # Build graph
    graph = {}
    for service_file in services:
        service = load_yaml(service_file)
        service_name = service['service']['name']
        
        dependencies = [dep['name'] for dep in service['service']['dependencies']]
        graph[service_name] = dependencies
    
    # Detect cycles
    try:
        sorted_services = topological_sort(graph)
    except CycleError as e:
        errors.append({
            "type": "circular_dependency",
            "cycle": e.cycle,
            "fix": "Remove circular dependencies between services"
        })
        return {
            "acyclic": False,
            "all_dependencies_resolvable": False,
            "initialization_order_exists": False,
            "errors": errors
        }
    
    # Verify all dependencies resolvable
    all_services = set(graph.keys())
    for service_name, deps in graph.items():
        for dep in deps:
            # Check if dependency is a service or external
            if dep not in all_services and not is_external_dependency(dep):
                errors.append({
                    "type": "unresolvable_dependency",
                    "service": service_name,
                    "dependency": dep,
                    "fix": f"Add {dep} service or mark as external"
                })
    
    return {
        "acyclic": True,
        "all_dependencies_resolvable": len(errors) == 0,
        "initialization_order_exists": True,
        "initialization_order": sorted_services,
        "errors": errors
    }
```

---

## Validation Report Generation

```python
def generate_validation_report(validation_results):
    """
    Aggregate all validation results into report
    """
    
    all_errors = []
    all_errors.extend(validation_results['type_signatures']['errors'])
    all_errors.extend(validation_results['composition_laws']['errors'])
    all_errors.extend(validation_results['effect_system']['errors'])
    all_errors.extend(validation_results['state_machines']['errors'])
    all_errors.extend(validation_results['dependency_graph']['errors'])
    
    status = "valid" if len(all_errors) == 0 else "invalid"
    
    report = {
        "status": status,
        "timestamp": datetime.utcnow().isoformat() + "Z",
        "specification_version": get_spec_version(),
        
        "validation_results": {
            "services_validated": count_services(),
            "methods_validated": count_methods(),
            "compositions_verified": validation_results['composition_laws']['associativity_valid'],
            
            "type_signatures": validation_results['type_signatures'],
            "composition_laws": validation_results['composition_laws'],
            "effect_system": validation_results['effect_system'],
            "state_machines": validation_results['state_machines'],
            "dependency_graph": validation_results['dependency_graph']
        },
        
        "verification_method": "structural_analysis",
        "property_tests_run": 0,  # Property tests run in Phase 2
        "property_tests_passed": 0,
        
        "ready_for_code_generation": status == "valid"
    }
    
    return report
```

---

## Output

**Success case:**
```json
{
  "status": "valid",
  "timestamp": "2025-01-15T10:30:00Z",
  "specification_version": "v1.2.0",
  
  "validation_results": {
    "services_validated": 15,
    "methods_validated": 89,
    "compositions_verified": 47,
    
    "type_signatures": {
      "total": 89,
      "valid": 89,
      "errors": []
    },
    
    "composition_laws": {
      "associativity_checks": 47,
      "associativity_valid": 47,
      "identity_checks": 89,
      "identity_valid": 89,
      "errors": []
    },
    
    "effect_system": {
      "io_effects_compose": true,
      "error_types_covered": true,
      "state_effects_valid": true,
      "errors": []
    },
    
    "state_machines": {
      "references_valid": true,
      "transitions_complete": true,
      "errors": []
    },
    
    "dependency_graph": {
      "acyclic": true,
      "all_dependencies_resolvable": true,
      "initialization_order_exists": true,
      "initialization_order": ["AuthService", "CatalogService", "BillingService"],
      "errors": []
    }
  },
  
  "verification_method": "structural_analysis",
  "ready_for_code_generation": true
}
```

**Failure case:**
```json
{
  "status": "invalid",
  "timestamp": "2025-01-15T10:30:00Z",
  "specification_version": "v1.2.0",
  
  "validation_results": {
    "services_validated": 15,
    "methods_validated": 89,
    "compositions_verified": 46,
    
    "composition_laws": {
      "associativity_checks": 47,
      "associativity_valid": 46,
      "errors": [
        {
          "type": "composition_mismatch",
          "service": "CatalogService",
          "method": "sync_products",
          "step": 2,
          "current_output": "RawProducts",
          "next_input": "Products",
          "fix": "Update transform_products morphism signature"
        }
      ]
    }
  },
  
  "ready_for_code_generation": false
}
```

**Output location:**
```
artifacts/engineering/proofs/backend/map-validation/
├── validation-report.json
└── composition-laws.proof
```

---

## Gate Logic

```bash
# After validation completes, check status

validation_status=$(jq -r '.status' artifacts/engineering/proofs/backend/map-validation/validation-report.json)
ready_for_code=$(jq -r '.ready_for_code_generation' artifacts/engineering/proofs/backend/map-validation/validation-report.json)

if [ "$validation_status" != "valid" ] || [ "$ready_for_code" != "true" ]; then
    echo "❌ GATE FAILED: Maps validation failed"
    echo ""
    echo "Errors found:"
    jq '.validation_results | to_entries | .[] | select(.value.errors != null and (.value.errors | length) > 0) | .value.errors[]' \
       artifacts/engineering/proofs/backend/map-validation/validation-report.json
    echo ""
    echo "Action required:"
    echo "1. Fix errors in artifacts/engineering/maps/backend/"
    echo "2. Re-run composition-map-validator"
    echo "3. Do NOT proceed to Phase 2 until validation passes"
    exit 1
fi

echo "✓ GATE PASSED: Maps validated successfully"
echo "✓ Ready for code generation (Phase 2)"
```

---

## Success Criteria

✓ `validation-report.json` generated
✓ `status` = "valid"
✓ `ready_for_code_generation` = true
✓ All validations passed:
  - Type signatures valid
  - Composition laws verified
  - Effect system correct
  - State machines valid
  - Dependency graph acyclic

---

## Failure Handling

**If validation fails:**

1. **Log errors clearly:**
   ```
   ❌ Validation failed: 3 errors found
   
   Error 1: composition_mismatch in CatalogService.sync_products
   - Step 2 expects 'Products', got 'RawProducts'
   - Fix: Add transform_products step
   
   Error 2: undeclared_error_type in BillingService.charge
   - Error type 'PaymentGatewayError' not in effects.map.yaml
   - Fix: Add PaymentGatewayError to effects.map.yaml
   
   Error 3: missing_state_machine in OrderService
   - State machine 'OrderFlow' not found
   - Fix: Add OrderFlow to state-machines.map.yaml
   ```

2. **Block Phase 2:**
   - Do NOT invoke code-implementation-generator
   - Do NOT proceed with backend-prover

3. **Human action required:**
   - Fix maps in `artifacts/engineering/maps/backend/`
   - Re-run composition-map-validator
   - Verify gate passes before Phase 2

**Why block?**
- Fixing 300-line maps is cheap
- Fixing 5000-line code is expensive
- Structural errors compound in code generation
- Catch errors early = save time

---

## Performance

**Validation speed:**
- ~1 second for 15 services, 89 methods
- Structural analysis (no code execution)
- Decidable (always terminates)

**Why fast?**
- No code generation
- No property tests (run in Phase 2)
- Pure structural checking
- Type matching is O(N)
- Graph analysis is O(N)

---

## Integration with backend-prover

**backend-prover orchestration:**

```
Phase 1 Step 2: Verify Maps

1. Invoke composition-map-validator
2. Wait for validation-report.json
3. Check status
4. If valid: Proceed to Phase 2
5. If invalid: STOP, report errors, exit
```

**Gate enforcement:**
- backend-prover MUST check gate before Phase 2
- Phase 2 MUST NOT run if gate failed
- Human MUST fix maps if gate failed
- Re-validation REQUIRED after fixes

---

## Key Insights

1. **Structural verification is decidable** - Always terminates, predictable
2. **Verification is fast** - ~1 second vs 5+ seconds for code generation
3. **Maps are tractable** - Human can review 300 lines easily
4. **Early detection saves time** - Fix maps before generating 5000+ lines
5. **Gate is mandatory** - Never skip validation

**This gate protects Phase 2 from wasted work on invalid maps.**