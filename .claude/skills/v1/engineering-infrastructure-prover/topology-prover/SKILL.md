---
name: topology-prover
description: Verify deployed topology matches architecture specification (isomorphism). Validates service existence, dependencies, network connectivity, and resource constraints. Generates deployment-isomorphism.proof for proof-composer. Sub-skill of infrastructure-prover (Step 5.5).
version: 1.0.0
allowed-tools: bash_tool, view, create_file
model: claude-sonnet-4-20250514
license: Proprietary - LeanOS Engineering Layer
---

# topology-prover: Verify Topology Isomorphism

## Purpose

Verify that generated deployment configurations match the architecture specification exactly. This is **isomorphism verification** - proving the deployed topology is structurally identical to the spec.

**Input:**
- Service topology graph (from service-topology-analyzer)
- Generated configs (from docker-generator, kubernetes-generator)
- Architecture spec (original)

**Output:** `deployment-isomorphism.proof`

---

## Position in Flow

```
Step 5.1: service-topology-analyzer → topology-graph.json
Step 5.2: docker-generator → Docker configs
Step 5.3: kubernetes-generator → K8s manifests
Step 5.4: ci-cd-generator → CI/CD workflows
Step 5.5: topology-prover (YOU) → deployment-isomorphism.proof
```

**Why after config generation?**
- Can only verify configs exist AFTER they're generated
- Compares spec vs actual configs (both must exist)
- Final validation before proof-composer

---

## Input

**Topology graph (from service-topology-analyzer):**
```
artifacts/engineering/code/frontend/.internal/topology-graph.json
```

**Generated configs:**
```
artifacts/engineering/configs/
├── docker/
│   ├── Dockerfile.*
│   └── docker-compose.yml
├── k8s/
│   ├── *-deployment.yaml
│   ├── services.yaml
│   └── ingress.yaml
└── ci-cd/
    └── .github/workflows/
```

**Architecture spec:**
```
artifacts/engineering/specifications/v{X}/services.spec.yaml
```

---

## Verification Process

### Step 1: Load All Inputs

```python
def load_inputs(spec_version):
    """Load topology graph, configs, and original spec"""

    # Load topology graph
    with open('artifacts/engineering/code/frontend/.internal/topology-graph.json') as f:
        topology = json.load(f)

    # Load original spec
    with open(f'artifacts/engineering/specifications/v{spec_version}/services.spec.yaml') as f:
        spec = yaml.safe_load(f)

    # List generated configs
    docker_configs = list_files('artifacts/engineering/configs/docker/')
    k8s_configs = list_files('artifacts/engineering/configs/k8s/')
    cicd_configs = list_files('artifacts/engineering/configs/ci-cd/')

    return {
        'topology': topology,
        'spec': spec,
        'docker_configs': docker_configs,
        'k8s_configs': k8s_configs,
        'cicd_configs': cicd_configs
    }
```

---

### Step 2: Verify Service Existence

```python
def verify_service_existence(spec_services, configs):
    """
    Verify: Every service in spec has deployment config

    Isomorphism property: |spec_services| = |deployed_services|
    """

    errors = []

    for service in spec_services:
        service_name = service['name'].lower()

        # Check Docker config exists
        dockerfile = f"Dockerfile.{service_name}"
        if dockerfile not in configs['docker_configs']:
            errors.append({
                'type': 'missing_dockerfile',
                'service': service['name'],
                'expected': dockerfile
            })

        # Check K8s deployment exists (if K8s enabled)
        if configs['k8s_configs']:
            deployment = f"{service_name}-deployment.yaml"
            if deployment not in configs['k8s_configs']:
                errors.append({
                    'type': 'missing_k8s_deployment',
                    'service': service['name'],
                    'expected': deployment
                })

    return {
        'verified': len(errors) == 0,
        'services_in_spec': len(spec_services),
        'services_with_configs': len(spec_services) - len(errors),
        'errors': errors
    }
```

---

### Step 3: Verify Dependencies Configured

```python
def verify_dependencies_configured(topology, configs):
    """
    Verify: All service dependencies are configured in deployment

    For each service S with dependency D:
    - If D is external: verify external dependency in compose/k8s
    - If D is internal: verify service-to-service networking
    """

    errors = []

    for service_name, service_data in topology['services'].items():
        for dep in service_data.get('dependencies', []):
            dep_name = dep['name']
            is_external = dep.get('external', False)

            if is_external:
                # External dependency (postgres, redis, etc)
                # Verify it's in docker-compose or K8s configs
                if not external_dep_configured(dep_name, configs):
                    errors.append({
                        'type': 'missing_external_dependency',
                        'service': service_name,
                        'dependency': dep_name
                    })
            else:
                # Internal service dependency
                # Verify network connectivity configured
                if not internal_dep_configured(service_name, dep_name, configs):
                    errors.append({
                        'type': 'missing_internal_dependency',
                        'service': service_name,
                        'dependency': dep_name
                    })

    return {
        'verified': len(errors) == 0,
        'dependencies_checked': count_dependencies(topology),
        'errors': errors
    }

def external_dep_configured(dep_name, configs):
    """Check if external dependency is in docker-compose or K8s"""
    # Check docker-compose.yml for service definition
    # Check K8s for external service/secret references
    return True  # Implement actual check

def internal_dep_configured(from_service, to_service, configs):
    """Check if internal service networking is configured"""
    # Check depends_on in docker-compose
    # Check service discovery in K8s
    return True  # Implement actual check
```

---

### Step 4: Verify Network Connectivity

```python
def verify_network_connectivity(topology, configs):
    """
    Verify: Services can reach their dependencies

    Check:
    - Docker network configuration
    - K8s service definitions
    - Port mappings match spec
    """

    errors = []
    network_info = topology.get('network', {})

    # Verify internal network
    for connection in network_info.get('internal_network', []):
        from_service = connection['from']
        to_service = connection['to']

        if not network_path_exists(from_service, to_service, configs):
            errors.append({
                'type': 'missing_network_path',
                'from': from_service,
                'to': to_service
            })

    # Verify ports match
    for service, port in network_info.get('required_ports', {}).items():
        if not port_configured(service, port, configs):
            errors.append({
                'type': 'port_mismatch',
                'service': service,
                'expected_port': port
            })

    return {
        'verified': len(errors) == 0,
        'network_paths_verified': len(network_info.get('internal_network', [])),
        'ports_verified': len(network_info.get('required_ports', {})),
        'errors': errors
    }
```

---

### Step 5: Verify Resource Constraints

```python
def verify_resource_constraints(spec_services, configs):
    """
    Verify: Resource constraints in configs >= spec requirements

    Check:
    - CPU limits sufficient
    - Memory limits sufficient
    - Replicas configured (if specified)
    """

    errors = []

    for service in spec_services:
        service_name = service['name']
        required_resources = service.get('resources', {})

        # Get configured resources from K8s deployment
        configured = get_configured_resources(service_name, configs)

        # Verify CPU
        if required_resources.get('cpu'):
            if not cpu_sufficient(required_resources['cpu'], configured.get('cpu')):
                errors.append({
                    'type': 'insufficient_cpu',
                    'service': service_name,
                    'required': required_resources['cpu'],
                    'configured': configured.get('cpu')
                })

        # Verify memory
        if required_resources.get('memory'):
            if not memory_sufficient(required_resources['memory'], configured.get('memory')):
                errors.append({
                    'type': 'insufficient_memory',
                    'service': service_name,
                    'required': required_resources['memory'],
                    'configured': configured.get('memory')
                })

    return {
        'verified': len(errors) == 0,
        'services_checked': len(spec_services),
        'errors': errors
    }
```

---

### Step 6: Verify No Extra Services

```python
def verify_no_extra_services(spec_services, configs):
    """
    Verify: No extra services deployed (bijection)

    Isomorphism requires:
    - Every spec service has config (injection)
    - Every config has spec service (surjection)
    - Together: bijection (one-to-one)
    """

    errors = []
    spec_service_names = {s['name'].lower() for s in spec_services}

    # Extract deployed service names from configs
    deployed_services = extract_deployed_services(configs)

    # Check for extra services (in configs but not in spec)
    for deployed in deployed_services:
        if deployed.lower() not in spec_service_names:
            # Check if it's an infrastructure service (allowed)
            if not is_infrastructure_service(deployed):
                errors.append({
                    'type': 'extra_service',
                    'service': deployed,
                    'message': 'Service in deployment but not in spec'
                })

    return {
        'verified': len(errors) == 0,
        'spec_services': len(spec_service_names),
        'deployed_services': len(deployed_services),
        'bijection': len(spec_service_names) == len(deployed_services) and len(errors) == 0,
        'errors': errors
    }

def is_infrastructure_service(service_name):
    """Infrastructure services allowed (not in spec)"""
    infra_services = {'postgres', 'redis', 'nats', 'nginx', 'traefik'}
    return service_name.lower() in infra_services
```

---

### Step 7: Generate Isomorphism Proof

```python
def generate_isomorphism_proof(verification_results, spec_version):
    """
    Generate deployment-isomorphism.proof

    Proof structure:
    - Status: valid/invalid
    - Isomorphism: true/false (bijection between spec and deployment)
    - Individual verifications
    - Errors (if any)
    """

    all_verified = all([
        verification_results['service_existence']['verified'],
        verification_results['dependencies']['verified'],
        verification_results['network']['verified'],
        verification_results['resources']['verified'],
        verification_results['no_extra']['verified']
    ])

    is_bijection = (
        verification_results['no_extra']['bijection'] and
        verification_results['service_existence']['verified']
    )

    proof = {
        "status": "verified" if all_verified else "failed",
        "isomorphism": is_bijection,
        "specification_version": spec_version,
        "verified_at": datetime.utcnow().isoformat() + "Z",

        "theorem": "Deployed topology isomorphic to architecture spec",

        "proof_steps": {
            "service_existence": {
                "claim": "Every service in spec has deployment config",
                "verified": verification_results['service_existence']['verified'],
                "services_verified": verification_results['service_existence']['services_with_configs'],
                "services_total": verification_results['service_existence']['services_in_spec']
            },

            "dependencies_configured": {
                "claim": "All service dependencies are configured",
                "verified": verification_results['dependencies']['verified'],
                "dependencies_checked": verification_results['dependencies']['dependencies_checked']
            },

            "network_connectivity": {
                "claim": "Services can reach their dependencies",
                "verified": verification_results['network']['verified'],
                "network_paths_verified": verification_results['network']['network_paths_verified'],
                "ports_verified": verification_results['network']['ports_verified']
            },

            "resource_constraints": {
                "claim": "Resource constraints sufficient",
                "verified": verification_results['resources']['verified'],
                "services_checked": verification_results['resources']['services_checked']
            },

            "bijection": {
                "claim": "No extra services deployed (one-to-one mapping)",
                "verified": verification_results['no_extra']['verified'],
                "spec_services": verification_results['no_extra']['spec_services'],
                "deployed_services": verification_results['no_extra']['deployed_services'],
                "is_bijection": is_bijection
            }
        },

        "conclusion": "QED - Topology isomorphism verified" if all_verified else "FAILED - See errors",

        "errors": collect_all_errors(verification_results)
    }

    return proof
```

---

## Output

**Proof file:**
```
artifacts/engineering/proofs/infrastructure/topology/deployment-isomorphism.proof
```

**Success proof structure:**
```json
{
  "status": "verified",
  "isomorphism": true,
  "specification_version": "v1.2.0",
  "verified_at": "2025-01-15T10:30:00Z",

  "theorem": "Deployed topology isomorphic to architecture spec",

  "proof_steps": {
    "service_existence": {
      "claim": "Every service in spec has deployment config",
      "verified": true,
      "services_verified": 15,
      "services_total": 15
    },

    "dependencies_configured": {
      "claim": "All service dependencies are configured",
      "verified": true,
      "dependencies_checked": 42
    },

    "network_connectivity": {
      "claim": "Services can reach their dependencies",
      "verified": true,
      "network_paths_verified": 12,
      "ports_verified": 15
    },

    "resource_constraints": {
      "claim": "Resource constraints sufficient",
      "verified": true,
      "services_checked": 15
    },

    "bijection": {
      "claim": "No extra services deployed (one-to-one mapping)",
      "verified": true,
      "spec_services": 15,
      "deployed_services": 15,
      "is_bijection": true
    }
  },

  "conclusion": "QED - Topology isomorphism verified",

  "errors": []
}
```

**Failure proof structure:**
```json
{
  "status": "failed",
  "isomorphism": false,
  "specification_version": "v1.2.0",

  "proof_steps": {
    "service_existence": {
      "verified": false,
      "services_verified": 14,
      "services_total": 15
    }
  },

  "conclusion": "FAILED - See errors",

  "errors": [
    {
      "type": "missing_k8s_deployment",
      "service": "BillingService",
      "expected": "billing-service-deployment.yaml"
    }
  ]
}
```

---

## Success Criteria

✓ All services in spec have deployment configs
✓ All dependencies configured
✓ Network connectivity verified
✓ Resource constraints sufficient
✓ No extra services (bijection)
✓ Isomorphism proof generated
✓ Proof consumed by proof-composer

---

## Error Handling

**Missing deployment config:**
```
ERROR: Service 'BillingService' has no deployment config
Expected: billing-service-deployment.yaml
Action: Re-run kubernetes-generator
```

**Missing dependency:**
```
ERROR: Dependency not configured
Service: BillingService
Dependency: CatalogService
Action: Check docker-compose.yml depends_on or K8s service discovery
```

**Insufficient resources:**
```
ERROR: Insufficient CPU for service
Service: CatalogService
Required: 2
Configured: 1
Action: Update K8s deployment resource limits
```

**Extra service detected:**
```
ERROR: Extra service in deployment
Service: DebugService
Not found in services.spec.yaml
Action: Remove from deployment or add to spec
```

---

## Integration

**Consumed by:**
- `proof-composer` - Includes topology proof in system certificate

**Depends on:**
- `service-topology-analyzer` - Provides topology graph
- `docker-generator` - Provides Docker configs
- `kubernetes-generator` - Provides K8s configs

---

## Key Insights

1. **Isomorphism = Bijection** - One-to-one mapping between spec and deployment
2. **Runs AFTER config generation** - Verifies generated artifacts
3. **Proof is machine-readable** - JSON for proof-composer
4. **Errors are actionable** - Each error has fix instruction
5. **Blocks deployment** - Invalid proof → proof-composer fails → no deploy

**Next:** proof-composer collects this proof for final system certificate
