---
name: service-topology-analyzer
description: Analyze service topology from services.spec.yaml. Extracts dependencies, builds dependency graph, validates no cycles, determines initialization order. Sub-skill of infrastructure-prover.
version: 1.0.0
allowed-tools: bash_tool, view
model: claude-sonnet-4-20250514
license: Proprietary - LeanOS Engineering Layer
---

# service-topology-analyzer: Services Spec → Topology Graph

## Purpose

Analyze service topology and build dependency graph for deployment configuration.

**Input:** services.spec.yaml  
**Output:** Topology graph (JSON)

---

## Input

```
artifacts/engineering/specifications/v{X}/services.spec.yaml
```

**Expected structure:**
```yaml
services:
  - name: CatalogService
    type: microservice
    language: python
    framework: fastapi
    port: 8001
    
    dependencies:
      - name: postgres
        type: database
        external: true
      
      - name: redis
        type: cache
        external: true
      
      - name: nats
        type: message_queue
        external: true
    
    resources:
      cpu: 2
      memory: 4Gi
    
    health_check:
      path: /health
      interval: 30s
  
  - name: BillingService
    type: microservice
    language: python
    framework: fastapi
    port: 8002
    
    dependencies:
      - name: postgres
        type: database
        external: true
      
      - name: CatalogService
        type: service
        external: false
    
    resources:
      cpu: 1
      memory: 2Gi
```

---

## Analysis Process

### Step 1: Parse Services Spec

```python
import yaml

def parse_services_spec(spec_path):
    """Load and parse services.spec.yaml"""
    with open(spec_path) as f:
        spec = yaml.safe_load(f)
    
    services = []
    for service_def in spec['services']:
        services.append({
            'name': service_def['name'],
            'type': service_def['type'],
            'language': service_def.get('language'),
            'framework': service_def.get('framework'),
            'port': service_def.get('port'),
            'dependencies': service_def.get('dependencies', []),
            'resources': service_def.get('resources', {}),
            'health_check': service_def.get('health_check', {})
        })
    
    return services
```

---

### Step 2: Build Dependency Graph

```python
def build_dependency_graph(services):
    """
    Build directed graph of service dependencies
    
    Nodes: Services
    Edges: Dependencies (A → B means A depends on B)
    """
    
    graph = {}
    
    for service in services:
        service_name = service['name']
        dependencies = []
        
        for dep in service['dependencies']:
            dep_name = dep['name']
            dep_type = dep['type']
            is_external = dep.get('external', False)
            
            dependencies.append({
                'name': dep_name,
                'type': dep_type,
                'external': is_external
            })
        
        graph[service_name] = {
            'dependencies': dependencies,
            'service': service
        }
    
    return graph
```

**Example graph:**
```python
{
  'CatalogService': {
    'dependencies': [
      {'name': 'postgres', 'type': 'database', 'external': True},
      {'name': 'redis', 'type': 'cache', 'external': True},
      {'name': 'nats', 'type': 'message_queue', 'external': True}
    ],
    'service': {...}
  },
  'BillingService': {
    'dependencies': [
      {'name': 'postgres', 'type': 'database', 'external': True},
      {'name': 'CatalogService', 'type': 'service', 'external': False}
    ],
    'service': {...}
  }
}
```

---

### Step 3: Validate No Circular Dependencies

```python
def detect_cycles(graph):
    """
    Detect circular dependencies using DFS
    
    Returns: List of cycles (empty if no cycles)
    """
    
    def dfs(node, visited, rec_stack, path):
        visited.add(node)
        rec_stack.add(node)
        path.append(node)
        
        # Check dependencies (skip external)
        for dep in graph[node]['dependencies']:
            if dep['external']:
                continue
            
            dep_name = dep['name']
            
            if dep_name not in graph:
                # Dependency not in services (external or missing)
                continue
            
            if dep_name not in visited:
                cycle = dfs(dep_name, visited, rec_stack, path)
                if cycle:
                    return cycle
            elif dep_name in rec_stack:
                # Cycle detected
                cycle_start = path.index(dep_name)
                return path[cycle_start:] + [dep_name]
        
        rec_stack.remove(node)
        path.pop()
        return None
    
    visited = set()
    
    for node in graph:
        if node not in visited:
            cycle = dfs(node, visited, set(), [])
            if cycle:
                return [cycle]
    
    return []

def validate_no_cycles(graph):
    """Validate dependency graph has no cycles"""
    cycles = detect_cycles(graph)
    
    if cycles:
        raise ValueError(
            f"Circular dependency detected: {' → '.join(cycles[0])}"
        )
    
    return True
```

---

### Step 4: Determine Initialization Order

```python
def topological_sort(graph):
    """
    Determine service initialization order using topological sort
    
    Services with no dependencies start first
    Services depending on others start after dependencies
    """
    
    # Build in-degree map (count of dependencies)
    in_degree = {service: 0 for service in graph}
    
    for service in graph:
        for dep in graph[service]['dependencies']:
            if not dep['external'] and dep['name'] in graph:
                in_degree[dep['name']] += 1
    
    # Queue services with no dependencies
    queue = [service for service, degree in in_degree.items() if degree == 0]
    initialization_order = []
    
    while queue:
        # Sort for deterministic order
        queue.sort()
        service = queue.pop(0)
        initialization_order.append(service)
        
        # Reduce in-degree for dependents
        for other_service in graph:
            for dep in graph[other_service]['dependencies']:
                if dep['name'] == service and not dep['external']:
                    in_degree[other_service] -= 1
                    if in_degree[other_service] == 0:
                        queue.append(other_service)
    
    if len(initialization_order) != len(graph):
        raise ValueError("Cannot determine initialization order (cycle exists)")
    
    return initialization_order
```

**Example order:**
```python
['CatalogService', 'BillingService', 'AuthService']
# CatalogService has only external deps → starts first
# BillingService depends on CatalogService → starts second
# AuthService depends on CatalogService → starts third
```

---

### Step 5: Identify Network Requirements

```python
def identify_network_requirements(graph):
    """
    Identify network connectivity requirements
    
    Returns:
    - Internal network (services communicating)
    - External dependencies (databases, caches, etc)
    - Required ports
    """
    
    internal_network = []
    external_dependencies = set()
    required_ports = {}
    
    for service_name, service_data in graph.items():
        service = service_data['service']
        
        # Collect port
        if service.get('port'):
            required_ports[service_name] = service['port']
        
        # Analyze dependencies
        for dep in service_data['dependencies']:
            if dep['external']:
                # External dependency (postgres, redis, etc)
                external_dependencies.add(dep['name'])
            else:
                # Internal service-to-service communication
                internal_network.append({
                    'from': service_name,
                    'to': dep['name'],
                    'type': dep['type']
                })
    
    return {
        'internal_network': internal_network,
        'external_dependencies': list(external_dependencies),
        'required_ports': required_ports
    }
```

**Example network requirements:**
```python
{
  'internal_network': [
    {'from': 'BillingService', 'to': 'CatalogService', 'type': 'service'}
  ],
  'external_dependencies': ['postgres', 'redis', 'nats'],
  'required_ports': {
    'CatalogService': 8001,
    'BillingService': 8002,
    'AuthService': 8003
  }
}
```

---

### Step 6: Generate Dependency Matrix

```python
def generate_dependency_matrix(graph):
    """
    Generate matrix showing which services depend on which
    
    Useful for visualization and verification
    """
    
    services = sorted(graph.keys())
    matrix = {}
    
    for service in services:
        matrix[service] = {}
        for other_service in services:
            # Check if service depends on other_service
            depends = any(
                dep['name'] == other_service and not dep['external']
                for dep in graph[service]['dependencies']
            )
            matrix[service][other_service] = depends
    
    return matrix
```

**Example matrix:**
```
                CatalogService  BillingService  AuthService
CatalogService       False          False         False
BillingService       True           False         False
AuthService          True           False         False
```

---

## Output: Topology Graph

**Complete topology graph:**
```json
{
  "specification_version": "v1.2.0",
  "analyzed_at": "2025-01-15T10:30:00Z",
  
  "services": {
    "CatalogService": {
      "type": "microservice",
      "language": "python",
      "framework": "fastapi",
      "port": 8001,
      "dependencies": [
        {"name": "postgres", "type": "database", "external": true},
        {"name": "redis", "type": "cache", "external": true},
        {"name": "nats", "type": "message_queue", "external": true}
      ],
      "resources": {
        "cpu": 2,
        "memory": "4Gi"
      },
      "health_check": {
        "path": "/health",
        "interval": "30s"
      }
    },
    "BillingService": {
      "type": "microservice",
      "language": "python",
      "framework": "fastapi",
      "port": 8002,
      "dependencies": [
        {"name": "postgres", "type": "database", "external": true},
        {"name": "CatalogService", "type": "service", "external": false}
      ],
      "resources": {
        "cpu": 1,
        "memory": "2Gi"
      }
    }
  },
  
  "topology": {
    "initialization_order": ["CatalogService", "BillingService", "AuthService"],
    
    "dependency_graph": {
      "nodes": ["CatalogService", "BillingService", "AuthService"],
      "edges": [
        {"from": "BillingService", "to": "CatalogService"},
        {"from": "AuthService", "to": "CatalogService"}
      ]
    },
    
    "dependency_matrix": {
      "CatalogService": {"CatalogService": false, "BillingService": false, "AuthService": false},
      "BillingService": {"CatalogService": true, "BillingService": false, "AuthService": false},
      "AuthService": {"CatalogService": true, "BillingService": false, "AuthService": false}
    }
  },
  
  "network": {
    "internal_network": [
      {"from": "BillingService", "to": "CatalogService", "type": "service"},
      {"from": "AuthService", "to": "CatalogService", "type": "service"}
    ],
    "external_dependencies": ["postgres", "redis", "nats"],
    "required_ports": {
      "CatalogService": 8001,
      "BillingService": 8002,
      "AuthService": 8003
    }
  },
  
  "validation": {
    "no_cycles": true,
    "initialization_order_valid": true,
    "all_dependencies_resolvable": true
  }
}
```

---

## Output Location

```
artifacts/engineering/code/frontend/.internal/topology-graph.json
```

(Internal file, not part of final output)

---

## Success Criteria

✓ Services spec parsed
✓ Dependency graph built
✓ No circular dependencies
✓ Initialization order determined
✓ Network requirements identified
✓ Dependency matrix generated
✓ Topology graph validated

---

## Error Handling

**Circular dependency:**
```
ERROR: Circular dependency detected
Cycle: CatalogService → BillingService → CatalogService
Action: Remove circular dependency from services.spec.yaml
```

**Unresolvable dependency:**
```
ERROR: Cannot resolve dependency
Service: BillingService
Dependency: CatalogService
Issue: CatalogService not defined in services.spec.yaml
Action: Add CatalogService or mark dependency as external
```

**Invalid initialization order:**
```
ERROR: Cannot determine initialization order
Issue: Dependency graph has cycle
Action: Fix circular dependencies
```

---

## Key Insights

1. **Topology graph is internal** - Used by other sub-skills, not deployed
2. **External dependencies marked** - postgres, redis, etc don't appear in graph
3. **Initialization order critical** - Services start in dependency order
4. **Network requirements explicit** - Service-to-service communication defined
5. **Validation is structural** - Graph analysis (decidable, fast)

**Next:** docker-generator and kubernetes-generator use this topology graph