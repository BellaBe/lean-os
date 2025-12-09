---
name: kubernetes-generator
description: Generate Kubernetes deployment manifests from service topology. Creates Deployments, Services, Ingress, ConfigMaps with resource quotas and probes. Sub-skill of infrastructure-prover.
version: 1.0.0
allowed-tools: bash_tool, create_file
model: claude-sonnet-4-20250514
license: Proprietary - LeanOS Engineering Layer
---

# kubernetes-generator: Topology → Kubernetes Manifests

## Purpose

Generate Kubernetes manifests for production deployment.

**Input:** Service topology graph  
**Output:** K8s YAML manifests

---

## Generated Manifests

### 1. Deployment per Service

```yaml
# catalog-deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: catalog-service
  labels:
    app: catalog
    version: v1
spec:
  replicas: 3
  selector:
    matchLabels:
      app: catalog
  template:
    metadata:
      labels:
        app: catalog
        version: v1
    spec:
      containers:
      - name: catalog
        image: catalog:v1.0.0
        ports:
        - containerPort: 8001
        env:
        - name: DATABASE_URL
          valueFrom:
            secretKeyRef:
              name: catalog-secrets
              key: database-url
        resources:
          limits:
            cpu: "2"
            memory: "4Gi"
          requests:
            cpu: "1"
            memory: "2Gi"
        livenessProbe:
          httpGet:
            path: /health
            port: 8001
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /health
            port: 8001
          initialDelaySeconds: 5
          periodSeconds: 5
```

---

### 2. Service Definitions

```yaml
# services.yaml
apiVersion: v1
kind: Service
metadata:
  name: catalog-service
spec:
  selector:
    app: catalog
  ports:
  - protocol: TCP
    port: 8001
    targetPort: 8001
  type: ClusterIP
---
apiVersion: v1
kind: Service
metadata:
  name: billing-service
spec:
  selector:
    app: billing
  ports:
  - protocol: TCP
    port: 8002
    targetPort: 8002
  type: ClusterIP
```

---

### 3. Ingress Rules

```yaml
# ingress.yaml
apiVersion: networking.k8s.io/v1
kind: Ingress
metadata:
  name: api-ingress
  annotations:
    nginx.ingress.kubernetes.io/rewrite-target: /
spec:
  rules:
  - host: api.example.com
    http:
      paths:
      - path: /catalog
        pathType: Prefix
        backend:
          service:
            name: catalog-service
            port:
              number: 8001
      - path: /billing
        pathType: Prefix
        backend:
          service:
            name: billing-service
            port:
              number: 8002
```

---

### 4. ConfigMaps and Secrets Templates

```yaml
# configmaps.yaml
apiVersion: v1
kind: ConfigMap
metadata:
  name: catalog-config
data:
  LOG_LEVEL: "info"
  ENVIRONMENT: "production"
---
# secrets.yaml.template (not committed)
apiVersion: v1
kind: Secret
metadata:
  name: catalog-secrets
type: Opaque
data:
  database-url: <base64-encoded>
  jwt-secret: <base64-encoded>
```

---

## Output Structure

```
artifacts/engineering/configs/k8s/
├── catalog-deployment.yaml
├── billing-deployment.yaml
├── auth-deployment.yaml
├── services.yaml
├── ingress.yaml
├── configmaps.yaml
├── secrets.yaml.template
└── README.md
```

---

## Key Features

- **Deployments:** Replicas, rolling updates, resource limits
- **Services:** ClusterIP for internal, LoadBalancer for external
- **Ingress:** HTTP routing with path-based rules
- **Probes:** Liveness (restart) and readiness (traffic)
- **ConfigMaps:** Environment-specific config
- **Secrets:** Sensitive data (templates only)

---

## Success Criteria

✓ Deployment per service
✓ Services configured (ClusterIP)
✓ Ingress rules for routing
✓ Resource quotas set
✓ Probes configured
✓ ConfigMaps/Secrets templates

**Next:** ci-cd-generator creates build/deploy pipelines
