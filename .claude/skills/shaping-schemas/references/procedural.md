# Procedural Schema Reference

Create repeatable, deterministic processes.

## When to Use

Use procedural schema when output is:
- Runbook or SOP
- Checklist or playbook
- Step-by-step guide
- Repeatable process documentation

## Output Structure

```yaml
procedure:
  name: string
  version: string
  last_updated: date
  
  purpose: string
  triggers:
    - "[When to use this procedure]"
    
  prerequisites:
    - item: string
      required: bool
      check: string
      
  steps:
    - number: int
      action: string
      expected_outcome: string
      notes: optional<string>
      warning: optional<string>
      
  decision_points:
    - at_step: int
      condition: string
      if_true: string
      if_false: string
      
  escalation:
    - condition: string
      escalate_to: string
      urgency: low | medium | high | critical
      
  rollback:
    - trigger: string
      actions: [string]
      
  checklist: [string]
```

## Construction Process

### Step 1: Define Purpose and Triggers

Answer:
- What does this procedure accomplish?
- When should someone use it?
- What conditions trigger it?

```yaml
purpose: "Deploy code changes to production environment"
triggers:
  - "Code merged to main branch"
  - "Hotfix approved for immediate deployment"
  - "Scheduled release window"
```

### Step 2: List Prerequisites

For each prerequisite:
- What's needed before starting?
- Is it required or optional?
- How to verify it's ready?

```yaml
prerequisites:
  - item: "CI pipeline passed"
    required: true
    check: "Green checkmark on PR"
    
  - item: "Staging verification complete"
    required: true
    check: "QA sign-off in ticket"
    
  - item: "Rollback plan documented"
    required: true
    check: "Link in deployment ticket"
```

### Step 3: Enumerate Steps

For each step:
- One action per step (atomic)
- Clear expected outcome
- Warnings for risky steps

```yaml
steps:
  - number: 1
    action: "Announce deployment in #deployments channel"
    expected_outcome: "Team aware, no objections within 5 min"
    
  - number: 2
    action: "Create deployment branch from main"
    expected_outcome: "Branch 'deploy/YYYY-MM-DD' exists"
    
  - number: 3
    action: "Run database migrations"
    expected_outcome: "Migrations complete, no errors in logs"
    warning: "POINT OF NO RETURN - rollback requires restore"
    
  - number: 4
    action: "Deploy application containers"
    expected_outcome: "All pods healthy in k8s dashboard"
```

### Step 4: Define Decision Points

Where does the procedure branch?

```yaml
decision_points:
  - at_step: 3
    condition: "Migration fails"
    if_true: "STOP. Go to Rollback section."
    if_false: "Continue to step 4"
    
  - at_step: 4
    condition: "Health checks fail after 5 minutes"
    if_true: "Execute rollback procedure"
    if_false: "Continue to step 5"
```

### Step 5: Define Escalation

When to involve others?

```yaml
escalation:
  - condition: "Deployment blocked >30 minutes"
    escalate_to: "On-call engineer"
    urgency: high
    
  - condition: "Data integrity concerns"
    escalate_to: "Database team lead"
    urgency: critical
```

### Step 6: Define Rollback

How to undo if needed?

```yaml
rollback:
  - trigger: "Health checks fail"
    actions:
      - "Revert deployment to previous version"
      - "Verify health checks pass"
      - "Announce rollback in #deployments"
      
  - trigger: "Migration failure"
    actions:
      - "Restore database from pre-deploy backup"
      - "Redeploy previous application version"
      - "Create incident ticket"
```

### Step 7: Create Checklist

Summary for quick reference:

```yaml
checklist:
  - "☐ CI pipeline green"
  - "☐ QA sign-off obtained"
  - "☐ Rollback plan ready"
  - "☐ Deployment announced"
  - "☐ Migrations complete"
  - "☐ App deployed"
  - "☐ Health checks passing"
  - "☐ Monitoring verified"
  - "☐ Deployment closed"
```

## Complete Example

```yaml
procedure:
  name: "Production Deployment"
  version: "2.1"
  last_updated: "2024-01-15"
  
  purpose: "Deploy code changes to production safely and reversibly"
  
  triggers:
    - "Code merged to main with deployment label"
    - "Hotfix approved by engineering lead"
    - "Scheduled Thursday deployment window"
    
  prerequisites:
    - item: "CI pipeline passed"
      required: true
      check: "Green status on main branch"
      
    - item: "QA sign-off"
      required: true
      check: "Comment in deployment ticket"
      
    - item: "Database backup <1 hour old"
      required: true
      check: "Backup timestamp in S3"
      
  steps:
    - number: 1
      action: "Post deployment start in #deployments"
      expected_outcome: "Message posted, no blocks within 5 min"
      
    - number: 2
      action: "Run pre-deploy checks: ./scripts/pre-deploy.sh"
      expected_outcome: "All checks pass, green output"
      
    - number: 3
      action: "Execute database migrations: ./scripts/migrate.sh"
      expected_outcome: "Migrations complete, 'SUCCESS' in output"
      warning: "Creates rollback complexity—verify backup first"
      
    - number: 4
      action: "Deploy via: kubectl apply -f production/"
      expected_outcome: "All pods show Running status"
      
    - number: 5
      action: "Verify health: curl https://api.example.com/health"
      expected_outcome: "200 OK with version matching deploy"
      
    - number: 6
      action: "Run smoke tests: ./scripts/smoke-test.sh"
      expected_outcome: "All critical paths pass"
      
    - number: 7
      action: "Post deployment complete in #deployments"
      expected_outcome: "Message posted with version number"
      
  decision_points:
    - at_step: 2
      condition: "Pre-deploy checks fail"
      if_true: "STOP. Fix issues before proceeding."
      if_false: "Continue to step 3"
      
    - at_step: 5
      condition: "Health check fails after 3 attempts"
      if_true: "Execute rollback procedure"
      if_false: "Continue to step 6"
      
  escalation:
    - condition: "Rollback fails"
      escalate_to: "On-call SRE"
      urgency: critical
      
    - condition: "Deployment blocked >1 hour"
      escalate_to: "Engineering manager"
      urgency: high
      
  rollback:
    - trigger: "Health checks fail OR smoke tests fail"
      actions:
        - "kubectl rollout undo deployment/api"
        - "Verify previous version healthy"
        - "If migrations ran: restore from backup"
        - "Post rollback notice in #deployments"
        - "Create incident ticket"
        
  checklist:
    - "☐ CI green"
    - "☐ QA signed off"
    - "☐ Backup verified"
    - "☐ Deployment announced"
    - "☐ Pre-deploy passed"
    - "☐ Migrations complete"
    - "☐ App deployed"
    - "☐ Health check passing"
    - "☐ Smoke tests passing"
    - "☐ Deployment closed"
```

## Quality Gates

| Gate | Requirement |
|------|-------------|
| Steps atomic | One action per step |
| Outcomes defined | Every step has expected outcome |
| Decisions explicit | Branch conditions clear |
| Rollback complete | Can undo from any step |
| Escalation clear | Know who to contact when |

## Anti-Patterns

| Avoid | Do Instead |
|-------|------------|
| Multi-action steps | One action per step |
| Vague outcomes | Specific, verifiable outcomes |
| Missing rollback | Every procedure needs undo |
| Assumed knowledge | List all prerequisites |
| Hidden decisions | Explicit decision points |
