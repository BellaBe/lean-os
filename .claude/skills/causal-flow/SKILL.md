# SKILL.md

```markdown
---
name: causal-flow
description: Orchestrate evidence-based decision making through 6 stages. Manages business threads, sales pipelines, and marketing campaigns with automatic Canvas updates.
allowed-tools: "Read,Write,Bash"
version: 2.0.0
---

# Causal Flow Orchestrator

You orchestrate evidence-based decision flows across 6 stages, delegating execution to specialized stage skills.

## Purpose

Execute systematic decision-making:
- Start with factual observations (Stage 1)
- Challenge business assumptions (Stage 2)
- Analyze full impact (Stage 3)
- Make official commitment (Stage 4)
- Execute coordinated actions (Stage 5)
- Validate and update Canvas (Stage 6)

## When to Use This Orchestrator

**Use when:**
- Starting new business decision thread
- Starting new sales pipeline thread
- Starting new marketing campaign thread
- Managing multiple concurrent threads

**Don't use when:**
- Adding observation to existing thread (invoke Stage 1 directly)
- Re-analyzing hypothesis only (invoke Stage 2 directly)
- Updating action progress only (invoke Stage 5 directly)
- Documenting learning only (invoke Stage 6 directly)

## Thread Types

Load thread-specific architecture as needed:

### Business Threads
**Path:** `/mnt/project/Causal_Flow_Skill/reference/business-threads.md`
**Use for:** Strategic decisions, product changes, market positioning
**Action types:** Engineering, legal, marketing, sales, operations

### Sales Threads
**Path:** `/mnt/project/Causal_Flow_Skill/reference/sales-threads.md`
**Use for:** Deal pipelines, individual prospects, enterprise opportunities
**Action types:** lead-intake, qualification, demo, pilot, close

### Marketing Threads
**Path:** `/mnt/project/Causal_Flow_Skill/reference/marketing-threads.md`
**Use for:** Campaign execution, content launches, market research
**Action types:** research, create, publish, promote, measure

## Orchestration Workflow

### Step 1: Determine Thread Type

Ask user if unclear:
- Business decision? → `threads/business/{name}/`
- Sales opportunity? → `threads/sales/{name}/`
- Marketing campaign? → `threads/marketing/{name}/`

### Step 2: Load Thread-Specific Architecture

```bash
# Load appropriate reference document
Read /mnt/project/Causal_Flow_Skill/reference/{type}-threads.md
```

This provides:
- Thread structure conventions
- Action type catalogs
- Metadata schemas
- Workflow patterns

### Step 3: Execute 6-Stage Flow

Invoke stage skills **sequentially**:

1. **Stage 1: Input** → Invoke `causal-flow-input`
2. **Stage 2: Hypothesis** → Invoke `causal-flow-hypothesis`
3. **Stage 3: Implication** → Invoke `causal-flow-implication`
4. **Stage 4: Decision** → Invoke `causal-flow-decision`
5. **Stage 5: Actions** → Invoke `causal-flow-actions`
6. **Stage 6: Learning** → Invoke `causal-flow-learning`

**CRITICAL:** Do NOT execute stage logic in this orchestrator. Delegate to stage skills.

### Step 4: Track Progress

Monitor thread state:
- `draft` → `active` → `in_review` → `completed` → `archived`

Update `ops/today.md` with high-impact items (≥0.8).

## Canvas Integration

**Location:** `strategy/canvas/` (15 markdown files)
**Primary for causal flow:** `strategy/canvas/10-assumptions.md`

Stage skills handle Canvas reading/updating automatically. Orchestrator only needs to know:
- Canvas exists
- Stage 2 reads assumptions
- Stage 6 updates assumptions

## Output Storage

**Strategy:** `strategy/canvas/`, `strategy/financials/`
**Artifacts:** `artifacts/sales/`, `artifacts/marketing/`, `artifacts/fundraising/`
**Threads:** `threads/{type}/{name}/` (working documents)

Stage skills route output correctly. Orchestrator doesn't need to know routing details.

## Decision Authority

**AI Autonomous (Impact <0.8):**
- Within strategic direction
- ROI > 3x, risk low-medium
- Cost <$100K, timeline <3 months

**Human Review (Impact ≥0.8):**
- Strategic pivot
- ROI <2x, high risk
- Cost ≥$100K, timeline ≥3 months

Stage 4 skill calculates impact and flags appropriately.

## Execution Pattern

**User provides input:**
```
1. Determine thread type
2. Load {type}-threads.md reference
3. Create thread structure
4. Invoke Stage 1 skill
5. Orchestrate Stages 2-6 (sequential invocation)
6. Monitor progress, flag exceptions
```

**Example:**
```
User: "ElsaAI wants white-label SDK, $400K budget"

1. Type: sales
2. Read /mnt/project/Causal_Flow_Skill/reference/sales-threads.md
3. Create threads/sales/elsa-white-label/
4. Invoke causal-flow-input (Stage 1)
5. Invoke causal-flow-hypothesis (Stage 2)
6. ... continue through Stage 6
```

## Available Resources

### Stage Skills
- `/mnt/project/Causal_Flow_Skill/stages/causal-flow-input/SKILL.md`
- `/mnt/project/Causal_Flow_Skill/stages/causal-flow-hypothesis/SKILL.md`
- `/mnt/project/Causal_Flow_Skill/stages/causal-flow-implication/SKILL.md`
- `/mnt/project/Causal_Flow_Skill/stages/causal-flow-decision/SKILL.md`
- `/mnt/project/Causal_Flow_Skill/stages/causal-flow-actions/SKILL.md`
- `/mnt/project/Causal_Flow_Skill/stages/causal-flow-learning/SKILL.md`

### Reference Documentation
- `/mnt/project/Causal_Flow_Skill/reference/business-threads.md`
- `/mnt/project/Causal_Flow_Skill/reference/sales-threads.md`
- `/mnt/project/Causal_Flow_Skill/reference/marketing-threads.md`

### Action Templates
- `/mnt/project/Causal_Flow_Skill/actions/templates/sales-*.md`
- `/mnt/project/Causal_Flow_Skill/actions/templates/marketing-*.md`

## Success Criteria

✓ **Evidence-based:** Starts with factual observation (Stage 1)
✓ **Hypothesis-driven:** Challenges assumptions (Stage 2)
✓ **Impact-analyzed:** Full cost/benefit (Stage 3)
✓ **Traceable:** Complete audit trail (Stages 1-6)
✓ **Self-correcting:** Canvas updates (Stage 6)
✓ **Autonomous:** AI executes >95%
✓ **Strategic:** Human review only when flagged

## Remember

Every decision—business, sales, or marketing—flows through **6 stages**. No shortcuts.

**This orchestrator:**
- Routes to appropriate thread type
- Loads thread-specific architecture
- Invokes stage skills sequentially
- Monitors progress

**This orchestrator does NOT:**
- Execute stage logic (delegate to stage skills)
- Know stage execution details (stage skills handle)
- Contain reference material (load on-demand)
