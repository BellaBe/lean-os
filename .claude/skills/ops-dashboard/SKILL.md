---
name: ops-dashboard
description: Generate observability dashboards by scanning all threads (business/sales/marketing), aggregating metrics, detecting patterns, and flagging issues for human review or meta-thread creation. Creates ops/today.md, ops/metrics.md, ops/velocity.md, ops/patterns.md.
allowed-tools: "Read,Write,Bash"
---

# Operations Dashboard Generator

You are an expert at extracting insights from distributed thread data and generating actionable dashboards for AI agents and human operators.

## Purpose

Scan all threads across business/sales/marketing, aggregate metrics, detect operational patterns, and generate auto-updated dashboards that:
- Provide daily operational overview (ops/today.md)
- Track cross-thread KPIs (ops/metrics.md)
- Measure throughput velocity (ops/velocity.md)
- Flag anomalies requiring meta-threads (ops/patterns.md)
- Surface strategic changes for human review (ops/changes.md)

## When to Use This Skill

**Use when:**
- Starting the day (generate ops/today.md for Bella's 5-min review)
- Weekly meta-learning check (detect patterns → spawn meta-threads)
- Before quarterly Canvas review (prepare comprehensive metrics)
- After major thread completion (update velocity baselines)
- On-demand when investigating operational issues

**Don't use when:**
- Working within a specific thread (use causal-flow instead)
- Creating/updating individual thread files
- Making strategic decisions (dashboards inform, don't decide)

## Output Structure

**Path:** `ops/`

```
ops/
├── today.md                    # Daily dashboard (Bella's entry point)
├── metrics.md                  # Cross-thread KPIs
├── velocity.md                 # Throughput & cycle time analysis
├── patterns.md                 # Detected anomalies → meta-thread triggers
└── changes.md                  # Strategic flags for human review
```

---

## Dashboard Generation Workflow

### Step 1: Scan Thread Directories

```bash
# Find all threads across types
find threads/ -name "meta.json" -type f
```

**Extract from each `meta.json`:**
- Thread type (business/sales/marketing)
- Thread state (draft/active/in_review/completed/archived)
- Current stage (1-7)
- Timestamps (created, stage transitions, completed)
- Impact score (for decision authority)
- Hypothesis ID (link to Canvas assumptions)
- Actions count and types

### Step 2: Aggregate Metrics

**Calculate:**

1. **Thread counts by type/state:**
   - Total threads: N
   - Active threads: X (state=active)
   - Completed this week/month/quarter
   - By type: business/sales/marketing breakdown

2. **Stage distribution:**
   - Threads at each stage (1-7)
   - Bottlenecks (stage with >3 threads stuck >7 days)

3. **Cycle time:**
   - Average days per stage
   - Total thread completion time
   - Variance by thread type

4. **Decision metrics:**
   - AI autonomy rate (decisions with impact <0.7)
   - Human intervention rate
   - Decision revision rate (decisions changed after stage 4)

5. **Hypothesis validation:**
   - Validation rate (validated / total tested)
   - Invalidation rate
   - Confidence changes (before/after)

6. **Action execution:**
   - Action completion rate
   - Average actions per thread
   - Typed action distribution (sales/marketing)

### Step 3: Detect Patterns (Meta-Thread Triggers)

**Pattern detection rules:**

```python
# Estimation variance
if variance(stage_duration) > 0.4 and sample_size >= 5:
    flag_pattern("estimation_variance", affected_stages)

# Validation rate
if validation_rate < 0.6 and sample_size >= 10:
    flag_pattern("low_validation_rate", hypothesis_ids)

# Decision revision
if decision_revision_rate > 0.2 and sample_size >= 5:
    flag_pattern("decision_churn", affected_threads)

# Stage quality
if stage_quality_score < 0.7 and issue_count > 0.3 * total:
    flag_pattern("stage_quality_issue", stage_number)

# Bottlenecks
if threads_at_stage > 3 and avg_days_stuck > 7:
    flag_pattern("stage_bottleneck", stage_number)
```

**Each pattern includes:**
- Pattern type
- Affected threads/stages
- Severity (low/medium/high)
- Recommended action (create meta-thread / adjust process / flag human)
- Sample size (N)

### Step 4: Generate Dashboards

#### ops/today.md

**Purpose:** Bella's daily 5-minute entry point

**Structure:**
```markdown
# Operations Dashboard - {date}

## 🎯 Needs Your Attention
- [ ] {High-impact decision waiting approval} (impact: 0.85)
- [ ] {Customer call today} - Sales thread S012
- [ ] {Quarterly Canvas review due}

## 📊 Today's Snapshot
- **Active threads:** X business, Y sales, Z marketing
- **Completed this week:** N threads
- **AI autonomy rate:** 94% (target: >95%)

## 🚨 Flags
- {Pattern detected: estimation variance in Stage 3} → Consider meta-thread
- {Strategic change: Invalidated assumption A7} → Review Canvas

## 📈 Velocity
- **Avg cycle time:** X days (↓ 12% vs last month)
- **Stage bottleneck:** Stage 5 (4 threads stuck >7 days)

---
[View detailed metrics](./metrics.md) | [View patterns](./patterns.md)
```

#### ops/metrics.md

**Purpose:** Comprehensive KPI tracking

**Structure:**
```markdown
# Cross-Thread Metrics - {date}

## Thread Overview
| Type | Draft | Active | In Review | Completed | Archived |
|------|-------|--------|-----------|-----------|----------|
| Business | X | Y | Z | A | B |
| Sales | X | Y | Z | A | B |
| Marketing | X | Y | Z | A | B |

## Stage Distribution
| Stage | Threads | Avg Days | Variance |
|-------|---------|----------|----------|
| 1: Input | X | Y | Z% |
| 2: Hypothesis | X | Y | Z% |
| ... | ... | ... | ... |

## Decision Authority
- **AI autonomous:** 156 decisions (96%)
- **Human review:** 7 decisions (4%)
- **Decision revision rate:** 8% (target: <20%)

## Hypothesis Validation
- **Validated:** 34 (68%)
- **Invalidated:** 12 (24%)
- **Testing:** 4 (8%)
- **Avg confidence change:** +18% (before: 52% → after: 70%)

## Action Execution
- **Total actions:** 248
- **Completed:** 231 (93%)
- **In progress:** 17 (7%)
- **By type (sales):** lead: 45, qualify: 38, demo: 22, pilot: 12, close: 9
- **By type (marketing):** research: 18, create: 34, publish: 29, promote: 15, measure: 12

## Cycle Time
- **Business threads:** 12.4 days avg (variance: 32%)
- **Sales threads:** 18.7 days avg (variance: 41%) ⚠️
- **Marketing threads:** 9.2 days avg (variance: 28%)

---
Last updated: {timestamp}
```

#### ops/velocity.md

**Purpose:** Throughput and efficiency analysis

**Structure:**
```markdown
# Velocity Analysis - {date}

## Throughput Trends
- **This week:** 8 threads completed (↑ 14% vs last week)
- **This month:** 32 threads completed
- **This quarter:** 89 threads completed

## Cycle Time by Stage (days)
| Stage | Current | Baseline | Delta |
|-------|---------|----------|-------|
| 1: Input | 0.8 | 1.0 | ↓ 20% |
| 2: Hypothesis | 1.6 | 2.0 | ↓ 20% |
| 3: Implication | 2.4 | 3.0 | ↓ 20% |
| 4: Decision | 1.2 | 2.0 | ↓ 40% |
| 5: Actions | 8.7 | 10.0 | ↓ 13% |
| 6: Learning | 1.8 | 2.0 | ↓ 10% |

## Bottleneck Analysis
**Current bottlenecks (>3 threads, >7 days):**
- Stage 5 (Actions): 4 threads, avg 11.2 days stuck
  - Threads: B023, S014, M007, S018
  - Root cause: Waiting on external dependencies

## Efficiency Metrics
- **First-time quality:** 87% (decisions not revised)
- **Rework rate:** 13%
- **Canvas update accuracy:** 94%

## Improvement Opportunities
1. **Stage 5 dependencies:** Create dependency tracking system
2. **Sales cycle time:** 41% variance indicates estimation issues
3. **Hypothesis quality:** 24% invalidation rate acceptable but monitor

---
Last updated: {timestamp}
```

#### ops/patterns.md

**Purpose:** Meta-thread triggers and anomaly detection

**Structure:**
```markdown
# Pattern Detection - {date}

## 🚨 Meta-Thread Triggers

### Pattern: Estimation Variance (Sales Cycle Time)
**Severity:** HIGH
**Detected:** {date}
**Rule:** Variance >40% with N≥5
**Data:**
- Sample size: 12 sales threads
- Variance: 41% (threshold: 40%)
- Affected stages: Stage 3 (Implication), Stage 5 (Actions)

**Recommended Action:** CREATE META-THREAD
```
threads/business/meta-sales-estimation/
1-input: Sales cycle time variance exceeds threshold
2-hypothesis: Current estimation model doesn't account for deal complexity
3-implication: Overruns cause resource allocation issues
4-decision: Implement deal complexity scoring
5-actions: Create scoring model, update templates
6-learning: Validate if complexity scoring reduces variance
```

---

### Pattern: Stage Bottleneck (Stage 5)
**Severity:** MEDIUM
**Detected:** {date}
**Rule:** >3 threads stuck >7 days
**Data:**
- Stuck threads: 4 (B023, S014, M007, S018)
- Average days stuck: 11.2
- Common blocker: External dependencies

**Recommended Action:** PROCESS ADJUSTMENT
- Add dependency tracking to Stage 4 (Decision)
- Flag external dependencies for proactive management
- Monitor for 2 weeks before meta-thread

---

### Pattern: Low Validation Rate
**Severity:** LOW
**Detected:** {date}
**Rule:** <60% validation rate with N≥10
**Data:**
- Sample size: 50 hypotheses
- Validation rate: 68% (threshold: 60%)
- Status: MONITORING (above threshold but trending down)

**Recommended Action:** CONTINUE MONITORING
- Check again in 2 weeks
- Create meta-thread if drops below 60%

---

## 📊 Pattern History
| Pattern Type | First Detected | Status | Meta-Thread Created |
|--------------|----------------|--------|---------------------|
| Estimation Variance (Sales) | 2025-10-15 | ACTIVE | threads/business/meta-sales-estimation |
| Decision Churn (Business) | 2025-09-22 | RESOLVED | threads/business/meta-decision-quality |

---
Last updated: {timestamp}
```

#### ops/changes.md

**Purpose:** Strategic flags requiring human review

**Structure:**
```markdown
# Strategic Changes - {date}

## 🔴 High Priority (Review This Week)

### Invalidated Assumption: A7 (Enterprise Sales Cycle)
**Thread:** threads/sales/acme-corp/7-learning.md
**Original hypothesis:** Enterprise deals close in 45-60 days
**Learning:** Actually 90-120 days due to procurement processes
**Canvas impact:**
- `strategy/canvas/11-pricing.md` - Update cash flow assumptions
- `strategy/canvas/14-growth.md` - Adjust quarterly targets
- `strategy/canvas/15-gtm.md` - Add procurement education to sales process

**Action required:** Review and approve Canvas updates

---

### Major Pivot Detected (Impact: 0.92)
**Thread:** threads/business/white-label-sdk/4-decision.md
**Decision:** Launch white-label SDK (new business model)
**Canvas impact:** Affects 8 Canvas sections
**Action required:** Schedule strategic review session

---

## 🟡 Medium Priority (Review This Month)

### New Opportunity: API-First Customers
**Thread:** threads/sales/dev-tools-co/7-learning.md
**Learning:** Developer tools companies prefer API over UI
**Canvas impact:**
- `strategy/canvas/04-segments.md` - Add "Developer Tools" segment
- `strategy/canvas/09-solution.md` - Prioritize API development

**Action required:** Validate segment size before Canvas update

---

## 🟢 Low Priority (FYI)

### Validated Assumption: A12 (LinkedIn Engagement)
**Thread:** threads/marketing/linkedin-q4/7-learning.md
**Original hypothesis:** 2-3 posts/week drives engagement
**Learning:** Confirmed - engagement up 47%
**Canvas status:** Already updated in `strategy/canvas/15-gtm.md`

---
Last updated: {timestamp}
```

---

## Execution Pattern

### On-Demand Generation

```bash
# Generate all dashboards
./generate_ops_dashboards.sh

# Or generate specific dashboard
./generate_ops_today.sh
./generate_ops_metrics.sh
```

### Scheduled Generation

**Daily:** `ops/today.md` (before Bella's day starts)
**Weekly:** All dashboards (Sunday night)
**Monthly:** Add trend analysis
**Quarterly:** Add historical comparison

### Pattern Detection Workflow

1. **Scan threads:** Extract metrics from meta.json + stage files
2. **Apply rules:** Check each pattern detection rule
3. **Calculate severity:** Based on sample size + deviation
4. **Generate recommendations:** Meta-thread template or process adjustment
5. **Update ops/patterns.md:** Add new patterns, update existing
6. **Flag in ops/today.md:** Surface high-severity patterns
7. **Auto-create meta-thread:** If severity=HIGH and human approves

---

## Meta-Thread Creation

When pattern detection triggers meta-thread:

### Step 1: Generate Meta-Thread Proposal

```markdown
## Proposed Meta-Thread: {pattern-type}

**Trigger:** {pattern detection rule}
**Data:** {metrics that triggered}
**Expected ROI:** {estimated time saved vs time invested}

**Thread structure:**
threads/business/meta-{pattern-name}/
1-input: {observation from pattern}
2-hypothesis: {root cause hypothesis}
3-implication: {impact analysis}
4-decision: {proposed solution}
5-actions: {implementation steps}
6-learning: {process improvement}
```

### Step 2: Human Approval

Add to `ops/today.md` under "Needs Your Attention"
- [ ] Create meta-thread for {pattern}? (ROI: X hours saved)

### Step 3: Execute Meta-Thread

Use `causal-flow` skill to execute standard 6-stage flow
Apply learnings to improve operational processes

### Step 4: Validate Improvement

Track same metrics for next N threads
Confirm pattern resolved
Update baseline metrics

---

## Best Practices

1. **Generate daily** - Keep ops/today.md fresh for Bella's morning review
2. **Monitor patterns weekly** - Don't let issues compound
3. **Low false positives** - Only trigger meta-threads for clear patterns (N≥5)
4. **Actionable insights** - Every flag must have recommended action
5. **Trend over snapshot** - Track direction (↑↓), not just current value
6. **Auto-update changes.md** - Stage 7 (Learning) should append to ops/changes.md
7. **Validate thresholds** - Adjust pattern detection rules based on meta-learning

---

## Success Criteria

✓ **Bella's 5-min dashboard** - ops/today.md has everything needed
✓ **Pattern detection** - Catches operational issues before they compound
✓ **Meta-thread triggers** - Clear ROI justification for process improvement
✓ **Zero manual updates** - All dashboards auto-generated from thread data
✓ **Actionable flags** - Every issue has recommended next step
✓ **Strategic alignment** - Canvas changes surfaced for human review

---

## Remember

This is Bella's primary human interface to GlamOS. Keep ops/today.md concise, actionable, and focused on what requires human attention. Everything else is for AI agents to self-optimize.