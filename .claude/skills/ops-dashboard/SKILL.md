---
name: ops-dashboard
description: Generate operational dashboards with 3-tier temporal structure. Daily (today.md), weekly (changes.md, velocity.md), and historical (archive/). Tracks business, engineering, sales, and marketing threads. Manages archiving, compression, and metrics computation.
allowed-tools: "Read,Write,Bash,Edit,Glob"
---

# Operations Dashboard Generator

Manage operational visibility with a clean 3-tier temporal structure.

**Thread types tracked:** Business, Engineering, Sales, Marketing
**Artifact types tracked:** Sales collateral, Marketing content, Engineering specs/proofs/configs

## Output Structure

```
ops/
├── today.md          # TODAY: Active work, needs attention, thread status
├── changes.md        # THIS WEEK: Rolling changelog (7-day window)
├── velocity.md       # COMPUTED: Weekly metrics, cycle times, throughput
├── patterns.md       # COMPUTED: Anomalies, meta-thread triggers (weekly)
└── archive/          # HISTORICAL: Daily completed items only
    ├── 2025-11-18.md
    ├── 2025-11-19.md
    └── weekly/       # Weekly summaries (compressed from changes.md)
```

---

## 3-Tier Temporal Structure

### Tier 1: TODAY (ops/today.md)

**Purpose:** Founder's daily 5-minute entry point
**Update frequency:** Daily (start of day, after major completions)

**Contains:**
- ✅ Completed Today (what got done)
- 🔴 Needs Your Attention (high-impact decisions, approvals)
- 📅 This Week's Actions (due dates, owners)
- 📊 Active Threads Summary (business, engineering, sales, marketing)
- 🔧 Engineering Progress (specs, proofs, deployments)
- 📈 Campaign Status (live progress)
- 🔮 Upcoming (next 7 days)
- 📊 Metrics to Monitor

**Does NOT contain:**
- Historical completed items (→ archive/)
- Detailed change logs (→ changes.md)
- Computed metrics (→ velocity.md)

---

### Tier 2: THIS WEEK (ops/changes.md + ops/velocity.md)

#### changes.md - Rolling Changelog

**Purpose:** Track what changed for velocity measurement
**Update frequency:** After each significant change
**Retention:** Current week only (7-day rolling window)

**Structure:**
```markdown
# Strategic Changes Log

**Purpose:** Track what changed day-to-day for velocity measurement
**Retention:** Current week (older entries compressed to weekly/)

---

## 2025-11-25

### {Change Title}
**Files changed:** {count and names}
**Impact:** {what it enables/fixes}

**Changes made:**
- {Detail 1}
- {Detail 2}

**Velocity metric:**
- {Measurable outcome}
- Time: {hours spent}

---

## 2025-11-24
...
```

**Compression rules:**
- At end of week (Sunday): Compress week's entries into summary
- Move summary to `archive/weekly/week-{YYYY-WW}.md`
- Keep only current week in changes.md

#### velocity.md - Computed Metrics

**Purpose:** Weekly metrics, cycle times, throughput analysis
**Update frequency:** Weekly (Sunday) or on-demand
**Computation:** Derived from threads + changes.md + archive

**Structure:**
```markdown
# Velocity Analysis - Week of {date}

## This Week Summary
- Threads completed: X
- Content published: Y pieces
- Threads created: Z
- Total changes logged: N

## Cycle Time by Thread Type
| Type | Avg Days | Threads | Variance |
|------|----------|---------|----------|
| Business | X | Y | Z% |
| Engineering | X | Y | Z% |
| Sales | X | Y | Z% |
| Marketing | X | Y | Z% |

## Throughput Trends
- This week: X threads completed
- Last week: Y threads completed
- Trend: ↑/↓ Z%

## Efficiency Metrics
- AI autonomy rate: X%
- Decision latency: <24h
- First-time quality: X%

---
**Computed:** {timestamp}
**Next update:** {next Sunday}
```

---

### Tier 3: HISTORICAL (ops/archive/)

**Purpose:** Permanent record of completed work
**Update frequency:** Daily (end of day or next morning)

**Structure:**
```
archive/
├── 2025-11-18.md     # Daily: completed items only
├── 2025-11-19.md
├── ...
└── weekly/
    ├── week-2025-47.md  # Weekly summary (compressed from changes.md)
    └── week-2025-48.md
```

#### Daily Archive Format

```markdown
# Operations Dashboard - {YYYY-MM-DD}

## ✅ Completed Today

### {Item 1 Title}
- ✓ {What was done}
- ✓ {Details}

### {Item 2 Title}
- ✓ {What was done}

---

**Archived:** {YYYY-MM-DD}
```

#### Weekly Summary Format

```markdown
# Week {WW} Summary - {date range}

## Highlights
- {Major accomplishment 1}
- {Major accomplishment 2}

## Threads
- Completed: X
- Created: Y
- Active end of week: Z

## Content Published
- {List of published content}

## Engineering Artifacts
- {Specs generated}
- {Proofs validated}
- {Configs deployed}

## Key Changes
- {Compressed list of significant changes}

## Velocity
- Avg cycle time: X days
- AI autonomy: X%

---

**Compressed from:** changes.md entries {date} - {date}
```

---

## Archive Management

### Archive Principle

**Archives contain ONLY what was completed. Future/pending items belong in today.md.**

### What Gets Archived vs Stays

| Content Type | Archive? | Stay in today.md? | Goes to changes.md? |
|--------------|----------|-------------------|---------------------|
| ✅ Completed Today | ✓ YES | Remove after archive | Log significant ones |
| 🔴 Needs Attention | ✗ NO | ✓ YES | ✗ NO |
| 📅 This Week's Actions | ✗ NO | ✓ YES | ✗ NO |
| 📊 Active Threads | ✗ NO | ✓ YES (update) | ✗ NO |
| 📈 Campaign Status | ✗ NO | ✓ YES (update) | ✗ NO |
| 🔧 Engineering Progress | ✗ NO | ✓ YES (update) | Log milestones |
| File changes | ✗ NO | ✗ NO | ✓ YES |
| Velocity metrics | ✗ NO | ✗ NO | → velocity.md |

### Daily Archive Workflow

**End of day or start of next day:**

1. **Read today.md** - Extract "✅ Completed Today" section
2. **Create archive file** - `archive/{YYYY-MM-DD}.md`
3. **Write completed items** - Full details of what was done
4. **Add footer** - `**Archived:** {date}`
5. **Update today.md** - Clear completed section, update thread statuses

### Weekly Compression Workflow

**Every Sunday (or Monday morning):**

1. **Read changes.md** - All entries from past week
2. **Create weekly summary** - `archive/weekly/week-{YYYY-WW}.md`
3. **Compress entries** - Keep highlights, remove granular details
4. **Clear changes.md** - Remove entries older than 7 days
5. **Update velocity.md** - Compute metrics from the week

---

## Changelog Management (changes.md)

### When to Log Changes

**Log to changes.md when:**
- Files created/deleted/significantly modified
- Canvas sections updated
- Skills added/modified
- Threads created/completed (business, engineering, sales, marketing)
- Engineering artifacts generated (specs, proofs, configs)
- Content published
- Process improvements implemented

**Don't log:**
- Minor typo fixes
- Formatting changes
- Routine status updates (those go to today.md)

### Change Entry Format

```markdown
## {YYYY-MM-DD}

### {Descriptive Title}
**Files changed:** {count} ({list key files})
**Impact:** {What this enables or fixes}

**Changes made:**
1. {Specific change 1}
2. {Specific change 2}

**Velocity metric:**
- {Measurable outcome: files, words, threads, time}
- Time: {hours spent}
```

### Compression Rules

**Keep detailed entries for current week only.**

**At week end, compress to:**
```markdown
### Week {WW}: {One-line summary}
- {Bullet 1: Major change}
- {Bullet 2: Major change}
- Threads: +X created, Y completed
- Files: Z modified
```

---

## Velocity Computation

### When to Compute

- **Weekly:** Sunday evening or Monday morning
- **On-demand:** Before important decisions, quarterly reviews
- **After milestones:** Campaign completions, major thread closures

### Metrics to Compute

**From threads:**
- Thread counts by type/state (business, engineering, sales, marketing)
- Stage distribution
- Cycle time (days per stage, total completion)
- Completion rate
- Engineering thread progress (specs generated, proofs validated)

**From changes.md:**
- Files changed per week
- Time spent on changes
- Change velocity (changes per day)

**From archive:**
- Historical trends
- Week-over-week comparison

### Velocity.md Computation Script

```bash
# Count threads by state
find threads/ -name "metadata.yaml" -exec grep -l "status:" {} \;

# Count completed this week
find ops/archive/ -name "*.md" -mtime -7 | wc -l

# Sum velocity metrics from changes.md
grep "Time:" ops/changes.md | # extract and sum
```

---

## Pattern Detection (ops/patterns.md)

### When to Update

- **Weekly:** During velocity computation
- **On trigger:** When pattern rules fire

### Pattern Rules

```
1. Estimation Variance: variance >40% with N≥5 → meta-thread
2. Validation Rate: <60% with N≥10 → meta-thread
3. Decision Revision: >20% revision rate with N≥5 → meta-thread
4. Stage Bottleneck: >3 threads stuck >7 days → immediate flag
```

### Pattern File Format

```markdown
# Pattern Detection - {date}

## 🚨 Active Patterns

### {Pattern Name}
**Severity:** HIGH/MEDIUM/LOW
**Detected:** {date}
**Data:** {metrics}
**Action:** {meta-thread / monitor / resolved}

## 📊 Pattern History

| Pattern | Detected | Status | Resolution |
|---------|----------|--------|------------|
| {name} | {date} | RESOLVED | {what fixed it} |

---
**Last computed:** {timestamp}
```

---

## Workflow Summary

### Daily Routine

1. **Morning:** Generate/update today.md
2. **After work:** Log significant changes to changes.md
3. **End of day:** Archive completed items

### Weekly Routine (Sunday/Monday)

1. **Compress changes.md** → archive/weekly/
2. **Compute velocity.md** from threads + changes + archive
3. **Check patterns.md** for anomalies
4. **Clean up today.md** for new week

### Monthly Routine

1. **Review velocity trends** (4-week comparison)
2. **Archive weekly summaries** older than 4 weeks (optional compression)
3. **Update baseline targets** if needed

---

## Best Practices

1. **Keep today.md actionable** - Only what needs attention NOW
2. **Log changes promptly** - Don't batch up a week's changes
3. **Compress weekly** - Don't let changes.md grow infinitely
4. **Archive is sacred** - Only completed items, no pending work
5. **Compute, don't maintain** - velocity.md is computed, not manually updated
6. **Patterns are triggers** - They lead to meta-threads or process fixes

---

## Success Criteria

✓ **Founder's 5-min review** - today.md has everything needed
✓ **Clean archives** - Only completed items, no forward-looking content
✓ **Rolling changelog** - changes.md stays <7 days of entries
✓ **Weekly velocity** - Computed metrics available every Monday
✓ **No stale files** - Everything either current or explicitly historical

---

**Last updated:** 2025-11-25
