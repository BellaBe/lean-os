# Daily Routine

Operational cadence for running LeanOS Core. Covers daily, weekly, and trigger-based routines.

---

## Quick Reference

| Time | Routine | Key Actions |
|------|---------|-------------|
| Morning | Start of Day | Review goals, check threads, set priorities |
| Throughout | Work | Progress threads through causal flow |
| End of Day | Close of Day | Update threads, capture learnings |
| Weekly | Review | Goal tracking, thread cleanup, planning |

---

## Morning Routine

### 1. Review Active Goals

```
SCAN strategy/goals/active/*.md

FOR EACH goal with status = activated:
  +-- Check: thread progress
  +-- Check: blockers
  +-- Check: today's milestone
```

### 2. Check Active Threads

```
SCAN threads/*/

FOR EACH thread with open actions:
  +-- Read 5-actions.md
  +-- Identify: what's next?

PRIORITIZE by:
1. Critical goal threads
2. Time-sensitive threads
3. Quick wins
4. Deep work threads
```

### 3. Set Today's Focus

Pick your top 3 goal-linked tasks for the day.

---

## Throughout the Day

### Thread Progression

```
FOR active thread:

1. READ current state
   +-- Where are we in causal flow?

2. EXECUTE next stage
   +-- 2-hypothesis.md --> Form hypothesis (use rsn-reasoning-problems)
   +-- 3-implication.md --> Derive implications
   +-- 4-decision.md --> Make decision (use rsn-reasoning-problems.dialectical)
   +-- 5-actions.md --> Execute actions

3. UPDATE thread
   +-- Document progress in 5-actions.md

4. CHECK completion
   +-- IF actions complete:
       +-- Write 6-learning.md (use rsn-learning-outcomes.reflection)
       +-- sys-tracking-goals updates goal
```

### Quick Decisions

```
FOR items < 5 min:
- Handle immediately
- Don't create thread (overhead > value)

FOR items > 15 min:
- Create thread
- Link to goal
```

---

## End of Day Routine

### 1. Update Active Threads

```
FOR EACH thread worked today:
  +-- Update 5-actions.md with progress
  +-- Note blockers
  +-- Identify next action
```

### 2. Capture Learnings

```
IF significant learning today:
  +-- Write to relevant thread's 6-learning.md

LEARNING TRIGGERS:
- Something failed unexpectedly
- Something succeeded unexpectedly
- Pattern noticed
- Process improvement idea
```

### 3. Check Goal Progress

```
FOR goals worked today:
  +-- Update current_value if measurable
  +-- sys-tracking-goals will recalculate gaps
```

---

## Weekly Routine

### 1. Goal Review

```
INVOKE sys-tracking-goals (full scan)

FOR EACH active goal:
  +-- Review: target vs current
  +-- Review: trajectory (on pace?)

IDENTIFY:
- Goals on track (continue)
- Goals at risk (intervention needed)
- Goals achieved (close)
- Goals to abandon (document why)
```

### 2. Thread Cleanup

```
FOR stale threads (no activity > 7 days):
  +-- Decide: continue, pause, or close
  +-- IF close: write 6-learning.md

FOR completed threads:
  +-- Ensure 6-learning.md complete
```

### 3. Learning Aggregation

```
COLLECT learnings from:
- Thread 6-learning.md files
- Failed experiments
- Successful tactics

IDENTIFY patterns:
- What's working?
- What's not?
```

### 4. Next Week Planning

```
FOR EACH goal:
  +-- What must happen next week?
  +-- What threads need activation?

SET weekly priorities (3 max)
```

---

## Trigger-Based Routines

### On New Opportunity

```
1. INVOKE sys-defining-goals
2. INVOKE sys-activating-goals
3. Begin causal flow in thread
```

### On Experiment Completion

```
1. READ results
2. INVOKE rsn-reasoning-problems.inductive (what patterns?)
3. DECIDE: continue / pivot / stop
4. UPDATE 6-learning.md
```

### On Planning Cycle

```
1. REVIEW canvas (still accurate?)
2. SET new goals (sys-defining-goals)
3. DECOMPOSE if needed (sys-decomposing-goals)
4. ACTIVATE (sys-activating-goals)
```

### On Pivot Decision

```
1. DOCUMENT why (6-learning.md)
2. ASSESS canvas impact
3. RE-RUN fnd-architect + fnd-researcher
4. RE-DEFINE goals from updated canvas
```

---

## Solo Operator Tips

**Batch similar work.** Process all thread updates together. Reduces context-switching.

**Use threads as memory.** Write to thread immediately. Trust the system to remind you.

**Weekly review is non-negotiable.** Skip daily routine sometimes. Never skip weekly review.

**Limit active goals.** 3-5 max. Fewer goals, more progress.

**Capture learnings immediately.** Learning fades fast. Even one sentence helps.

---

## Quick Commands

```bash
# Morning
"What goals need attention today?"
"What threads are active?"

# Thread work
"Continue thread for [context]"
"Update actions for [thread]"
"Complete thread and capture learnings"

# Reasoning
"Figure out why [problem]"
"Brainstorm options for [challenge]"
"What patterns do you see in [data]?"

# Goal tracking
"How are we tracking against [goal]?"
"Run full goal review"

# Foundations
"Help me define my business mode"
"Size my market for [idea]"
"Analyze competition in [space]"
```
