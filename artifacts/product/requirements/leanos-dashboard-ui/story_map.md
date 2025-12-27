# User Story Map: LeanOS Dashboard UI

## BACKBONE (User Activities)

```
[Understand System] --> [Monitor Operations] --> [Explore Capabilities] --> [Review History]
```

## STORY MAP

```
+---------------------------+---------------------------+---------------------------+---------------------------+
|    UNDERSTAND SYSTEM      |    MONITOR OPERATIONS     |   EXPLORE CAPABILITIES    |      REVIEW HISTORY       |
+---------------------------+---------------------------+---------------------------+---------------------------+
|                           |                           |                           |                           |
|  TASK: Get Overview       |  TASK: Track Goals        |  TASK: Browse Skills      |  TASK: View Threads       |
|  -----------------------  |  -----------------------  |  -----------------------  |  -----------------------  |
|  US-001 Dashboard Home    |  US-004 Goal List         |  US-008 Skill Catalog     |  US-012 Thread List       |
|  US-002 System Stats      |  US-005 Goal Detail       |  US-009 Skill Detail      |  US-013 Thread Detail     |
|  US-003 Quick Actions     |  US-006 Goal Progress     |  US-010 Agent Catalog     |  US-014 Stage Viewer      |
|                           |  US-007 Goal Tree         |  US-011 Agent Detail      |  US-015 Thread Timeline   |
+---------------------------+---------------------------+---------------------------+---------------------------+
|                           |                           |                           |                           |
|  TASK: View Canvas        |  TASK: Track Threads      |  TASK: View Research      |  TASK: View Artifacts     |
|  -----------------------  |  -----------------------  |  -----------------------  |  -----------------------  |
|  US-016 Canvas Overview   |  US-019 Active Threads    |  US-022 Source Library    |  US-025 Artifact Browser  |
|  US-017 Section Detail    |  US-020 Thread Progress   |  US-023 Playbook Library  |  US-026 Artifact Detail   |
|  US-018 Canvas Health Map |  US-021 Stage Status      |  US-024 Source Viewer     |                           |
|                           |                           |                           |                           |
+---------------------------+---------------------------+---------------------------+---------------------------+
```

## RELEASE SLICES

### Release 1: Walking Skeleton (Core Showcase)
Priority: MUST HAVE - Demonstrates the LeanOS value proposition

| Story | Description | Why Essential |
|-------|-------------|---------------|
| US-001 | Dashboard Home | Entry point, first impression |
| US-002 | System Stats | Shows system health at a glance |
| US-016 | Canvas Overview | Visualizes the 15-section strategy |
| US-019 | Active Threads | Shows what's executing now |
| US-008 | Skill Catalog | Demonstrates 70+ capabilities |

### Release 2: Goal-Centric View
Priority: HIGH - Shows the goal-driven operating model

| Story | Description | Why Important |
|-------|-------------|---------------|
| US-004 | Goal List | All active goals |
| US-005 | Goal Detail | Goal structure and state |
| US-006 | Goal Progress | Visual progress indicators |
| US-012 | Thread List | All threads by type |
| US-013 | Thread Detail | Full 6-stage view |

### Release 3: Deep Exploration
Priority: MEDIUM - For users who want to understand deeply

| Story | Description | Why Valuable |
|-------|-------------|--------------|
| US-007 | Goal Tree | Hierarchical goal visualization |
| US-017 | Section Detail | Canvas section content viewer |
| US-018 | Canvas Health Map | Visual health grid |
| US-010 | Agent Catalog | 13 agent orchestrators |
| US-022 | Source Library | Research sources |

### Release 4: Complete Experience
Priority: LOW - Polish and completeness

| Story | Description | Why Nice |
|-------|-------------|----------|
| US-003 | Quick Actions | Action shortcuts |
| US-009 | Skill Detail | Individual skill deep dive |
| US-011 | Agent Detail | Agent skill routing |
| US-014 | Stage Viewer | Individual stage content |
| US-015 | Thread Timeline | Temporal thread view |
| US-023 | Playbook Library | Generated playbooks |
| US-024 | Source Viewer | Source detail view |
| US-025 | Artifact Browser | Generated artifacts |
| US-026 | Artifact Detail | Artifact content |

## WALKING SKELETON FLOW

```
User arrives at /
        |
        v
+-------------------+
|   Dashboard Home  |  <-- System overview, entry point
|   (US-001)        |
+-------------------+
        |
   +----+----+
   |    |    |
   v    v    v
+------+  +-------+  +--------+
|Canvas|  |Threads|  |Skills  |
|Grid  |  |Active |  |Catalog |
+------+  +-------+  +--------+
   |         |           |
   v         v           v
[Understand] [See what's] [Know what
 Strategy]   running]     it can do]
```

## SUCCESS METRICS

| Metric | Target | How Measured |
|--------|--------|--------------|
| Time to understand | <60 seconds | User can explain what LeanOS does |
| Information density | High | Key stats visible without scrolling |
| Navigation depth | <3 clicks | Any detail accessible quickly |
| Visual appeal | Impressive | Suitable for demos/presentations |
