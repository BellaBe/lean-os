# Product Context Summary: LeanOS Dashboard UI

## Target Users

### Primary: Startup Founders / Solo Operators
- Running 1-3 person teams
- Want to operate like 5-10 person teams
- Spend less than 30 min/day on operations
- Technical enough to use CLI tools (Claude Code)
- Need visibility into what the AI is doing autonomously

### Secondary: Potential LeanOS Adopters
- Exploring LeanOS as a solution
- Need to understand the value proposition quickly
- Want to see how autonomous AI operations work in practice

## Problems to Solve

### Problem 1: Invisible AI Operations - Intensity: 5/5
Users can't see what LeanOS is doing. 70+ skills, 13 agents, goals, threads, canvas sections - all happen in the file system. No visual way to understand:
- What's running right now?
- What decisions were made?
- What's the state of my business?

### Problem 2: System Comprehension - Intensity: 4/5
LeanOS is powerful but complex. New users struggle to understand:
- How goals flow to threads to artifacts
- What each skill/agent does
- How the Canvas connects to execution
- What the 6-stage causal flow means

### Problem 3: Trust in Autonomous Operations - Intensity: 4/5
AI making 95%+ of decisions is scary. Users need:
- Transparency into decision rationale
- Ability to see impact scores before approval
- Confidence in what's being auto-executed vs flagged

## Solution Direction

A **showcase dashboard** that visualizes the LeanOS operating system:

1. **System Overview** - Health metrics, active work, recent decisions
2. **Goal Visualization** - Goal tree with progress and linked threads
3. **Canvas Health** - 15-section strategy status with coverage map
4. **Thread Activity** - Real-time view of 6-stage executions
5. **Skill/Agent Catalog** - Browsable capability reference
6. **Research Knowledge** - Sources and playbooks library

## Critical Assumptions

- A1: Users will understand LeanOS faster through visualization than reading markdown
- A2: Seeing autonomous decisions in real-time builds trust, not fear
- A3: A showcase UI will drive LeanOS adoption more than documentation
- A4: The leanos.json data structure is sufficient for UI needs
