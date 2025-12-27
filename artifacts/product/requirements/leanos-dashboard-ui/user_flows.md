# User Flows: LeanOS Dashboard UI

## Flow 1: First-Time User Understanding LeanOS

**Goal:** Understand what LeanOS is and what it can do in under 60 seconds

```
[Open Dashboard /]
       |
       v
+------------------+
| Dashboard Home   |
|                  |
| See stats cards: |
| - 0 goals        |
| - 0% canvas      |
| - 6 threads      |
| - 70 skills      |
+------------------+
       |
   User thinks: "What are all these?"
       |
       v
+------------------+
| Click "Skills"   |
| (Skill Catalog)  |
|                  |
| Browse 70 skills |
| by category:     |
| - engineering    |
| - sales          |
| - marketing      |
| - reasoning      |
+------------------+
       |
   User thinks: "Wow, 70 AI skills!"
       |
       v
+------------------+
| Click "Canvas"   |
| (Canvas Overview)|
|                  |
| See 15-section   |
| grid with status |
| indicators       |
+------------------+
       |
   User thinks: "This is my strategy layer"
       |
       v
+------------------+
| Click "Threads"  |
| (Thread List)    |
|                  |
| See 6 threads    |
| with 6-stage     |
| progress bars    |
+------------------+
       |
   User understands: "Goals -> Canvas -> Threads -> Done"
       |
       v
[User Understands LeanOS]
```

**Key Insight:** The dashboard should tell the story of LeanOS through navigation flow.

---

## Flow 2: Checking System Health

**Goal:** Assess operational state of the business

```
[Open Dashboard /]
       |
       v
+------------------+
| Dashboard Home   |
|                  |
| Quick scan:      |
| - Canvas: 0%     |
|   (needs setup)  |
| - Threads: 6     |
|   (2 completed)  |
+------------------+
       |
   Concern: Canvas is empty
       |
       v
+------------------+
| Click Canvas     |
| Health Card      |
|                  |
| See grid with    |
| all 15 sections  |
| marked "missing" |
+------------------+
       |
       v
+------------------+
| See CTA:         |
| "Run Canvas      |
|  Setup"          |
|                  |
| Understand next  |
| action needed    |
+------------------+
       |
       v
[User Knows to Run Canvas Setup in CLI]
```

---

## Flow 3: Reviewing Active Work

**Goal:** See what the AI is working on

```
[Open Dashboard /]
       |
       v
+------------------+
| Dashboard Home   |
|                  |
| See "Active      |
| Threads" summary |
| in sidebar       |
+------------------+
       |
   Click "View All Threads"
       |
       v
+------------------+
| Thread List      |
|                  |
| SALES (2)        |
| - example [done] |
| - campaigns [1]  |
|                  |
| MARKETING (2)    |
| - example [done] |
| - campaigns [1]  |
|                  |
| OPERATIONS (2)   |
| - example [done] |
| - archive [1]    |
+------------------+
       |
   Click on "sales/example"
       |
       v
+------------------+
| Thread Detail    |
|                  |
| [1] Input        |
| [2] Hypothesis   |
| [3] Implication  |
| [4] Decision     |
| [5] Actions      |
| [6] Learning     |
|                  |
| All stages show  |
| as completed     |
+------------------+
       |
   User clicks Stage 4 (Decision)
       |
       v
+------------------+
| Stage Content    |
|                  |
| See decision     |
| rationale with   |
| impact score     |
+------------------+
       |
       v
[User Understands What Was Decided and Why]
```

---

## Flow 4: Exploring System Capabilities

**Goal:** Learn what LeanOS can do

```
[Open Dashboard /]
       |
       v
+------------------+
| Click "Skills"   |
| card or nav      |
+------------------+
       |
       v
+------------------+
| Skill Catalog    |
|                  |
| Categories:      |
| [>] action (11)  |
| [>] engineering  |
| [>] foundations  |
| [>] marketing    |
| [>] product      |
| [>] reasoning    |
| [>] sales        |
+------------------+
       |
   Click "engineering" category
       |
       v
+------------------+
| Engineering      |
| Skills (20)      |
|                  |
| engineering-     |
| spec-objects     |
| "Extract type    |
| definitions..."  |
|                  |
| engineering-     |
| build-category   |
| "Formalize       |
| domain..."       |
+------------------+
       |
   User sees: "SPEC -> BUILD -> VERIFY -> GEN pipeline"
       |
       v
+------------------+
| Click "Agents"   |
| in sidebar       |
|                  |
| See 13 agents    |
| that orchestrate |
| these skills     |
+------------------+
       |
       v
[User Understands Skill/Agent Architecture]
```

---

## Flow 5: Tracking Goal Progress

**Goal:** See progress toward business objectives

```
[Open Dashboard /]
       |
       v
+------------------+
| Click "Goals"    |
| card (0 active)  |
+------------------+
       |
       v
+------------------+
| Goal List        |
|                  |
| [Empty State]    |
| "No active goals"|
|                  |
| CTA: "Create     |
| your first goal  |
| using goal-setter|
| skill in CLI"    |
+------------------+

--- OR (if goals exist) ---

+------------------+
| Goal List        |
|                  |
| g-launch-mvp     |
| [=======---] 70% |
| 5/7 criteria met |
|                  |
| g-first-customer |
| [====------] 40% |
| 2/5 criteria met |
+------------------+
       |
   Click "g-launch-mvp"
       |
       v
+------------------+
| Goal Detail      |
|                  |
| Objective:       |
| Launch MVP by Q1 |
|                  |
| Success Criteria:|
| [x] Define specs |
| [x] Build backend|
| [ ] Build UI     |
|                  |
| Linked Threads:  |
| - eng/mvp-specs  |
| - eng/backend    |
+------------------+
       |
       v
[User Sees Goal Structure and Progress]
```

---

## Flow 6: Viewing Research & Knowledge

**Goal:** Access synthesized knowledge base

```
[Open Dashboard /]
       |
       v
+------------------+
| Click "Research" |
| in navigation    |
+------------------+
       |
       v
+------------------+
| Research Library |
|                  |
| SOURCES (0)      |
| [Empty State]    |
| "Process expert  |
| sources to build |
| knowledge base"  |
|                  |
| PLAYBOOKS (0)    |
| [Empty State]    |
| "Generate        |
| playbooks from   |
| sources"         |
+------------------+

--- OR (if populated) ---

+------------------+
| Research Library |
|                  |
| SOURCES          |
| - product-ops    |
| - user-story-map |
| - shape-up       |
|                  |
| PLAYBOOKS        |
| - sales-process  |
| - content-strat  |
+------------------+
       |
   Click source
       |
       v
+------------------+
| Source Detail    |
|                  |
| Insights from    |
| source content   |
|                  |
| Key takeaways    |
| and frameworks   |
+------------------+
       |
       v
[User Accesses Knowledge Base]
```

---

## Navigation Map

```
                    +------------------+
                    |   Dashboard (/)  |
                    +------------------+
                           |
       +-------------------+-------------------+
       |         |         |         |         |
       v         v         v         v         v
   +-------+ +-------+ +-------+ +-------+ +--------+
   | Goals | |Canvas | |Threads| |Skills | |Research|
   +-------+ +-------+ +-------+ +-------+ +--------+
       |         |         |         |         |
       v         v         v         v         v
   +-------+ +-------+ +-------+ +-------+ +--------+
   |Goal   | |Section| |Thread | |Skill  | |Source  |
   |Detail | |Detail | |Detail | |Detail | |Detail  |
   +-------+ +-------+ +-------+ +-------+ +--------+
       |
       v
   +-------+
   |Goal   |
   |Tree   |
   +-------+
```

---

## Empty States

### No Goals
```
+------------------------------------------+
|  [icon: target]                          |
|                                          |
|  No active goals                         |
|                                          |
|  Goals drive all LeanOS operations.      |
|  Create your first goal using the        |
|  goal-setter skill:                      |
|                                          |
|  > claude "Create a goal to launch MVP"  |
|                                          |
+------------------------------------------+
```

### Empty Canvas
```
+------------------------------------------+
|  [icon: grid]                            |
|                                          |
|  Canvas needs setup (0/15 sections)      |
|                                          |
|  The Canvas is your strategic foundation.|
|  Populate it using foundations-builder:  |
|                                          |
|  > claude "Set up my Canvas"             |
|                                          |
+------------------------------------------+
```

### No Research
```
+------------------------------------------+
|  [icon: book]                            |
|                                          |
|  No knowledge sources yet                |
|                                          |
|  Process expert content to build your    |
|  knowledge base using knowledge-builder: |
|                                          |
|  > claude "Process this video: [URL]"    |
|                                          |
+------------------------------------------+
```

---

## Key UX Principles

1. **Progressive Disclosure** - Show summary first, details on click
2. **Clear Empty States** - Guide users on what to do when data is missing
3. **Visual Progress** - Use progress bars, completion indicators
4. **Consistent Navigation** - Same pattern for all detail views
5. **Status at a Glance** - Color-coded indicators for health/status
