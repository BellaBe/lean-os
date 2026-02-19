# LeanOS Core

Open-source AI operating system for validating ideas and executing goals. 3 agents, 15 skills.

Define goals, research markets, reason through problems — all from the command line.

---

## What's Included

### Agents (3)

| Agent | What It Does |
|-------|-------------|
| `fnd-architect` | Sets up strategic foundation — business mode, constraints, context |
| `fnd-researcher` | Market research — TAM/SAM/SOM, segments, problem validation, competitors |
| `rsn-problem-solver` | Structured reasoning — causal, abductive, inductive, analogical, dialectical, counterfactual |

### Skills (15)

**System backbone (6)** — goal-driven execution:

| Skill | What It Does |
|-------|-------------|
| `sys-defining-goals` | Transform intent into measurable goal files |
| `sys-decomposing-goals` | Break goals into subgoal hierarchies |
| `sys-activating-goals` | Create execution threads from goals |
| `sys-tracking-goals` | Monitor progress against targets |
| `sys-executing-threads` | Write agent outputs to thread stage files |
| `sys-indexing-directories` | Generate index files for context loading |

**Reasoning (4)** — structured thinking:

| Skill | What It Does |
|-------|-------------|
| `rsn-reasoning-problems` | 6 cognitive modes for problem solving |
| `rsn-perceiving-information` | Systematic information gathering |
| `rsn-creating-ideas` | Creative ideation and novel solutions |
| `rsn-learning-outcomes` | Extract insights from outcomes |

**Foundations research (5)** — idea validation:

| Skill | What It Does |
|-------|-------------|
| `fnd.r-sizing-markets` | Calculate TAM/SAM/SOM |
| `fnd.r-segmenting-customers` | Define customer segments and ICP |
| `fnd.r-scoring-problems` | Score problem severity and willingness to pay |
| `fnd.r-analyzing-competition` | Map competitive landscape |
| `fnd-validating-gates` | Validate phase transition requirements |

---

## Quick Start

### 1. Install

```bash
git clone https://github.com/BellaBe/lean-os.git my-project
cd my-project
```

### 2. Set Up Your Project

```
run fnd-architect agent
```

This creates your business mode, captures constraints, and initializes `strategy/canvas/`.

### 3. Research Your Market

```
run fnd-researcher agent
```

Sizes your market, defines segments, scores the problem, maps competitors.

### 4. Define Your First Goal

```
run skill sys-defining-goals
```

Creates a measurable goal in `strategy/goals/active/`.

### 5. Execute

Goals create threads. Threads follow a 6-stage causal flow:

```
1-input → 2-hypothesis → 3-implication → 4-decision → 5-actions → 6-learning
```

Every action links to a goal. Every outcome captures learning.

---

## How It Works

```
You (decisions)
    |
Agents (orchestration)
    |
Skills (execution)
```

**Goals** drive **threads**. Threads follow a 6-stage causal flow. Agents execute threads by calling skills. The system reads index files on start for context.

### Directory Structure

```
my-project/
├── strategy/
│   ├── canvas/          # Business canvas
│   └── goals/           # Goal definitions
├── threads/             # Execution threads (6-stage causal flow)
├── artifacts/           # Deliverables
├── docs/                # Documentation
└── .claude/
    ├── agents/          # 3 orchestrators
    └── skills/          # 15 skills
```

### Business Modes

Set in `strategy/canvas/00.mode.md`:

| Mode | Optimizes For |
|------|---------------|
| **BOOTSTRAP** | Profitability, cash flow, fast decisions |
| **VENTURE** | Growth rate, market size, defensibility |

---

## Core vs Pro

Core validates your idea. [Pro](https://bellabe.github.io/leanos) builds and runs the business.

| Capability | Core | Pro |
|-----------|------|-----|
| Agents | 3 | 39 |
| Skills | 15 | 191 |
| Goal system | Full | Full |
| Reasoning | Full (6 modes) | Full + domain intelligence |
| Market research | Full | Full |
| Business modeling | -- | Pricing, unit economics, cost structure |
| GTM planning | -- | Channels, assumptions, launch plan |
| Engineering | -- | Backend IR pipeline, frontend, Shopify |
| Design systems | -- | Intent to web/infographic specs (16 skills) |
| Sales | -- | Outbound, partnerships, enablement |
| Marketing | -- | Inbound, content, campaigns |
| Customer success | -- | Onboarding, retention, expansion |
| RevOps | -- | Signals, scoring, allocation |
| Product | -- | Features, PLG, growth mechanics |
| Critique | -- | Quality validation across artifacts |
| Behavioral science | -- | Choice architecture, nudges |

**[Get LeanOS Pro](https://bellabe.github.io/leanos)**

---

## License

MIT. See [LICENSE](LICENSE).
