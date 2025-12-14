# Skills and Agents Architecture

Reference documentation for Claude Code skills and subagents in LeanOS.

---

## Overview

| Concept | What It Is | When to Use |
|---------|------------|-------------|
| **Skill** | Instructions/expertise injected into context | Domain knowledge, procedures, templates |
| **Subagent** | Separate AI instance with own context window | Orchestration, parallel work, isolated tasks |

---

## Skills

### What They Are
- Markdown files with instructions Claude reads and follows
- Injected into the main conversation context
- Claude stays in the same conversation after loading

### File Structure
```
.claude/skills/{skill-name}/
├── SKILL.md              # Required - main instructions
├── references/           # Optional - supporting docs
│   ├── template.md
│   └── patterns.md
└── examples/             # Optional - examples
```

### SKILL.md Format
```markdown
---
name: skill-name
description: Brief description (max 1024 chars) - include WHEN to use
allowed-tools: Read, Grep, Glob  # Optional - omit for full access
---

## Purpose
What this skill does.

## Instructions
Step-by-step guidance.

## Inputs
What the skill expects.

## Outputs
What the skill produces.
```

### Key Points
- **Flat structure**: Only top-level skills are registered (`.claude/skills/{name}/SKILL.md`)
- **Nested files are references**: Subdirectories are NOT separate skills, just supporting docs
- **Description matters**: Claude uses it to decide when to auto-load the skill
- **Stateless**: Just instructions, no memory between invocations

---

## Subagents

### What They Are
- Separate AI instances spawned via the Task tool
- Have their own context window (don't see conversation history)
- Execute independently and return a final report
- Can load multiple skills into their context

### File Location
```
.claude/agents/{agent-name}.md
```

### File Format
```markdown
---
name: agent-name
description: When this agent should be invoked
skills: skill1, skill2, skill3  # Optional - auto-load skills
model: sonnet                    # Optional - sonnet/opus/haiku/inherit
---

Instructions for the agent (not role assignment).
```

### Configuration Fields

| Field | Required | Description |
|-------|----------|-------------|
| `name` | Yes | Unique identifier (lowercase, hyphens) |
| `description` | Yes | When to invoke (used for auto-delegation) |
| `skills` | No | Comma-separated skill names to auto-load |
| `model` | No | `sonnet`, `opus`, `haiku`, or `inherit` |
| `tools` | No | Omit for full access, or restrict with comma-separated list |
| `permissionMode` | No | `default`, `acceptEdits`, `bypassPermissions`, `plan`, `ignore` |

### Key Points
- **No role assignment needed**: Prompt is just instructions, not "You are a..."
- **Skills loading**: Use `skills:` field to inject expertise
- **Full tool access by default**: Omit `tools` field to inherit all
- **Parallel execution**: Multiple agents can run simultaneously
- **Resumable**: Can continue from previous execution via agent ID

---

## Skills vs Subagents

| Aspect | Skills | Subagents |
|--------|--------|-----------|
| Context | Shares main conversation | Fresh, isolated context |
| Invocation | Auto-loaded by description | Delegated via Task tool |
| Output | Continues in conversation | Returns final report |
| State | Stateless | Stateful within execution |
| Composition | Single skill per invocation | Can load multiple skills |
| Parallelism | Sequential | Can run in parallel |

---

## Architecture Pattern

### Recommended Structure

**Skills** = Individual capabilities (flat, one per domain action)
```
.claude/skills/
├── sales-materials-generation/SKILL.md
├── sales-prospect-research/SKILL.md
├── sales-contact-finding/SKILL.md
├── sales-outreach-sequencing/SKILL.md
├── sales-qualification-support/SKILL.md
├── marketing-content-generation/SKILL.md
├── marketing-content-delivery/SKILL.md
└── marketing-channel-optimization/SKILL.md
```

**Subagents** = Orchestrators that load and route to skills
```
.claude/agents/
├── sales-execution.md      # loads sales-* skills
├── marketing-execution.md  # loads marketing-* skills
└── foundations-builder.md  # loads foundations-* skills
```

### Example Orchestrator Agent

```markdown
---
name: sales-execution
description: Orchestrates sales activities (materials, prospecting, contacts, outreach, qualification)
skills: sales-materials-generation, sales-prospect-research, sales-contact-finding, sales-outreach-sequencing, sales-qualification-support
---

Route based on activity_type parameter:

| activity_type | Skill to follow |
|---------------|-----------------|
| materials | sales-materials-generation |
| prospecting | sales-prospect-research |
| contact-finding | sales-contact-finding |
| outreach | sales-outreach-sequencing |
| qualification | sales-qualification-support |

Pass through all context parameters (product, Canvas, ICP) to the skill.
Return skill output to caller.
```

---

## Current Structure (v3.0)

```
.claude/
├── skills/                        # FLAT - one capability per skill (62 total)
│   │
│   │  # Action Skills (11)
│   ├── action-alignment/
│   ├── action-constrain/
│   ├── action-decision/
│   ├── action-descriptive/
│   ├── action-diagnostic/
│   ├── action-evaluative/
│   ├── action-planning/
│   ├── action-prescriptive/
│   ├── action-procedural/
│   ├── action-risk/
│   ├── action-validation/
│   │
│   │  # Engineering Skills (20)
│   ├── engineering-spec-objects/
│   ├── engineering-spec-morphisms/
│   ├── engineering-spec-effects/
│   ├── engineering-spec-constraints/
│   ├── engineering-build-category/
│   ├── engineering-build-effects/
│   ├── engineering-build-functors/
│   ├── engineering-build-transformations/
│   ├── engineering-verify-laws/
│   ├── engineering-verify-constraints/
│   ├── engineering-verify-coverage/
│   ├── engineering-verify-maps/
│   ├── engineering-gen-types/
│   ├── engineering-gen-morphisms/
│   ├── engineering-gen-maps/
│   ├── engineering-gen-code/
│   ├── engineering-gen-wiring/
│   ├── engineering-apply-standards/
│   ├── engineering-foundation-schema/
│   ├── engineering-foundation-targets/
│   │
│   │  # Foundations Skills (10)
│   ├── foundations-market-intelligence/
│   ├── foundations-problem-solution-fit/
│   ├── foundations-value-proposition/
│   ├── foundations-business-model/
│   ├── foundations-validation/
│   ├── foundations-go-to-market/
│   ├── foundations-funding/
│   ├── foundations-regulatory/
│   ├── foundations-retention-optimizer/
│   ├── foundations-icp-generator/
│   │
│   │  # Goal Skills (2)
│   ├── goal-setter/
│   ├── goal-tracker/
│   │
│   │  # Marketing Skills (5)
│   ├── marketing-content-generation/
│   ├── marketing-content-delivery/
│   ├── marketing-channel-optimization/
│   ├── marketing-content-strategy/
│   ├── marketing-narrative/
│   │
│   │  # Reasoning Skills (6)
│   ├── reasoning-causal/
│   ├── reasoning-abductive/
│   ├── reasoning-inductive/
│   ├── reasoning-analogical/
│   ├── reasoning-dialectical/
│   ├── reasoning-counterfactual/
│   │
│   │  # Research Skills (2)
│   ├── research-market-venture/
│   ├── research-market-bootstrap/
│   │
│   │  # Sales Skills (6)
│   ├── sales-materials-generation/
│   ├── sales-prospect-research/
│   ├── sales-contact-finding/
│   ├── sales-outreach-sequencing/
│   ├── sales-qualification-support/
│   └── sales-narrative/
│
└── agents/                        # ORCHESTRATORS (10)
    ├── lean-os.md                 # Main engineering orchestrator
    ├── lean-os-spec.md            # SPEC phase
    ├── lean-os-build.md           # BUILD phase
    ├── lean-os-verify.md          # VERIFY phase
    ├── lean-os-gen.md             # GEN phase
    ├── problem-solving-gateway.md # Action skill routing
    ├── reasoning-gateway.md       # Reasoning mode routing
    ├── foundations-builder.md     # Canvas population
    ├── sales-execution.md         # Sales orchestration
    └── marketing-execution.md     # Marketing orchestration
```

---

## Best Practices

### Skills
1. **One capability per skill** - focused, single purpose
2. **Descriptive names** - `sales-materials-generation` not `materials`
3. **Clear descriptions** - include WHEN to use
4. **References in subfolders** - supporting docs go in `references/`

### Subagents
1. **Instructions, not roles** - "Route based on X" not "You are a router"
2. **Load relevant skills** - use `skills:` field
3. **Full tool access** - omit `tools:` unless restriction needed
4. **Specific descriptions** - helps auto-delegation

### General
1. **Skills for knowledge** - procedures, templates, domain expertise
2. **Agents for orchestration** - routing, parallel work, isolation
3. **Flat skill structure** - no nesting, use prefixes for grouping
4. **Version control both** - `.claude/skills/` and `.claude/agents/` in git

---

## Available Tools

Tools that can be used in `allowed-tools` (skills) or `tools` (agents).

### Built-in Claude Code Tools

| Tool | Description | Permission |
|------|-------------|------------|
| **Read** | Read files (text, images, PDFs, notebooks) | No |
| **Write** | Create or overwrite files | Yes |
| **Edit** | Targeted string replacements in files | Yes |
| **Glob** | Find files by pattern matching | No |
| **Grep** | Search file contents with regex | No |
| **Bash** | Execute shell commands | Yes |
| **BashOutput** | Get output from background shell | No |
| **KillBash** | Kill background shell by ID | No |
| **Task** | Spawn a subagent | No |
| **TodoWrite** | Manage task lists | No |
| **AskUserQuestion** | Ask user multiple choice questions | No |
| **WebFetch** | Fetch and process URL content | Yes |
| **WebSearch** | Search the web | Yes |
| **NotebookEdit** | Modify Jupyter notebook cells | Yes |
| **Skill** | Execute a skill | Yes |
| **SlashCommand** | Run custom slash commands | Yes |
| **ExitPlanMode** | Exit plan mode | Yes |
| **ListMcpResources** | List MCP resources | No |
| **ReadMcpResource** | Read MCP resource | No |

### MCP Tools

Tools from configured MCP servers use the format: `mcp__servername__toolname`

Examples:
- `mcp__github__create_issue`
- `mcp__ide__getDiagnostics`
- `mcp__postgres__query`

### Tool Inheritance

| Context | When Field Omitted |
|---------|-------------------|
| **Skills** (`allowed-tools`) | Asks permission per tool |
| **Agents** (`tools`) | Inherits ALL tools including MCP |

### Restricting Tools

**In Skills:**
```yaml
---
name: read-only-skill
allowed-tools: Read, Grep, Glob
---
```

**In Agents:**
```markdown
---
name: read-only-agent
tools: Read, Grep, Glob
---
```

**For full access:** Omit the field entirely.

---

## Related Documentation

- [All Skills Reference](all-skills.md)
- [Architecture Overview](architecture.md)
- [How It Works](architecture.md)
