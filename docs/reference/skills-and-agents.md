# Skills and Agents Architecture

Reference documentation for Claude Code skills and subagents in LeanOS Core.

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

### LeanOS Core Structure

**Skills** = Individual capabilities (flat, one per domain action)
```
.claude/skills/
├── reasoning-causal/SKILL.md
├── reasoning-abductive/SKILL.md
├── reasoning-inductive/SKILL.md
├── reasoning-analogical/SKILL.md
├── reasoning-dialectical/SKILL.md
├── reasoning-counterfactual/SKILL.md
├── action-descriptive/SKILL.md
├── action-diagnostic/SKILL.md
├── action-prescriptive/SKILL.md
├── action-planning/SKILL.md
├── action-decision/SKILL.md
├── goal-setter/SKILL.md
├── goal-tracker/SKILL.md
├── foundations-market-intelligence/SKILL.md
└── foundations-problem-solution-fit/SKILL.md
```

**Subagents** = Orchestrators that load and route to skills
```
.claude/agents/
├── reasoning-gateway.md      # routes to reasoning-* skills
└── problem-solving-gateway.md # routes to action-* skills
```

### Example Orchestrator Agent

```markdown
---
name: reasoning-gateway
description: Route to appropriate reasoning mode based on task context
skills: reasoning-causal, reasoning-abductive, reasoning-inductive, reasoning-analogical, reasoning-dialectical, reasoning-counterfactual
---

Route based on context:

| Context | Reasoning Mode |
|---------|----------------|
| Operational execution | reasoning-causal |
| Anomaly diagnosis | reasoning-abductive |
| Pattern detection | reasoning-inductive |
| Novel situation | reasoning-analogical |
| Stakeholder conflict | reasoning-dialectical |
| Decision evaluation | reasoning-counterfactual |

Select mode, pass context, return structured output.
```

---

## Best Practices

### Skills
1. **One capability per skill** - focused, single purpose
2. **Descriptive names** - `reasoning-causal` not `causal`
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
| **Task** | Spawn a subagent | No |
| **TodoWrite** | Manage task lists | No |
| **AskUserQuestion** | Ask user multiple choice questions | No |
| **WebFetch** | Fetch and process URL content | Yes |
| **WebSearch** | Search the web | Yes |

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

- [Skills Reference](skills-index.md)
- [Architecture Overview](architecture.md)
