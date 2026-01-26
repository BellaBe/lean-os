---
name: agent-creating
description: Creates Claude Code subagents with proper YAML frontmatter, system prompts, and tool configuration. Use when user asks to create an agent, subagent, or orchestrator.
---

# Agent Creation

Subagents are specialized AI assistants that Claude Code delegates tasks to. Each has its own context window, specific tools, and custom system prompt.

## Quick Start

Create agent file at `.claude/agents/{agent-name}.md`:

```markdown
---
name: agent-name
description: Description of when this agent should be invoked. Use proactively when...
tools: Read, Write, Edit, Bash, Glob, Grep
model: inherit
skills: skill1, skill2
---

You are a [role description].

## When Invoked

1. First action
2. Second action
3. Third action

## Workflow

[Detailed workflow instructions]

## Constraints

- Constraint 1
- Constraint 2
```

## File Locations

| Type | Location | Scope | Priority |
|------|----------|-------|----------|
| **Project** | `.claude/agents/` | Current project | Highest |
| **User** | `~/.claude/agents/` | All projects | Lower |
| **CLI** | `--agents '{...}'` | Session only | Middle |

Project-level agents take precedence when names conflict.

## Configuration Fields

### Required

| Field | Constraints |
|-------|-------------|
| `name` | Lowercase, hyphens only. Must match filename without `.md` |
| `description` | Clear purpose + trigger phrases. Include "Use proactively" or "MUST BE USED" for auto-invocation |

### Optional

| Field | Purpose | Values |
|-------|---------|--------|
| `tools` | Restrict available tools | Comma-separated list (inherits all if omitted) |
| `model` | Model selection | `sonnet`, `opus`, `haiku`, `inherit` |
| `skills` | Auto-load skills | Comma-separated skill names |
| `permissionMode` | Permission handling | `default`, `acceptEdits`, `dontAsk`, `bypassPermissions`, `plan`, `ignore` |

### Model Selection

- **Model alias**: `sonnet`, `opus`, `haiku`
- **`inherit`**: Use same model as main conversation
- **Omitted**: Defaults to `sonnet`

## Available Tools

**Core tools:**
`Read`, `Write`, `Edit`, `Bash`, `Glob`, `Grep`, `WebFetch`, `WebSearch`, `Task`, `TodoWrite`, `NotebookEdit`

**MCP tools:** Inherited from main thread if `tools` field omitted.

## Description Writing

The `description` field determines when Claude delegates to the agent. **Auto-discovery depends on exact format.**

### Required Pattern

```
[Verb ending in 's'] [what it does]. [More details]. [Trigger phrase].
```

### Rule 1: First Word MUST Be Third-Person Singular Verb

The first word must end in 's' (third-person singular present tense).

| ✅ Correct | ❌ Wrong |
|-----------|----------|
| "Generates..." | "Generate..." |
| "Creates..." | "Create..." |
| "Orchestrates..." | "Orchestrate..." |
| "Transforms..." | "Transform..." |
| "Designs..." | "Design..." |
| "Executes..." | "Execute..." |
| "Analyzes..." | "Analyze..." |

**Never start with:**
- Base form verbs: "Generate", "Create", "Apply"
- Noun phrases: "Market entry and validation.", "Fundraising strategy."
- First person: "I generate...", "We create..."
- Second person: "You can use this to..."

### Rule 2: MUST Include Trigger Phrase

Every description must contain at least one trigger phrase:

| Trigger | Use Case |
|---------|----------|
| `Use when` | General invocation |
| `Use for` | Specific task types |
| `Use proactively` | Auto-invoke after related actions |
| `MUST BE USED` | Mandatory for specific keywords |
| `Triggers on` | Keyword-based activation |

### Rule 3: Structure

```
[Third-person verb] [primary capability]. [Secondary capabilities]. Use [when/for] [conditions].
```

### Examples

```yaml
# ✅ CORRECT
description: Generates complete design systems from requirements. Produces React + Tailwind implementation. Use when creating design systems or component libraries. MUST BE USED when user mentions "design system".

# ✅ CORRECT
description: Orchestrates product design from Canvas to engineering handoff. Use when translating strategy into specs, creating stories, designing flows, or preparing features for engineering.

# ✅ CORRECT
description: Transforms requirements into IntentIR v0.1. Orchestrates 4 extraction phases. Use when processing natural language requirements into structured intent artifacts.

# ❌ WRONG - base form verb
description: Transform requirements into IntentIR v0.1.

# ❌ WRONG - noun phrase start
description: Market entry and validation. Use for assumption testing.

# ❌ WRONG - missing trigger
description: Generates code from specifications.

# ❌ WRONG - first person
description: I help you generate design systems.
```

### Validation Checklist

Before saving, verify:

- [ ] First word ends in 's' (Generates, Creates, Orchestrates)
- [ ] NOT base form (Generate, Create, Orchestrate)
- [ ] NOT noun phrase (Market entry..., Fundraising strategy...)
- [ ] Contains trigger phrase (Use when, Use for, MUST BE USED, Triggers on)
- [ ] No first/second person (I, we, you)

## System Prompt Guidelines

1. **Define role clearly** - "You are a senior [role]..."
2. **State immediate actions** - "When invoked: 1. Check state, 2. Execute..."
3. **Include workflow** - Step-by-step process
4. **Add constraints** - Non-negotiables
5. **Handle errors** - What to do when things fail

## Agent Patterns

### Orchestrator Pattern

Routes to skills based on task type:

```markdown
---
name: domain-orchestrator
description: Orchestrates [domain] workflows. Use when working on [domain] tasks.
tools: Read, Write, Edit, Bash, Glob, Grep
skills: domain-skill-1, domain-skill-2, domain-skill-3
---

You are a [domain] orchestrator.

## Routing

| Task Type | Skill | Output |
|-----------|-------|--------|
| type-a | `domain-skill-1` | `artifacts/domain/a/` |
| type-b | `domain-skill-2` | `artifacts/domain/b/` |

## Workflow

1. Identify task type
2. Load appropriate skill
3. Execute with skill guidance
4. Validate output
```

### Pipeline Pattern

Sequential phase execution:

```markdown
---
name: pipeline-agent
description: Executes [pipeline] phases sequentially. Use for [trigger].
skills: phase-1, phase-2, phase-3, verification
---

## Pipeline

PHASE-1 → PHASE-2 → PHASE-3
   │         │         │
 verify    verify    verify

## Phase Execution

For EACH phase:
1. Load phase skill
2. Execute transformation
3. Run verification
4. Gate: PASS → next, FAIL → stop
```

### Specialist Pattern

Deep expertise in single domain:

```markdown
---
name: specialist-agent
description: Expert [domain] specialist. Use proactively for [triggers].
tools: Read, Write, Edit, Bash
---

You are a senior [domain] expert.

## Standards

- Standard 1
- Standard 2

## Anti-Patterns

- Anti-pattern 1
- Anti-pattern 2
```

## Built-in Agents

### general-purpose
- **Model:** Sonnet
- **Tools:** All tools
- **Mode:** Read/write, can modify files
- **Use:** Complex multi-step tasks, code modifications

### Explore
- **Model:** Haiku (fast)
- **Tools:** Glob, Grep, Read, Bash (read-only)
- **Mode:** Strictly read-only
- **Use:** Codebase search and analysis
- **Thoroughness:** quick, medium, very thorough

### Plan
- **Model:** Sonnet
- **Tools:** Read, Glob, Grep, Bash
- **Use:** Research during plan mode

## Example Agents

### Code Reviewer

```markdown
---
name: code-reviewer
description: Expert code review specialist. Proactively reviews code for quality, security, and maintainability. Use immediately after writing or modifying code.
tools: Read, Grep, Glob, Bash
model: inherit
---

You are a senior code reviewer ensuring high standards of code quality and security.

When invoked:
1. Run git diff to see recent changes
2. Focus on modified files
3. Begin review immediately

Review checklist:
- Code is clear and readable
- Functions and variables are well-named
- No duplicated code
- Proper error handling
- No exposed secrets or API keys
- Input validation implemented
- Good test coverage
- Performance considerations addressed

Provide feedback organized by priority:
- Critical issues (must fix)
- Warnings (should fix)
- Suggestions (consider improving)

Include specific examples of how to fix issues.
```

### Debugger

```markdown
---
name: debugger
description: Debugging specialist for errors, test failures, and unexpected behavior. Use proactively when encountering any issues.
tools: Read, Edit, Bash, Grep, Glob
---

You are an expert debugger specializing in root cause analysis.

When invoked:
1. Capture error message and stack trace
2. Identify reproduction steps
3. Isolate the failure location
4. Implement minimal fix
5. Verify solution works

Debugging process:
- Analyze error messages and logs
- Check recent code changes
- Form and test hypotheses
- Add strategic debug logging
- Inspect variable states

For each issue, provide:
- Root cause explanation
- Evidence supporting the diagnosis
- Specific code fix
- Testing approach
- Prevention recommendations

Focus on fixing the underlying issue, not the symptoms.
```

## CLI Configuration

Define agents dynamically with `--agents` flag:

```bash
claude --agents '{
  "code-reviewer": {
    "description": "Expert code reviewer. Use proactively after code changes.",
    "prompt": "You are a senior code reviewer. Focus on code quality, security, and best practices.",
    "tools": ["Read", "Grep", "Glob", "Bash"],
    "model": "sonnet"
  }
}'
```

## Advanced Usage

### Chaining Agents

```
> First use the code-analyzer agent to find performance issues,
  then use the optimizer agent to fix them
```

### Resumable Agents

Agents can be resumed with their `agentId`:

```
> Resume agent abc123 and now analyze the authorization logic
```

Use cases:
- Long-running research across sessions
- Iterative refinement without losing context
- Multi-step workflows with maintained state

### Explicit Invocation

```
> Use the test-runner agent to fix failing tests
> Have the code-reviewer agent look at my recent changes
```

## Best Practices

1. **Generate with Claude first** - Use `/agents` to generate, then customize
2. **Single responsibility** - Focused agents perform better
3. **Detailed prompts** - More guidance = better performance
4. **Limit tools** - Only grant necessary tools
5. **Version control** - Check project agents into git

## Validation Checklist

- [ ] `name` matches filename (e.g., `my-agent.md` → `name: my-agent`)
- [ ] `description` has clear triggers
- [ ] `tools` limited to necessary tools
- [ ] `skills` lists all required skills
- [ ] System prompt defines clear role
- [ ] Workflow steps are actionable
- [ ] Error handling included
