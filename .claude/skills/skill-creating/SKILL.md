---
name: skill-creating
description: Creates Claude Code skills with proper SKILL.md format, references, and optional scripts. Use when user asks to create a skill, capability, or knowledge module.
---

# Skill Creation

Skills are modular packages that extend Claude's capabilities with specialized knowledge and workflows. They transform Claude from a general-purpose agent into a specialized one equipped with procedural knowledge.

**Skills are instructions first.** The core is clear, imperative instructions in SKILL.md. Scripts, references, and assets are optional additions.

## Quick Start

Create skill at `.claude/skills/{category}/{skill-name}/SKILL.md`:

```markdown
---
name: skill-name
description: Extracts X, processes Y, generates Z. Use when working with X files or when user mentions Y.
---

# Skill Title

## Quick Start

[Essential instructions with code examples]

## Workflow

1. Step one
2. Step two
3. Step three

## Resources

- See [references/schema.md](references/schema.md) for definitions
```

## Structure

```
skill-name/
├── SKILL.md              # Required: metadata + instructions (<500 lines)
├── references/           # Optional: docs loaded into context as needed
│   └── schema.md
├── assets/               # Optional: files used in output (not loaded)
│   └── template.pptx
└── scripts/              # Optional: only when deterministic code needed
    └── validate.py
```

### Directory Types

| Directory | Purpose | When to Include |
|-----------|---------|-----------------|
| `references/` | Documentation Claude reads while working | Domain knowledge, schemas, policies |
| `assets/` | Templates, images, fonts for output | Boilerplate, brand assets |
| `scripts/` | Deterministic, reusable code | Same code repeated OR reliability critical |

**Most skills need only SKILL.md and possibly references.**

### Locations & Precedence

| Scope | Path | Priority |
|-------|------|----------|
| Enterprise | Managed settings | Highest |
| Personal | `~/.claude/skills/skill-name/` | High |
| Project | `.claude/skills/skill-name/` | Medium |
| Plugin | `skills/skill-name/` in plugin dir | Lowest |

Higher rows override lower rows when names conflict.

## Required Fields

| Field | Constraints |
|-------|-------------|
| `name` | Lowercase, hyphens, numbers. Max 64 chars. Must match directory name. |
| `description` | Third-person singular verbs. Max 1024 chars. Include ALL triggers. |

## Optional Fields

| Field | Purpose | Example |
|-------|---------|---------|
| `allowed-tools` | Restrict tools | `Read, Grep, Glob` |
| `model` | Override model | `claude-sonnet-4-20250514` |
| `context` | Isolated execution | `fork` |
| `agent` | Agent for forked context | `Explore`, `Plan` |
| `hooks` | Lifecycle hooks | `PreToolUse`, `PostToolUse` |
| `user-invocable` | Hide from slash menu | `false` |
| `disable-model-invocation` | Block Skill tool | `true` |

### Visibility Matrix

| Setting | Slash Menu | Skill Tool | Auto-Discovery |
|---------|------------|------------|----------------|
| Default | ✓ | ✓ | ✓ |
| `user-invocable: false` | ✗ | ✓ | ✓ |
| `disable-model-invocation: true` | ✓ | ✗ | ✓ |

## Naming Convention

Use gerund form (verb + -ing), lowercase with hyphens:

```
processing-pdfs
analyzing-spreadsheets
managing-databases
generating-reports
```

## Description Writing

The `description` is the **primary trigger**. Claude reads only name + description to decide skill usage. **Auto-discovery depends on exact format.**

### Required Pattern

```
[Verb ending in 's'] [what it does]. [More details]. [Trigger phrase].
```

### Rule 1: First Word MUST Be Third-Person Singular Verb

The first word must end in 's' (third-person singular present tense).

| ✅ Correct | ❌ Wrong |
|-----------|----------|
| "Extracts..." | "Extract..." |
| "Generates..." | "Generate..." |
| "Validates..." | "Validate..." |
| "Creates..." | "Create..." |
| "Processes..." | "Process..." |
| "Analyzes..." | "Analyze..." |

**Never start with:**
- Base form verbs: "Extract", "Generate", "Validate"
- Noun phrases: "PDF processing.", "Data extraction."
- First person: "I extract...", "We process..."
- Second person: "You can use this to..."

### Rule 2: MUST Include Trigger Phrase

Every description must contain at least one trigger phrase:

| Trigger | Use Case |
|---------|----------|
| `Use when` | General invocation |
| `Use for` | Specific task types |
| `Triggers on` | Keyword-based activation |

### Rule 3: Structure

```
[Third-person verb] [primary capability]. [Secondary capabilities]. Use [when/for] [conditions].
```

### Examples

```yaml
# ✅ CORRECT
description: Extracts text and tables from PDFs, fills forms, merges documents. Use when working with PDF files, forms, or document extraction.

# ✅ CORRECT
description: Creates, edits, and analyzes Word documents with support for tracked changes. Use when working with .docx files.

# ✅ CORRECT
description: Validates API responses against OpenAPI schemas, generates mock data, and documents endpoints. Use when working with REST APIs or OpenAPI specs.

# ❌ WRONG - base form verb
description: Extract text and tables from PDFs.

# ❌ WRONG - noun phrase start
description: PDF processing and extraction. Use when working with PDFs.

# ❌ WRONG - missing trigger
description: Extracts text from PDF files.

# ❌ WRONG - first person
description: I can help you process PDFs.
```

### Description Validation Checklist

- [ ] First word ends in 's' (Extracts, Generates, Validates)
- [ ] NOT base form (Extract, Generate, Validate)
- [ ] NOT noun phrase (PDF processing..., Data extraction...)
- [ ] Contains trigger phrase (Use when, Use for, Triggers on)
- [ ] No first/second person (I, we, you)

## Body Instructions

Use **imperative language** (commands) in the body:

| Location | Verb Form | Example |
|----------|-----------|---------|
| `description` | Third-person singular | "Extracts text, fills forms" |
| Body instructions | Imperative | "Extract text", "Fill the form" |

```markdown
# PDF Processing

## Quick Start

Extract text with pdfplumber:
```python
import pdfplumber
with pdfplumber.open("file.pdf") as pdf:
    text = pdf.pages[0].extract_text()
```

## Form Filling

1. Analyze the form structure first
2. Identify all fillable fields
3. Use pypdf for simple text fields
```

## Progressive Disclosure

Three-level loading system:

1. **Metadata** (~100 words) - Always in context
2. **SKILL.md body** (<500 lines) - When skill triggers
3. **Bundled resources** (unlimited) - As needed by Claude

### Reference Rules

- One level deep only (no A→B→C)
- TOC for files >100 lines
- Under 500 lines each
- No duplication with SKILL.md

### Pattern: High-Level Guide with References

```markdown
## Form Filling

1. Analyze form structure to identify field types
2. For simple text fields, use pypdf
3. For complex forms, see [references/forms.md](references/forms.md)

## Resources
- **Form filling details**: See [references/forms.md](references/forms.md)
- **API reference**: See [references/api.md](references/api.md)
```

## Scripts

**Scripts are optional.** Include only when:
- Same code rewritten repeatedly
- Deterministic reliability critical
- Complex logic error-prone when regenerated

### Script Requirements

```python
# Handle errors explicitly
def process_file(path):
    try:
        with open(path) as f:
            return f.read()
    except FileNotFoundError:
        print(f"File {path} not found, creating default")
        return ''

# Document constants
REQUEST_TIMEOUT = 30  # HTTP requests typically complete within 30s
```

### When to Use Each Approach

| Need | Approach |
|------|----------|
| Simple file checks | Bash one-liners |
| Logic/decisions | Natural language instructions |
| Complex validation | Bundled scripts in `scripts/` |
| Automated checks | Hooks |
| Code examples for Claude | Short inline snippets |

## Configuration Examples

### Allowed Tools

```yaml
---
name: read-only-analysis
description: Analyzes files without modification. Use for safe file inspection.
allowed-tools:
license: Complete terms in LICENSE.txt
  - Read
  - Grep
  - Glob
---
```

### Forked Context

```yaml
---
name: code-analysis
description: Analyzes code quality, generates detailed reports. Use for comprehensive code review.
context: fork
agent: Plan
---
```

### Hooks

```yaml
---
name: secure-operations
description: Performs operations with security validation. Use for sensitive file operations.
hooks:
  PreToolUse:
    - matcher: "Bash"
      hooks:
        - type: command
          command: "./scripts/security-check.sh $TOOL_INPUT"
          once: true
---
```

### Skill Injection into Subagents

Subagents don't inherit skills. Inject via agent's `skills` field:

```yaml
# .claude/agents/code-reviewer.md
---
name: code-reviewer
description: Reviews code for quality and best practices
skills: pr-review, security-check
---
```

## Creation Process

### Step 1: Understand with Examples

Gather concrete usage examples:
- "What functionality should this skill support?"
- "Can you give examples of how it would be used?"
- "What would a user say that should trigger this skill?"

### Step 2: Plan Resources

| Example Query | Analysis | Resource |
|---------------|----------|----------|
| "Edit this Word doc" | Need XML structure knowledge | Instructions in SKILL.md |
| "Review this PR" | Need team standards | `references/standards.md` |
| "Query our sales data" | Need schema each time | `references/schema.md` |
| "Rotate this PDF" | Same code, error-prone | `scripts/rotate.py` |
| "Build me a dashboard" | Same boilerplate | `assets/template/` |

### Step 3: Initialize Directory

```
skill-name/
├── SKILL.md
├── scripts/      # Delete if unused
├── references/   # Delete if unused
└── assets/       # Delete if unused
```

### Step 4: Implement

1. Create all planned resources first
2. Test any scripts by running them
3. Write SKILL.md with proper frontmatter
4. Document every resource in SKILL.md
5. Verify completeness
6. Delete unused directories

**Critical**: Generate resources first, then document them. Don't reference files that don't exist.

### Step 5: Validate

- YAML frontmatter has `name` and `description`
- Description uses third-person singular verbs
- No extraneous files (README, CHANGELOG)
- Scripts tested and working

### Step 6: Iterate

1. Use skill on real tasks
2. Notice struggles or inefficiencies
3. Update SKILL.md or resources
4. Test again

## Skill Patterns

### Workflow Pattern

```markdown
## Document Editing Workflow

1. Unpack the .docx file
2. Locate target content in `word/document.xml`
3. Make edits preserving XML structure
4. Validate changes
5. Repack into .docx
6. Test output opens correctly
```

### Validation Loop Pattern

```markdown
## Editing with Validation

1. Make the edit
2. Check XML is well-formed
3. Verify element nesting
4. If errors: fix and validate again
5. Only proceed when validation passes
```

### Template Pattern

**Low freedom (fragile):**
```markdown
ALWAYS use this exact structure:
```json
{"field": "value", "required": true}
```
```

**High freedom (flexible):**
```markdown
Suggested format, adapt as needed:
# Title
## Summary
```

### Degrees of Freedom

| Freedom | When | Style |
|---------|------|-------|
| High | Multiple valid approaches | Text guidelines |
| Medium | Preferred pattern exists | Templates with parameters |
| Low | Fragile/error-prone | Exact scripts, no modification |

## Directory Organization

```
.claude/skills/
├── engineering/
│   ├── be/           # Backend skills
│   ├── fe/           # Frontend skills
│   ├── design/       # Design system skills
│   └── test/         # Testing skills
├── product/
├── gtm/              # Go-to-market skills
├── customer/         # Customer success skills
├── revops/           # Revenue operations skills
├── foundations/      # Business foundations
├── intelligence/     # Domain expertise
├── critique/         # Review skills
├── reasoning/        # Reasoning modes
├── research/         # Research skills
├── knowledge/        # Knowledge synthesis
├── strategy/         # Goal skills
└── system/           # System utilities
```

## Skills vs Other Options

| Option | What It Is | Triggered By |
|--------|------------|--------------|
| **Skills** | Passive knowledge | Claude loads when relevant |
| **Subagents** | Isolated execution | Claude delegates |
| **Slash commands** | Reusable prompts | User types `/command` |
| **CLAUDE.md** | Project-wide instructions | Every conversation |
| **Hooks** | Scripts on events | Tool events |
| **MCP servers** | External tools/data | Claude invokes |

## What NOT to Include

Skills contain only essential files. **Never create:**
- README.md
- INSTALLATION_GUIDE.md
- QUICK_REFERENCE.md
- CHANGELOG.md
- Any auxiliary documentation

## Anti-Patterns

| Avoid | Do Instead |
|-------|------------|
| Inline Python scripts | Bash, natural language, or bundled scripts |
| Resources not in SKILL.md | Reference every file with usage guidance |
| Mentioning resources without creating them | Generate all planned files |
| Magic constants | Documented values with rationale |
| Verbose explanations | Assume Claude knows basics |
| "When to use" in body | Put in description |
| README, CHANGELOG files | Only essential skill files |
| Duplicating info | SKILL.md OR references, not both |
| Windows paths | Unix paths only |
| Deeply nested references | One level from SKILL.md |
| First/second person in description | Third-person singular |
| Base form in description | Third-person singular |

## Validation Checklist

### Required
- [ ] `name` matches directory name
- [ ] `name` is lowercase, hyphens, numbers only
- [ ] `description` uses third-person singular verbs
- [ ] `description` includes ALL triggers
- [ ] `description` ≤1024 chars

### Structure
- [ ] SKILL.md < 500 lines
- [ ] References one level deep
- [ ] TOC for reference files >100 lines
- [ ] Unix-style paths only
- [ ] No extraneous files

### Resources
- [ ] All planned resources created
- [ ] Every resource documented in SKILL.md
- [ ] No inline Python scripts

### Content
- [ ] Body uses imperative language
- [ ] Concise (no explanations Claude knows)
- [ ] No duplication between SKILL.md and references

### Scripts (if included)
- [ ] Justified (repeated code OR reliability needed)
- [ ] Tested by running
- [ ] Errors handled explicitly
- [ ] Constants documented
