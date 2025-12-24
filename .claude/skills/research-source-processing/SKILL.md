---
name: research-source-processing
description: Process expert sources (videos, podcasts, articles, books) into structured insights. Use when ingesting new knowledge sources for extraction and analysis.
---

# Research Source Processing

Transform raw expert content into structured, actionable insights.

## Type Signature

```
SourceProcessing : RawSource × SourceType × Context → StructuredInsights

Where:
  RawSource         : URL | File | Transcript
  SourceType        : video | podcast | article | book | talk
  Context           : Domain × Purpose × Audience
  StructuredInsights: Metadata × KeyInsights × Patterns × Quotes × ActionItems
```

## When to Use

- Ingesting expert content (podcasts, talks, articles, books)
- Building knowledge base from authoritative sources
- Extracting actionable frameworks from expert material
- Client research sprint (processing their chosen sources)

## Input Requirements

| Field | Required | Description |
|-------|----------|-------------|
| source | Yes | URL, file path, or raw transcript |
| source_type | Yes | video, podcast, article, book, talk |
| author | Yes | Expert/author name |
| domain | Yes | Topic domain (e.g., "network effects", "pricing") |
| context | No | Additional context for extraction focus |

## Process

### Stage 1: Source Ingestion

**For video/podcast:**
```
1. Extract transcript (if URL, fetch; if file, read)
2. Identify speaker(s) and structure (interview, talk, panel)
3. Note timestamps for key sections
4. Capture metadata (date, duration, platform)
```

**For article/book:**
```
1. Extract full text
2. Identify structure (chapters, sections, headings)
3. Note key definitions and frameworks
4. Capture metadata (publication date, author bio)
```

### Stage 2: Insight Extraction

Extract insights using this schema:

```yaml
insight:
  id: I{N}
  title: "Short descriptive title"
  category: [framework | principle | tactic | warning | metric | quote]
  content: "2-3 sentence insight"
  evidence: "Supporting quote or data from source"
  actionable: true | false
  confidence: high | medium | low
  related_to: [other insight IDs]
```

**Extraction priorities:**
1. **Frameworks** - Mental models, decision structures
2. **Principles** - Universal truths, rules
3. **Tactics** - Specific actions, playbooks
4. **Warnings** - Anti-patterns, mistakes to avoid
5. **Metrics** - Numbers, benchmarks, thresholds
6. **Quotes** - Memorable statements worth preserving

### Stage 3: Pattern Identification

Within the source, identify:

```yaml
patterns:
  recurring_themes: ["theme 1", "theme 2"]
  key_frameworks: ["framework name → brief description"]
  contrarian_views: ["what goes against conventional wisdom"]
  tensions: ["seemingly contradictory ideas to reconcile"]
```

### Stage 4: Actionability Assessment

For each insight, determine:

```yaml
actionability:
  insight_id: I{N}
  immediate_action: "What can be done today"
  requires: ["prerequisite 1", "prerequisite 2"]
  applies_to: ["context where this applies"]
  does_not_apply: ["context where this fails"]
```

## Output Structure

Create two files in `research/sources/{source-slug}/`:

### 1. raw.md (Reference)

```markdown
# {Source Title}

**Author:** {Name}
**Type:** {video | podcast | article | book}
**Date:** {YYYY-MM-DD}
**URL:** {if applicable}
**Duration/Length:** {if applicable}

## Summary
{1-2 paragraph overview}

## Transcript/Content
{Full or key excerpts}

## Timestamps (if video/podcast)
- 00:00 - Introduction
- 05:30 - Key Topic 1
- ...
```

### 2. insights.md (Extracted Value)

```markdown
# Insights: {Source Title}

**Source:** {Author} - {Source Type}
**Domain:** {Topic domain}
**Processed:** {YYYY-MM-DD}
**Insight Count:** {N}

---

## Key Frameworks

### {Framework Name}
**Insight:** {Description}
**Application:** {How to use it}
**Evidence:** "{Quote from source}"

---

## Core Principles

### I1: {Principle Title}
**Category:** principle
**Insight:** {2-3 sentences}
**Evidence:** "{Quote}"
**Actionable:** Yes/No
**Action:** {If yes, what to do}

### I2: {Principle Title}
...

---

## Tactics & Playbooks

### I{N}: {Tactic Title}
**Category:** tactic
**Insight:** {Description}
**Steps:**
1. {Step 1}
2. {Step 2}
3. {Step 3}
**Evidence:** "{Quote}"

---

## Warnings & Anti-Patterns

### I{N}: {Warning Title}
**Category:** warning
**Insight:** {What to avoid}
**Why:** {Consequence}
**Instead:** {What to do instead}

---

## Key Metrics & Benchmarks

| Metric | Value | Context |
|--------|-------|---------|
| {metric} | {value} | {when this applies} |

---

## Memorable Quotes

> "{Quote 1}"

> "{Quote 2}"

---

## Patterns Detected

**Recurring Themes:**
- {Theme 1}
- {Theme 2}

**Contrarian Views:**
- {What challenges conventional wisdom}

**Tensions to Reconcile:**
- {Seeming contradiction}

---

## Cross-References

**Related Sources:** {Other sources in knowledge base}
**Related Playbooks:** {Existing playbooks this connects to}

---

## Tags

`{tag1}` `{tag2}` `{tag3}`
```

## Quality Checklist

```
[ ] Source metadata complete (author, date, type)
[ ] At least 5 insights extracted
[ ] Each insight has evidence (quote/data)
[ ] Frameworks identified and named
[ ] Actionable items have clear steps
[ ] Patterns section completed
[ ] Tags added for discoverability
```

## Integration

### With research-playbook-generation
- Output insights.md feeds playbook generation
- Frameworks become playbook sections
- Tactics become playbook steps

### With reasoning-inductive (via knowledge-builder)
- Multiple insights.md files feed synthesis
- Patterns aggregate across sources
- Contradictions surface for resolution

### With Index
- Update `research/index.md` with new source
- Add to relevant domain sections
- Link to generated playbooks

## Example

**Input:**
```yaml
source: "https://youtube.com/watch?v=..."
source_type: video
author: "Andrew Chen"
domain: "network effects"
context: "Building marketplace startups"
```

**Output:**
```
research/sources/andrew-chen-network-effects/
├── raw.md         # Transcript + metadata
└── insights.md    # 15 insights extracted
    ├── Frameworks: Cold start theory, Atomic networks
    ├── Principles: Density before scale, Hard side first
    ├── Tactics: Flintstoning, Invite-only launch
    ├── Warnings: Scaling too early, Wrong side focus
    └── Metrics: 15% threshold, Network density targets
```

## Constraints

- **Preserve author voice** - Don't paraphrase into generic language
- **Cite evidence** - Every insight needs supporting quote/data
- **Acknowledge uncertainty** - Mark low-confidence insights
- **Note context** - Insights may not apply universally
- **Avoid interpretation** - Extract what's said, not what you think
