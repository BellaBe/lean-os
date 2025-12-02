---
name: marketing-narrative
description: Generate brand identity and content patterns. Use when: setting up marketing for a product/personal brand, creating content patterns, or updating brand voice. Outputs brand-voice.md, positioning.md, content-pillars.md, and patterns/. Channel-agnostic — works regardless of GTM motion. Requires Canvas files.
allowed-tools: "Read,Write,WebSearch,WebFetch,AskUserQuestion"
---

# Marketing Narrative Generator

Generate brand identity and content patterns that work across any channel or GTM motion.

## Core Principle

This skill answers: **Who are we and how do we sound?**

It does NOT answer:
- Which channels to use (→ `strategy/canvas/15.go-to-market.md`)
- How to optimize channels (→ `channel-optimization`)
- Where to distribute (→ `content-delivery`)
- Loop mechanics (→ `content-generation`)

## Input Requirements

**Required (Canvas):**
- `strategy/canvas/04.segments.md`
- `strategy/canvas/05.problem.md`
- `strategy/canvas/07.uvp.md`
- `strategy/canvas/08.advantage.md`
- `strategy/canvas/09.solution.md`

**Optional (enhances output):**
- `artifacts/sales/{segment}/narratives/*.md`
- Existing content examples (for voice extraction)

If Canvas files missing → Stop, flag which files needed

## Output Structure

```
artifacts/marketing/narrative/
├── brand-voice.md
├── positioning.md
├── content-pillars.md
└── patterns/
    ├── insight.md
    ├── tutorial.md
    ├── case-study.md
    ├── story.md
    └── {user-requested}.md
```

## Generation Modes

### Mode 1: Full Identity Generation

**Trigger:** First-time setup or major positioning change

**Process:**
1. Extract positioning from Canvas
2. Generate positioning.md (what we stand for)
3. Generate brand-voice.md (how we sound)
4. Generate content-pillars.md (what we talk about)
5. Generate default patterns (case-study, insight, tutorial, story)

See references:
- `references/brand-voice-template.md`
- `references/positioning-template.md`
- `references/content-pillars-template.md`
- `references/content-patterns.md`

### Mode 2: Pattern Creation

**Trigger:** User requests new content type

**Input:**

| Parameter | Required | Description |
|-----------|----------|-------------|
| `content_type` | Yes | Name for the pattern |
| `examples` | Recommended | 2-3 examples of good content |
| `purpose` | Yes | What this content achieves |

**Output:** `artifacts/marketing/narrative/patterns/{content_type}.md`

### Mode 3: Voice Refinement

**Trigger:** Voice drift, new positioning, user feedback

**Process:**
1. Read existing brand-voice.md
2. Analyze recent content (what's working)
3. Update voice guidelines
4. Flag patterns that need updating

## Validation

Before completing:

- [ ] Positioning extracted from Canvas (not invented)
- [ ] Voice is specific (not generic "professional and friendly")
- [ ] Pillars connect to UVP and segments
- [ ] Patterns are channel-agnostic (can adapt to any channel)

## Relationship to Other Skills

| Skill | Relationship |
|-------|--------------|
| `go-to-market` | Declares channels; narrative doesn't read it |
| `channel-optimization` | Reads narrative, applies to channel formats |
| `content-generation` | Reads narrative, applies voice/patterns to drafts |
| `content-strategy` | Reads pillars for opportunity alignment |
| `content-delivery` | Doesn't read narrative (channel routing only) |
