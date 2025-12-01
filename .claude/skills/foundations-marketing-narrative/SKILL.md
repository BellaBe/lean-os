---
name: marketing-narrative
description: Generate content strategy, distribution model, and patterns for brand-aligned content. Use when: setting up marketing for a product/personal brand, creating content patterns, updating brand voice, or defining distribution loops. Outputs brand-voice.md, positioning.md, distribution-model.md, content-pillars.md, channel-guidelines.md, and patterns/. Requires Canvas files.
allowed-tools: "Read,Write,WebSearch,WebFetch,AskUserQuestion"
---

# Marketing Narrative Generator

Generate content strategy and distribution model that builds authority through loops, not funnels.

## Core Principle

> "Great product is not enough. Distribution wins."

Distribution is baked into everything. Not marketing's job — everyone's job.

## Input Requirements

**Required (Canvas):**
- `strategy/canvas/04-segments.md`
- `strategy/canvas/05-problem.md`
- `strategy/canvas/07-uvp.md`
- `strategy/canvas/08-advantage.md`
- `strategy/canvas/09-solution.md`

**Optional (enhances output):**
- `artifacts/sales/{segment}/narratives/*.md`
- Product/service usage data (for loop design)

If Canvas files missing → Stop, flag which files needed

## Output Structure
```
artifacts/marketing/narrative/
├── brand-voice.md           # How we sound
├── positioning.md           # What we stand for
├── distribution-model.md    # How growth actually works (loops, channels)
├── content-pillars.md       # Strategic themes
├── channel-guidelines.md    # Format specs (distribution-aware)
└── patterns/
    ├── loop-content.md      # Content designed to loop
    ├── blog.md
    ├── case-study.md
    ├── linkedin.md
    └── {user-requested}.md
```

## Generation Modes

### Mode 1: Full Strategy Generation

**Trigger:** First-time setup or major positioning change

**Process:**
1. Extract positioning from Canvas
2. Generate distribution-model.md (loops, channels, velocity)
3. Generate brand-voice.md, positioning.md
4. Generate content-pillars.md (loop-aware)
5. Generate channel-guidelines.md (distribution physics applied)
6. Generate default patterns (loop-content, blog, case-study, linkedin)

See 
- `references/distribution-model-template.md` for distribution model structure.
- `references/brand-voice-template.md` for brand voice structure.
- `references/positioning-template.md` for positioning structure.
- `references/channel-guidelines-template.md` for channel guidelines structure.
- `references/content-pillars-template.md` for content pillars structure.
- `references/loop-content-pattern.md` for loop content pattern details.


### Mode 2: Pattern Creation

**Trigger:** content-generation requests pattern, or user wants new content type

**Input:**
| Parameter | Required | Description |
|-----------|----------|-------------|
| `content_type` | Yes | Name for the pattern |
| `examples` | Recommended | 2-3 examples of good content |
| `purpose` | Yes | What this content achieves |
| `loop_mechanic` | Recommended | How this content generates next input |

**Output:** `artifacts/marketing/narrative/patterns/{content_type}.md`

### Mode 3: Distribution Model Update

**Trigger:** Market shift, channel performance data, loop metrics

**Process:**
1. Read existing distribution-model.md
2. Integrate new learnings (what's working, what's dying)
3. Update channel priorities
4. Update loop mechanics based on data

## Distribution Model Framework

See `references/distribution-model-template.md` for full template.

**Core components:**

| Component | Purpose |
|-----------|---------|
| Distribution physics | What's dying, what's working |
| Loop design | How each interaction generates the next |
| Growth model | Stage-by-stage with loop triggers |
| Velocity positioning | Before → After time compression |
| Defensibility | Complexity as moat |
| Channel strategy | Investment priorities based on reality |
| Content triggers | When to publish (learning-driven, not calendar) |

## Pattern Requirements

**All patterns must include:**

1. **Loop trigger** — How this content generates response/implementation
2. **Velocity framing** — Before → After with time compression
3. **Connection point** — How this feeds other content

**No orphan content.** Every piece connects to the loop.

## Validation

Before completing:

- [ ] distribution-model.md defines loops, not funnels
- [ ] Channel strategy reflects current reality (SEO dying, founder socials rising)
- [ ] All patterns include loop triggers
- [ ] Velocity framing present in positioning
- [ ] Content triggers are learning-driven, not calendar-driven
- [ ] No engagement bait tactics

## Applicability

| Business Type | Loop Focus | Key Adaptation |
|---------------|------------|----------------|
| SaaS Product | Users share outputs, invite others | Build sharing into product |
| Personal Brand | Followers implement, share results | Teach methods worth sharing |
| Service Business | Clients become case studies | Results → content → more clients |
| E-commerce | Customers share purchases/results | UGC, reviews, community |