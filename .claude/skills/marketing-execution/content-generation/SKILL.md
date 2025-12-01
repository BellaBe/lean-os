---
name: content-generation
description: Generate loop-triggering content drafts with brand intelligence. Use when: creating blog posts, case studies, social posts from source material. Requires distribution-model.md, brand-voice.md, positioning.md, and content patterns. Every piece must include loop trigger and velocity framing.
allowed-tools: "Read,Write,Bash"
---

# Content Generation

Generate content designed to loop — every piece generates its own next input.

## Core Principles

> "Loops are so much better than funnels."
> "Velocity of shipping can become your moat."

Every draft must:
1. Include loop trigger (how it generates response)
2. Include velocity framing (before → after with time compression)
3. Connect to larger content ecosystem (no orphans)

## Prerequisites

**Required context (from marketing-narrative):**

| File | Purpose | If Missing |
|------|---------|------------|
| `artifacts/marketing/narrative/distribution-model.md` | Loop mechanics, velocity framing | Cannot proceed |
| `artifacts/marketing/narrative/brand-voice.md` | How we sound | Cannot proceed |
| `artifacts/marketing/narrative/positioning.md` | What we stand for | Cannot proceed |
| `artifacts/marketing/narrative/patterns/{type}.md` | Structure for content type | Flag, request creation |

If required files missing → Flag "Run marketing-narrative to generate context"

## Input

| Parameter | Required | Description |
|-----------|----------|-------------|
| `content_type` | Yes | Matches pattern filename |
| `source_paths` | Yes | Paths to source material |
| `loop_trigger_type` | Recommended | implementation / question / challenge / offer |
| `velocity_proof` | Recommended | Before → After data |
| `output_path` | Yes | Where to save draft |

## Process

### 1. Validate Context Exists
```bash
artifacts/marketing/narrative/distribution-model.md   # Must exist
artifacts/marketing/narrative/brand-voice.md          # Must exist
artifacts/marketing/narrative/positioning.md          # Must exist
artifacts/marketing/narrative/patterns/{content_type}.md  # Should exist
```

### 2. Load Intelligence

**Distribution model** — Extract:
- Loop mechanics for this content type
- Velocity framing requirements
- Channel-specific adaptations

**Brand voice** — Extract:
- Tone principles
- Language patterns
- Anti-patterns (engagement bait, CTAs)

**Positioning** — Extract:
- Core problem we solve
- Unique approach
- Differentiators

**Pattern** — Extract:
- Structure for this content type
- Loop trigger format
- Length guidelines

### 3. Load Source Material

Read all `source_paths`:
- Extract facts, metrics, quotes
- Identify velocity proof (before → after)
- Note user stories (loop fuel)
- Flag gaps for human review

### 4. Generate Draft

**Layer intelligence:**
```
Loop trigger requirement
    ↓ shapes ending
Velocity framing
    ↓ shapes proof
Pattern structure
    ↓ shapes flow
Brand voice
    ↓ colors tone
Source material
    ↓ fills content
Draft
```

**Generation rules:**
- Every draft ends with loop trigger
- Velocity proof in first half (before → after with time)
- All claims traced to source material
- Voice consistent with brand-voice.md
- No engagement bait (see anti-patterns in brand-voice.md)
- No orphan content (connects to ecosystem)

### 5. Validate
```bash
python {baseDir}/scripts/validate_draft.py \
  --draft {output_path} \
  --type {content_type} \
  --check-loop-trigger \
  --check-velocity
```

### 6. Output
```markdown
---
content_type: "{type}"
source_paths: ["{paths}"]
loop_trigger_type: "{type}"
velocity_proof: "{before} → {after}"
created: "{date}"
status: "draft"
---

# {Title}

{Content with velocity proof in first half}

---

{Loop trigger — question, challenge, offer, or implementation ask}

---

## Review Notes

**Loop check:**
- [ ] Clear loop trigger at end
- [ ] Velocity framing present

**Voice check:**
- [ ] Tone matches brand voice
- [ ] No engagement bait

**Accuracy check:**
- [ ] All metrics sourced
- [ ] {Specific items to verify}
```

## Loop Trigger Types

| Type | When to Use | Example |
|------|-------------|---------|
| Implementation | Tutorials, frameworks | "Try this and share your result" |
| Question | Insights, observations | "What's your version of this?" |
| Challenge | Methods, templates | "Rewrite yours using this. Tag me." |
| Offer | Problem posts | "Facing this? DM your situation" |

**Default:** If no type specified, use Question for thought leadership, Implementation for how-to.

## Velocity Framing Requirements

Every piece must include before → after with time compression:
```
{Time period} to {old way}.
{Shorter time} to {new way}.
```

Examples:
- "Three weeks to build. Twenty minutes to realize it was wrong."
- "Days of writing. Minutes of review."
- "Weeks to create the problem. Minutes to fix it."

**If no velocity data in source material:** Flag for human to provide, or frame as transformation without time.

## Edge Cases

| Situation | Action |
|-----------|--------|
| No velocity proof available | Frame as transformation, flag for human |
| No obvious loop trigger | Use Question type, flag for review |
| Source material thin | Flag gaps, request more input |
| Multiple loop opportunities | Pick strongest, note alternatives |

## Boundaries

**DO:**
- Load and apply distribution intelligence
- Include loop trigger in every draft
- Include velocity framing
- Validate against brand standards
- Flag gaps and uncertainties

**DON'T:**
- Proceed without distribution context
- Create content without loop trigger
- Skip velocity framing
- Use engagement bait tactics
- Create orphan content