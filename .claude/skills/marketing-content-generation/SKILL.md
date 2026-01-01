---
name: marketing-content-generation
description: Generate content drafts adapted to GTM motion. Use when creating blog posts, case studies, social posts, sales collateral, or app store copy. Requires brand-voice.md and positioning.md.
allowed-tools: "Read,Write,Bash"
---

# Content Generation

Generate content that serves your GTM motion.

## Core Principle

Content serves strategy. Different modes need different content. Mode is determined by orchestrator.

## Prerequisites

**Required:**

| File | Purpose | If Missing |
|------|---------|------------|
| `strategy/canvas/15.gtm.md` | Motion, channels | Cannot proceed |
| `artifacts/marketing/narrative/brand-voice.md` | How we sound | Cannot proceed |
| `artifacts/marketing/narrative/positioning.md` | What we stand for | Cannot proceed |

**Recommended:**

| File | Purpose | If Missing |
|------|---------|------------|
| `artifacts/marketing/narrative/patterns/{type}.md` | Structure | Use defaults |
| `artifacts/marketing/narrative/content-pillars.md` | Topics | Proceed with caution |

## Input

| Parameter | Required | Description |
|-----------|----------|-------------|
| `content_type` | Yes | Type of content |
| `source_paths` | Yes | Source material |
| `output_path` | Yes | Where to save |
| `mode` | Yes | From orchestrator: `loop-driven`, `marketplace-driven`, or `sales-driven` |

**Mode is required.** This skill does not detect motion  -  it receives mode from `marketing-execution` orchestrator.

**Mode-specific parameters:**

| Mode | Additional |
|------|------------|
| loop-driven | `loop_trigger_type`, `velocity_proof` |
| marketplace-driven | `platform`, `keywords` |
| sales-driven | `target_persona`, `sales_stage` |

## Process

### 1. Validate Mode

Mode passed from marketing-execution. If missing → Stop, flag "Invoke via marketing-execution orchestrator"

```python
if not mode:
    raise Error("Mode required. Invoke via marketing-execution.")
    
valid_modes = ["loop-driven", "marketplace-driven", "sales-driven", "hybrid"]
if mode not in valid_modes:
    raise Error(f"Invalid mode: {mode}")
```

### 2. Load Context

```
brand-voice.md      → Tone, language
positioning.md      → What we stand for
patterns/{type}.md  → Structure
```

### 3. Load Source Material

- Extract facts, metrics, quotes
- Identify transformation stories
- Note gaps for human review

### 4. Generate Draft

Apply mode-specific rules (see below).

### 5. Validate

Mode-appropriate validation.

### 6. Output

Save with mode-appropriate frontmatter.

---

## Mode: Loop-Driven (PLG, Content-Led)

**Every draft must include:**
1. Loop trigger (generates response)
2. Velocity framing (before → after)
3. Connection to ecosystem

See `references/loop-mechanics.md` for details.

### Loop Trigger Types

| Type | When | Example |
|------|------|---------|
| Implementation | Tutorials | "Try this and share your result" |
| Question | Insights | "What's your version?" |
| Challenge | Templates | "Rewrite yours. Tag me." |
| Offer | Problems | "Facing this? DM me" |

### Velocity Framing

```
{Long time} to {old way}.
{Short time} to {new way}.
```

### Output Format

```markdown
---
content_type: "{type}"
mode: "loop-driven"
loop_trigger_type: "{type}"
velocity_proof: "{before} → {after}"
status: "draft"
---

# {Title}

{Content with velocity proof in first half}

---

{Loop trigger}

---

## Review Notes
- [ ] Loop trigger present
- [ ] Velocity framing present
- [ ] Brand voice applied
```

---

## Mode: Marketplace-Driven (Partner-Led)

**Content purpose:** Support discovery and conversion on platform.

See `references/marketplace-copy.md` for platform guidelines.

### Content Types

| Type | Purpose |
|------|---------|
| App listing | Convert to installs |
| Feature descriptions | Explain value |
| Changelog | Retain users |
| Review prompts | Generate social proof |
| Support articles | Reduce churn |

### Rules

1. Benefit-first, keyword-aware
2. Show value, not features
3. Clear, actionable, scannable
4. Platform guidelines followed

### Output Format

```markdown
---
content_type: "{type}"
mode: "marketplace-driven"
platform: "{platform}"
keywords: ["{list}"]
status: "draft"
---

# {Title}

{Content}

---

## Platform Notes
- [ ] Keywords included
- [ ] Character limits met
- [ ] Guidelines followed
```

---

## Mode: Sales-Driven (SLG)

**Content purpose:** Enable sales conversations.

See `references/sales-content.md` for patterns.

### Content Types

| Type | Purpose |
|------|---------|
| Case studies | Prove value |
| One-pagers | Leave-behind |
| Battle cards | Competitive positioning |
| Email sequences | Nurture |
| Pitch decks | Present to committee |

### Rules

1. Speak to buyer committee
2. Include ROI/metrics
3. Address objections
4. Single clear CTA

### Output Format

```markdown
---
content_type: "{type}"
mode: "sales-driven"
sales_stage: "{stage}"
target_persona: "{persona}"
status: "draft"
---

# {Title}

{Content}

---

## Sales Notes
- [ ] ROI included
- [ ] Objections addressed
- [ ] Single CTA
- [ ] Persona-appropriate
```

---

## Mode: Hybrid

1. Identify primary purpose
2. Apply that mode's rules
3. Note secondary purposes

```markdown
---
content_type: "{type}"
mode: "hybrid"
primary_purpose: "{mode}"
secondary_purpose: "{mode}"
---
```

---

## References

- `references/loop-mechanics.md`  -  Loop triggers, velocity, examples
- `references/marketplace-copy.md`  -  Platform guidelines
- `references/sales-content.md`  -  Sales enablement patterns

## Boundaries

**DO:**
- Confirm mode before generating
- Apply mode-appropriate rules
- Validate against mode requirements
- Flag mismatches

**DON'T:**
- Apply loop mechanics to sales content
- Skip mode confirmation
- Create without purpose alignment
- Assume one-size-fits-all