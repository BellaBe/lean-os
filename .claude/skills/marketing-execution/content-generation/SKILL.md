---
name: content-generation
description: Generate educational content drafts from thread learning. Transforms business insights into 80% complete content following brand voice (educational, technical, non-promotional) and content patterns. Human reviews for accuracy and depth.
allowed-tools: "Read,Write,Bash"
---

# Content Generation

Transform thread learning into educational content drafts.

## Purpose

**Input:** Content opportunity (from content-strategy) + Thread learning  
**Output:** 80% complete draft following brand voice and content patterns  
**Human role:** Review for accuracy, refine last 20%

**Core principle:** Share knowledge, not sales pitches. Build authority through depth.

---

## Process

### Step 1: Load Context

**Read opportunity:**
```bash
threads/marketing/campaigns/{campaign-slug}/4-decision.md  # Content plan with opportunities
```

Extract from opportunity:
- `topic` - What to write about
- `content_type` - blog|case-study|announcement|linkedin|email
- `target_keyword` - Primary SEO keyword
- `source_thread` - Where the learning came from
- `pillar` - Which content pillar this supports

**Read source material:**
```bash
# Source thread context
{source_thread}/1-input.md          # What triggered this
{source_thread}/2-hypothesis.md     # What was tested
{source_thread}/6-learning.md       # What was learned

# Strategic positioning
strategy/canvas/{product}/07-uvp.md     # Value proposition
strategy/canvas/{product}/05-problem.md # Problem definition

# Brand voice
artifacts/marketing/narrative/brand-voice.md
```

If `source_thread` includes sales narratives:
```bash
artifacts/sales/{segment}/narratives/{persona}-narrative.md
```

### Step 2: Select Pattern

**Load pattern guide for content type:**
```bash
{baseDir}/references/{content_type}-pattern.md
```

Available patterns:
- `blog-patterns.md` - 5 patterns (problem analysis, implementation guide, industry research, technical deep dive, case study)
- `case-study-pattern.md` - Customer success stories
- `announcement-pattern.md` - Product/feature launches
- `linkedin-patterns.md` - Company page posts
- `email-patterns.md` - Newsletters, announcements

**Pattern guides provide:**
- Structure principles (not rigid templates)
- Example openings/transitions
- Common pitfalls to avoid
- Length guidelines (ranges, not exact)

### Step 3: Generate Draft

**Apply pattern:**
- Follow structure from pattern guide
- Use source thread for facts/data
- Apply brand voice from `brand-voice.md`
- Include technical depth

**Brand voice essentials:**
- Educational focus (teach, don't sell)
- Data-driven (specific metrics from threads)
- Technical depth (architecture, methodology)
- Honest (include uncertainties, limitations)
- No CTAs (no "Book a demo", "Sign up now")

**Critical rules:**
- All metrics must come from threads (no invented numbers)
- Customer names require public approval (check thread for confirmation)
- No confidential information (remove proprietary details)
- Technical details must match thread/Canvas exactly

### Step 4: Validate Quality

**Run validation script:**
```bash
python {baseDir}/scripts/validate_draft.py --draft {draft_path}
```

Checks:
- Brand voice compliance (tone, depth, honesty)
- Factual accuracy (all claims sourced)
- Pattern adherence (structure, length)
- SEO readiness (if blog: keyword placement, H2s)

**Manual review flags:**
```markdown
## Editor Notes

**For human review:**
- [ ] {Specific items needing verification}
- [ ] {Potential improvements}
- [ ] {Missing context or data}
```

---

## Output Format

**Draft file:**
```markdown
---
title: "{Draft title}"
content_type: "{type}"
target_keyword: "{keyword}"
source_thread: "{path}"
pillar: "{pillar}"
created: "{date}"
status: "draft"
word_count: {count}
---

# {Title}

{Full content following pattern}

---

## Editor Notes

**For human review:**
- [ ] {Verification items}

**Potential improvements:**
- {Suggestions}
```

**Save location:**
```
threads/marketing/campaigns/{campaign-slug}/5-actions/drafts/{slug}-draft.md
```

**Update ops dashboard:**
```markdown
## Content Drafts Ready for Review

1. **{Title}**
   - Type: {content_type} ({word_count} words)
   - Location: {file_path}
   - Keyword: "{keyword}"
   - Action: Review for accuracy, approve for SEO optimization
```

---

## Edge Cases

### Insufficient Source Material
**If thread lacks details:**
- Flag: "Insufficient data for {content_type}"
- Request human provides additional context
- Or suggest alternative content type

### Confidential Information
**If thread contains confidential data:**
- Anonymize customer names, specific metrics
- Generalize: "A {premium segment} company" vs "BrandName"
- Flag for human review before proceeding

### Customer Approval Required
**If using customer name/data:**
- Flag: "Customer approval needed for public use"
- Mark draft as "pending approval"
- Don't proceed without confirmation

### Multiple Source Threads
**If opportunity combines multiple threads:**
- Read all source threads
- Synthesize learnings
- Note pattern: "Based on {N} deals across {timeframe}"

---

## Quality Standards

**Draft acceptance criteria:**
- 80% complete (human refines last 20%)
- All metrics sourced from threads
- Brand voice applied consistently
- Pattern structure followed
- Technical depth included
- No sales language

**Success = Educational content that builds authority and converts organically.**

---

## Usage Example

**Input opportunity:**
```yaml
topic: "How {Premium Segment} Use {Solution Approach}"
content_type: "case-study"
target_keyword: "{target keyword}"
source_thread: "threads/sales/{customer-thread}/"
pillar: "Product capabilities"
```

**Process:**
1. Read campaign: `threads/marketing/campaigns/{campaign-slug}/4-decision.md`
2. Read source: `threads/sales/{customer-thread}/6-learning.md`
3. Read positioning: `strategy/canvas/07-uvp.md`
4. Read voice: `artifacts/marketing/narrative/brand-voice.md`
5. Load pattern: `{baseDir}/references/case-study-pattern.md`
6. Generate draft following pattern structure
7. Validate with `validate_draft.py`
8. Save to `drafts/{customer}-case-study-draft.md`
9. Flag in `ops/today.md` for human review

**Output:** 1,450-word case study with metrics from thread, technical details, educational tone, ready for human review.