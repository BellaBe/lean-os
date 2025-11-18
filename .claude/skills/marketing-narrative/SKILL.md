---
name: marketing-narrative
description: Generate content strategy for building authority and trust through educational content. Defines content pillars (strategic themes), SEO strategy (keyword priorities), brand voice (public content tone), and channel guidelines (format specifications) based on Canvas positioning and sales narratives.
allowed-tools: "Read,Write"
---

# Marketing Narrative Generator

You generate content strategy that builds market authority through educational, non-promotional content.

## Purpose

Transform Canvas positioning + Sales narratives → Content strategy (pillars, SEO, voice, channels)

**Core principle:** Marketing builds trust through knowledge sharing, not sales pitches.

---

## Input Requirements

### Required Files

**Canvas (strategy/canvas/):**
- `04-segments.md` - Customer segments
- `05-problem.md` - Problems to address
- `07-uvp.md` - Value proposition
- `08-advantage.md` - Differentiation
- `09-solution.md` - Product capabilities

**Sales Narratives (artifacts/sales/{segment}/narratives/):**
- `{segment}-{buyer-type}.md` - Narratives per buyer type (economic, technical, end-user, etc.)
- `{segment}-objection-lib.md` - Common objections and responses per segment

**If files missing:** Inform user which files needed.

**If sales narratives don't exist:** Use Canvas only (sales narratives provide consistency but aren't required).

---

## Output Structure
```
artifacts/marketing/narrative/
├── content-pillars.md       # 3-5 strategic themes
├── seo-strategy.md          # Priority keywords by funnel stage
├── brand-voice.md           # Public content voice guidelines
└── channel-guidelines.md    # Format specs per channel
```

**NOT per channel.** These 4 files apply across all channels.

---

## Generation Process

### Step 1: Extract Core Positioning

**From Canvas:**
- Problems: What pain points exist (problem.md)
- Solution: What product does (solution.md)
- Differentiation: What makes it unique (uvp.md, advantage.md)
- Segments: Who it's for (segments.md)

**From Sales Narratives (if exist):**
- Problem articulation: How each segment experiences pain
- Solution framing: How solution maps to segments
- Proof points: Customer results, metrics

### Step 2: Generate content-pillars.md

**Structure:**
```markdown
# Content Pillars - GlamYouUp

Generated: {date}

## Pillar 1: {Theme Name}

**Description:** {What this pillar covers}

**Canvas alignment:** {Which Canvas section this addresses}

**Target segments:** {Which customer segments care about this}

**Content angles:**
1. **{Angle}:** {Specific topic approach}
   - Format: {Article/analysis/guide}
   - Frequency: {When to publish}
   - Example: "{Sample topic}"

2. **{Angle}:** {Specific topic approach}
   - Format: {Article/analysis/guide}
   - Frequency: {When to publish}
   - Example: "{Sample topic}"

**SEO keywords:**
- Primary: {main keyword}
- Secondary: {related keywords}

**Success metrics:**
- Traffic: {target}
- Engagement: {target}
- Conversions: {target}

## Pillar 2: {Theme Name}
{Repeat structure}

## Pillar 3: {Theme Name}
{Repeat structure}

## Content Strategy

**Pillar distribution:** {How to balance pillars}
- Example: "40% Pillar 1, 30% Pillar 2, 30% Pillar 3"

**Publishing triggers:**
- Business learning: When sales/engineering threads reveal insights
- Market events: Industry shifts, competitor moves
- Product launches: New features, capabilities

**Quality over quantity:**
- Publish when there's substance worth sharing
- No arbitrary "30 posts/month" quotas
- Each piece should teach something valuable
```

**Guidelines:**
- 3-5 pillars (not 8+)
- Each pillar = distinct theme from Canvas problems/solution
- Pillars must be sustainable (20+ articles per year possible)
- Map to customer segment interests

### Step 3: Generate seo-strategy.md

**Structure:**
```markdown
# SEO Strategy - GlamYouUp

Generated: {date}

## Keyword Research Approach

**Sources:**
- Sales conversations: What prospects search for
- Problem articulation: Pain points from Canvas
- Competitor content: Gaps in market coverage

## Keywords by Funnel Stage

### Top of Funnel (Awareness)

**Primary keywords:** {high-volume problem keywords}
- "{keyword 1}" - {search volume estimate}
- "{keyword 2}" - {search volume estimate}

**Content type:** Educational blog posts, industry analysis

**Target:** People discovering they have the problem

### Middle of Funnel (Consideration)

**Primary keywords:** {solution-category keywords}
- "{keyword 1}" - {search volume estimate}
- "{keyword 2}" - {search volume estimate}

**Content type:** How-to guides, solution comparisons

**Target:** People researching solution approaches

### Bottom of Funnel (Decision)

**Primary keywords:** {product/competitor keywords}
- "{product name}" - {search volume estimate}
- "{competitor} alternative" - {search volume estimate}

**Content type:** Product pages, case studies

**Target:** People evaluating specific vendors

## Content Opportunities

**High-value targets:**
1. {Keyword}: {Why this matters}
   - Content pillar: {Which pillar}
   - Estimated impact: {Traffic/leads}

2. {Keyword}: {Why this matters}
   - Content pillar: {Which pillar}
   - Estimated impact: {Traffic/leads}

## Keyword Mapping to Pillars

| Keyword | Pillar | Priority | Difficulty |
|---------|--------|----------|------------|
| {kw} | {pillar} | High | Medium |
| {kw} | {pillar} | Medium | Low |
```

**Guidelines:**
- Use web_search to research keyword volume (if allowed)
- Prioritize keywords where customers actually search
- Map keywords to specific content pillars
- Include competitor keywords for comparison content

### Step 4: Generate brand-voice.md

**Structure:**
```markdown
# Brand Voice - GlamYouUp

Generated: {date}

## Voice Attributes

**For public content (blog, LinkedIn, website, email):**

**Tone:** {Professional, authoritative, educational}

**NOT:** {Sales-focused, promotional, engagement-bait}

**Characteristics:**
- **{Trait 1}:** {How it manifests}
  Example: "Data-driven: Include specific metrics, not vague claims"
  
- **{Trait 2}:** {How it manifests}
  Example: "Technical depth: Don't dumb down for non-technical readers"
  
- **{Trait 3}:** {How it manifests}
  Example: "Honest: Share failures and unknowns, not just wins"

## Content Philosophy

**Purpose:** Build authority through knowledge sharing

**NOT:** Generate leads through engagement tactics

**Approach:**
- Share what you learned (not what you sell)
- Document build process (not results)
- Analyze trends (not hot takes)
- Provide depth (not surface-level tips)

## Writing Guidelines

**Structure:**
- No hook formulas ("Most X think Y...")
- No CTAs (no "Book a demo", "Sign up now")
- No engagement bait ("What do you think?")
- Length: However long needed to explain properly

**Style:**
- Technical details included (code, architecture, data)
- Citations and sources (not just opinions)
- Honest about uncertainties (not overconfident)
- Original analysis (not regurgitated content)

## Vocabulary

**DO use:**
- Industry-standard terms (from Canvas solution.md)
- Technical terminology (don't simplify unnecessarily)
- Specific metrics (numbers, not "many" or "significant")
- Data sources (cite where information comes from)

**AVOID:**
- Marketing buzzwords: {list from Canvas or common offenders}
  Example: "synergy, disruptive, game-changer, best-in-class"
- Vague claims: "improve efficiency, optimize performance"
- Promotional language: "amazing, revolutionary, incredible"
- Engagement tricks: Emoji spam, clickbait, "change my mind"

## Content Quality Bar

**Publish when:**
- Significant learning occurred (from threads)
- Original analysis or data to share
- Technical depth warrants documentation
- Insight challenges conventional thinking

**Don't publish:**
- Just to hit publishing quota
- Repackaged generic advice
- Content without substance
- Sales pitch disguised as education

## Example Transformations

**Sales narrative (1-to-1):**
"{Sample from sales-narrative: problem-narrative.md}"

**Marketing content (1-to-many):**
"{Adapted for public: educational, not personalized}"

**Why different:** {Explain the adaptation}
```

**Guidelines:**
- Voice is educational, not promotional
- Authority comes from depth, not engagement
- No "growth hacking" tactics
- Quality over quantity

### Step 5: Generate channel-guidelines.md

**Structure:**
```markdown
# Channel Guidelines - GlamYouUp

Generated: {date}

## Blog

**Purpose:** Organic discovery (SEO), education, thought leadership

**Content types:**
- Industry analysis (800-1,200 words)
- Technical deep dives (1,500-2,500 words)
- Implementation guides (1,200-2,000 words)
- Case studies (1,000-1,500 words)

**Structure:**
- Title: Keyword-optimized (from seo-strategy.md)
- Intro: Problem context + what reader learns
- Body: Detailed analysis with data/examples
- Conclusion: Key takeaways (no hard CTA)

**SEO requirements:**
- H1: Primary keyword
- H2s: Secondary keywords
- First 100 words: Keyword mentioned naturally
- Internal links: 3-5 related articles
- Images: Alt text with keywords

**Quality bar:**
- Technical accuracy verified
- Sources cited
- Actionable (not just theory)
- Original analysis (not rehashed)

## LinkedIn (Company Page)

**Purpose:** Product updates, case studies, industry insights

**Content types:**
- Feature announcements (300-500 words)
- Customer success highlights (400-600 words)
- Industry trend analysis (500-800 words)
- Technical explanations (600-1,000 words)

**Structure:**
- Opening: Observation or data point
- Body: Analysis with specifics
- Close: Implication or learning (no CTA)

**Formatting:**
- Short paragraphs (1-2 sentences)
- Line breaks for readability
- No hashtag spam (3-5 max, end of post)
- Links in first comment (not post body)

**Quality bar:**
- Substantive (not engagement bait)
- Professional tone (not personal)
- Data-backed (metrics, sources)
- No "What do you think?" prompts

## Website

**Purpose:** Conversion (demonstrate value to prospects)

**Content types:**
- Product pages (feature → benefit → proof)
- Case studies (problem → solution → results)
- Technical documentation (implementation guides)
- About/company pages (positioning, team)

**Structure:**
- Hero: Clear value proposition (10-15 words)
- Sections: Scannable, benefit-focused
- Proof: Customer logos, testimonials, metrics
- CTA: Demo request, documentation, pricing

**Formatting:**
- Short paragraphs (2-3 sentences)
- Bullet points for lists
- Bold for key phrases
- White space for breathing room

**Quality bar:**
- Clear positioning (not vague)
- Quantified benefits (not claims)
- Social proof (real customers)
- Fast load time (<3 seconds)

## Email

**Purpose:** Nurture, education, product updates

**Content types:**
- Newsletter (400-600 words, curated insights)
- Product announcements (200-400 words)
- Educational series (300-500 words per email)
- Case study highlights (250-400 words)

**Structure:**
- Subject: Specific value (not clickbait)
- Preview: Extend subject (don't repeat)
- Body: Single topic, scannable
- CTA: One primary action (if needed)

**Formatting:**
- Short paragraphs (2-3 sentences)
- Mobile-optimized (single column)
- Clear CTA button (if included)
- Real sender (not "Marketing Team")

**Quality bar:**
- Valuable content (not filler)
- Relevant to recipient (segmented)
- Respectful of inbox (not spam)
- Easy unsubscribe (one click)

## Cross-Channel Consistency

**Same positioning across all channels:**
- Value proposition from Canvas
- Problem articulation from sales narratives
- Differentiation from Canvas advantage
- Proof points (metrics, customers)

**Adapted execution per channel:**
- Blog: Long-form, SEO-focused
- LinkedIn: Professional, data-driven
- Website: Conversion-focused, scannable
- Email: Personal, action-oriented

## Content Sourcing

**Trigger content from business learning:**

**Sales threads (Stage 7: Learning):**
- Validated hypothesis → Blog analysis
- Customer success → Case study
- Common objection → Educational content

**Business threads (Canvas updates):**
- Strategic pivot → Industry analysis
- Market shift → Trend commentary
- New segment → Segment-specific content

**Engineering threads (Feature launches):**
- New capability → Product announcement
- Technical innovation → Deep dive article
- Implementation → How-to guide

**Process:**
1. Thread completes (Stage 7: Learning)
2. AI flags content opportunity
3. Human decides: Worth sharing?
4. AI generates draft
5. Human edits for depth/voice
6. Publish when ready (not on schedule)
```

**Guidelines:**
- Different channels, same core positioning
- Format adapts, message doesn't
- Content triggers from threads (not arbitrary calendar)

---

## Output Summary
```markdown
## Marketing Narrative Complete

**Product:** GlamYouUp
**Generated:** {date}
**Location:** artifacts/marketing/narrative/

**Files created:**
- content-pillars.md (3-5 strategic themes)
- seo-strategy.md (keywords by funnel stage)
- brand-voice.md (public content voice)
- channel-guidelines.md (format specs)

**Content pillars:**
1. {Pillar 1}: {Description}
2. {Pillar 2}: {Description}
3. {Pillar 3}: {Description}

**Top SEO opportunities:**
- {Keyword 1}: {Pillar}
- {Keyword 2}: {Pillar}
- {Keyword 3}: {Pillar}

**Next steps:**
1. Review pillars against competitive content
2. Validate SEO keywords with web_search (volume/difficulty)
3. Create content when business threads generate learning
4. Track which content types drive pipeline

**Notes:** {Any warnings or recommendations}
```

---

## Quality Validation

Before finalizing:

- [ ] 3-5 content pillars (distinct themes)
- [ ] Each pillar maps to Canvas problems/solution
- [ ] SEO keywords align with customer search behavior
- [ ] Brand voice emphasizes education, not promotion
- [ ] Channel guidelines specify format, not just strategy
- [ ] Content sources from threads (learning-driven)
- [ ] No "30 posts/month" quotas (quality over quantity)

---

## Success Criteria

**Good marketing narrative enables:**
1. Content created when learning occurs (not arbitrary schedule)
2. Authority built through depth (not engagement tactics)
3. SEO-driven organic discovery (not paid promotion)
4. Trust established through education (not sales pitches)
5. Consistent positioning (same message, adapted format)

**Remember:** Marketing builds trust. Sales converts trust. Don't confuse the two.