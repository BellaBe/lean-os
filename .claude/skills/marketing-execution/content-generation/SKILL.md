---
name: content-generation
description: Generate content drafts from thread learning and content opportunities. Applies brand voice (educational, technical, non-promotional), follows content patterns (not templates), and produces 80% complete drafts requiring human review for accuracy and depth.
allowed-tools: "Read,Write"
---

# Content Generation

You generate educational content drafts from business learning.

## Purpose

Content opportunity + Thread learning → Draft content (80% complete)

**Core principle:** Share knowledge, not sales pitches. Build authority through depth.

---

## Input Requirements

### Required Inputs

**1. Content opportunity (from content-strategy):**
```yaml
topic: "How Enterprise Fashion Brands Use White-Label SDKs"
content_type: "case study"
pillar: "Product capabilities"
target_keyword: "white-label SDK"
source_thread: "threads/sales/elsa-white-label/"
```

**2. Source material:**
- Campaign decision: `threads/marketing/campaigns/{campaign-slug}/4-decision.md`
- Source learning: `{source_thread}/6-learning.md` (if applicable)
- Thread context: `{source_thread}/1-input.md` through `6-results.md`
- Canvas positioning: `strategy/canvas/{product}/`
- Sales narratives: `artifacts/sales/{segment}/narratives/`

**3. Brand voice guidelines:**
- `artifacts/marketing/narrative/brand-voice.md`

**4. Content patterns (not templates):**
- `{baseDir}/references/{content_type}-patterns.md`

---

## Content Generation Process

### Step 1: Load Context

**Read campaign context:**
```bash
threads/marketing/campaigns/{campaign-slug}/4-decision.md  # Content plan
threads/marketing/campaigns/{campaign-slug}/5-actions/execution-log.md  # Progress tracking
```

**Read source thread (if applicable):**
```bash
{source_thread}/1-input.md       # What triggered this
{source_thread}/2-hypothesis.md  # What was tested
{source_thread}/6-learning.md    # What was learned
```

**Read positioning:**
```bash
strategy/canvas/{product}/07-uvp.md        # Value proposition
strategy/canvas/{product}/05-problem.md    # Problem definition
artifacts/sales/{segment}/narratives/      # If applicable
```

**Read voice guidelines:**
```bash
artifacts/marketing/narrative/brand-voice.md
```

### Step 2: Select Content Pattern

**Load pattern guide:**
```bash
{baseDir}/references/{content_type}-patterns.md
```

**Pattern types:**
- `blog-patterns.md` - 5 patterns (problem analysis, implementation guide, industry research, technical deep dive, case study)
- `case-study-pattern.md` - Customer success structure
- `announcement-pattern.md` - Product launch/feature announcement
- `linkedin-patterns.md` - Company page content (announcements, insights, milestones)
- `email-patterns.md` - Newsletter, announcement, educational series

**Select pattern based on content_type from opportunity.**

### Step 3: Generate Draft

**Apply pattern structure:**
- Follow pattern guide (not rigid template)
- Use source thread for facts/data
- Apply brand voice characteristics
- Include technical depth

**Core requirements:**
- **Educational focus:** Teach, don't sell
- **Data-driven:** Specific metrics from threads
- **Technical depth:** Don't oversimplify
- **Honest:** Include uncertainties, limitations
- **No CTAs:** No "Book a demo", "Sign up now"

### Step 4: Validate Quality

**Check against brand voice:**
- [ ] Tone: Educational, authoritative (not promotional)
- [ ] Depth: Technical details included (not surface-level)
- [ ] Honesty: Admits unknowns/limitations
- [ ] Data: Specific numbers (not vague claims)
- [ ] No sales language: No buzzwords, CTAs, engagement bait

**Check against pattern:**
- [ ] Structure follows pattern guide
- [ ] Length appropriate for content type
- [ ] All required sections present
- [ ] Examples/data included

**Check factual accuracy:**
- [ ] All claims sourced from threads or Canvas
- [ ] Metrics match thread results exactly
- [ ] Customer names approved for public use
- [ ] No confidential information included

---

## Content Type Specifications

### Blog Article (Problem Analysis)

**Pattern:** Problem → Data → Analysis → Implication

**Length:** 800-1,200 words

**Structure:**
```markdown
# {SEO-optimized title with keyword}

## Introduction (100-150 words)
- Problem context (what's happening in industry)
- Why it matters (impact on target audience)
- What reader will learn

## The Problem (200-300 words)
- Specific pain point from Canvas/threads
- Quantified impact (data from threads)
- Why obvious solutions don't work

## Data Analysis (300-400 words)
- Original data/research (from threads)
- Methodology explained (how we know this)
- Findings with specific numbers
- Surprising insights

## Implications (200-300 words)
- What this means for audience
- Non-obvious conclusions
- Actionable insights

## Conclusion (100-150 words)
- Key takeaways (3-5 points)
- Related topics (internal links)
- NO hard CTA (maybe "Learn more about {topic}")
```

**Example opening (ElsaAI case study):**
```markdown
# Why Luxury Fashion Brands Choose White-Label Over Co-Branded SDKs

## Introduction

When we launched our fit recommendation SDK, we assumed enterprise brands would prefer co-branded widgets—our logo alongside theirs. After 5 enterprise deals, we learned we were wrong.

100% of luxury brands ($100M+ GMV) chose white-label integration. This wasn't about hiding our technology. It was about brand consistency being non-negotiable in luxury e-commerce.

Here's what we learned from $5.5M in enterprise contracts about brand positioning and SDK architecture.
```

### Blog Article (Implementation Guide)

**Pattern:** Challenge → Approach → Implementation → Results

**Length:** 1,200-2,000 words

**Structure:**
```markdown
# {How-to title with keyword}

## Introduction
- Problem to solve
- Why it's challenging
- What this guide covers

## The Challenge (200-300 words)
- Specific technical/business problem
- Why obvious approaches fail
- Requirements for solution

## Our Approach (300-500 words)
- Solution architecture/methodology
- Why this works
- Trade-offs considered

## Implementation (400-800 words)
- Step-by-step process
- Technical details (code, architecture)
- Pitfalls to avoid
- Time/resource requirements

## Results (200-300 words)
- Metrics from implementation
- Lessons learned
- What we'd do differently

## Conclusion
- Key takeaways
- When to use this approach
- Related resources
```

### Case Study

**Pattern:** Customer → Problem → Solution → Results

**Length:** 1,000-1,500 words

**Structure:**
```markdown
# {Customer Name}: {Result Achieved}

## Customer Overview (100-150 words)
- Company name, industry, size
- Business model
- Initial challenge

## The Problem (250-350 words)
- Specific pain point (quantified)
- Business impact (revenue, costs)
- Previous solutions attempted
- Why they needed change

## Solution (300-400 words)
- What they implemented
- Technical approach
- Implementation timeline
- Resources required

## Results (300-400 words)
- Metrics (before/after)
- Timeline to results
- Unexpected benefits
- Customer quote (if available)

## Technical Details (200-300 words)
- Architecture/integration approach
- Challenges overcome
- Why it worked

## Conclusion (100-150 words)
- Key success factors
- Applicability to others
- Soft link to product (if relevant)
```

**Example (ElsaAI):**
```markdown
# ElsaAI Reduced Returns 38% with White-Label Fit Recommendations

## Customer Overview

ElsaAI is a luxury fashion marketplace with $200M GMV serving 250K monthly customers. Their curated selection emphasizes high-end designers and premium pricing—where brand consistency is critical.

They faced a 25% return rate on dresses, costing $3.2M annually in reverse logistics and lost revenue.

## The Problem

Luxury customers expect flawless brand experiences. ElsaAI's previous fit solution used a co-branded widget that broke their visual aesthetic:

- Widget displayed third-party branding
- Design didn't match site style
- Mobile experience was clunky
- Customers questioned legitimacy

Beyond aesthetics, fit accuracy was insufficient:
- Generic size charts: 68% accuracy
- Virtual try-on competitors: 72% accuracy
- Neither met the 85% threshold ElsaAI needed

At 25% return rates, $120 average order value, and 50K dress orders/year:
- Revenue impact: $1.5M (25% of $6M)
- Reverse logistics: $400K ($8 per return)
- Customer service: $200K (15 min per return @ $40/hr)
- Total annual cost: $2.1M

## Solution

ElsaAI implemented our white-label SDK with custom branding:

**Technical approach:**
- React SDK with custom styling
- ElsaAI's fonts, colors, design system
- Hosted on ElsaAI subdomain (fit.elsaai.com)
- Zero external branding

**Integration:**
- 2-week implementation
- 10 hours engineering time
- No infrastructure changes needed

**Fit accuracy:**
- AI trained on 10M+ body scans
- 94% accuracy on luxury dress category
- Personalized per customer

## Results

**30-day pilot (dress category only):**
- Return rate: 25% → 18% (28% reduction)
- Fit accuracy: 94% (vs 68% baseline)
- Customer satisfaction: 3.2 → 4.1 (27% improvement)
- Mobile conversion: +12% (cleaner UI)

**Annual projection:**
- Returns avoided: 3,500 (7% of 50K orders)
- Revenue retained: $420K
- Logistics saved: $280K
- Customer service saved: $105K
- Total annual savings: $805K

**ROI:**
- Implementation cost: $500K/year (white-label tier)
- Savings: $805K/year
- Net benefit: $305K (61% ROI)
- Payback: 7.4 months

## Technical Details

**Architecture:**
- SDK loaded asynchronously (no page speed impact)
- Body measurement API: <200ms latency
- Recommendation cache: 99.9% uptime
- Analytics dashboard: Real-time fit data

**Challenges overcome:**
1. **Brand consistency:** Custom CSS matching ElsaAI's design system exactly
2. **Mobile performance:** Lazy loading prevented slowdown
3. **Data privacy:** GDPR-compliant body measurement storage

**Why it worked:**
- White-label removed trust friction
- 94% accuracy exceeded luxury threshold
- Fast integration minimized engineering burden

## Conclusion

ElsaAI's success validates three insights:

1. **Luxury brands won't compromise on brand consistency** - Co-branded solutions are non-starters regardless of accuracy
2. **Fit accuracy >90% is table stakes** - Luxury customers expect near-perfect recommendations
3. **Fast implementation matters** - 2-week integration vs 3-month custom build

This approach works for fashion brands with:
- Strong brand identity (luxury, premium)
- High average order value (>$100)
- Technical team for integration (5-10 hours)

White-label SDK available for enterprise: Technical docs at {link}
```

### Product Announcement

**Pattern:** What → Why → How → Who → When

**Length:** 400-700 words

**Structure:**
```markdown
# {Feature/Product Name} Now Available

## What (100-150 words)
- Feature/product name
- One-sentence summary
- Primary benefit

## Why (150-200 words)
- Problem this solves
- Customer demand (from threads)
- Strategic context

## How (200-300 words)
- Technical approach
- Key capabilities
- Differentiation from alternatives

## Who (100-150 words)
- Target customers
- Use cases
- Requirements

## When & Pricing (50-100 words)
- Availability (now, beta, Q1 2025)
- Pricing tier
- How to access

## Technical Details (optional, 100-200 words)
- Architecture highlights
- Integration approach
- Performance specs
```

### LinkedIn Company Post

**Pattern:** Insight → Analysis → Implication

**Length:** 300-600 words

**Structure:**
```markdown
{Opening observation or data point}

{Analysis with supporting details}

{Implication or learning}

{Soft link to product/content if relevant}
```

**Example:**
```markdown
We closed 5 enterprise fashion deals in Q4. All 5 chose white-label SDK over co-branded.

This wasn't about hiding our technology. It was about brand consistency being non-negotiable.

What we learned:

**Luxury brands ($100M+ GMV) prioritize brand consistency over vendor recognition**

They'll pay 3x more for white-label because:
- Co-branded widgets break visual aesthetic
- Customers question legitimacy of third-party branding
- Mobile experience needs seamless integration

One customer (luxury marketplace, $200M GMV) told us: "Our customers don't care who powers fit recommendations. They care that it looks like ElsaAI."

**Fast fashion brands ($10M-$50M GMV) prefer co-branded**

Opposite behavior:
- Third-party branding adds credibility ("powered by AI")
- Lower technical resources (easier implementation)
- Price-sensitive (white-label costs 3x)

**Takeaway:**
Customer segment dictates product packaging. Same technology, different positioning.

We're now offering both:
- White-label: Enterprise tier ($400K+)
- Co-branded: Growth tier ($50K+)

Technical docs: {link}
```

### Email Newsletter

**Pattern:** Curated insights + Educational content

**Length:** 400-600 words

**Structure:**
```markdown
Subject: {Specific value, not clickbait}

Preview: {Extend subject, don't repeat}

---

{Personal greeting}

{Opening: Why this matters now}

**Section 1: {Insight}** (150-200 words)
- Key learning or announcement
- Supporting data
- Link to full article

**Section 2: {Resource}** (150-200 words)
- Educational content
- Practical takeaway
- Link to guide/case study

**Section 3: {Update}** (100-150 words)
- Product update or industry news
- Brief context
- Link for more

---

{Closing line}

{Real person signature}
{Name, Title}
```

---

## Quality Validation

**Before outputting draft, verify:**

### Brand Voice Compliance

- [ ] **Educational tone:** Teaches, doesn't sell
- [ ] **Technical depth:** Includes architecture, data, methodology
- [ ] **Data-driven:** Specific numbers (not "many", "significant")
- [ ] **Honest:** Admits limitations, uncertainties
- [ ] **No sales language:** No buzzwords, CTAs, engagement tricks

### Factual Accuracy

- [ ] **All metrics from threads:** No invented numbers
- [ ] **Customer names verified:** Check thread for public approval
- [ ] **Technical details accurate:** Match thread/Canvas exactly
- [ ] **No confidential info:** Remove proprietary details

### Structure Compliance

- [ ] **Pattern followed:** Matches selected pattern guide
- [ ] **Length appropriate:** Within range for content type
- [ ] **Complete sections:** No "TODO" or missing parts
- [ ] **Transitions smooth:** Logical flow between sections

### SEO Readiness (if blog)

- [ ] **Keyword in title:** Natural integration
- [ ] **Keyword in first 100 words:** Organic mention
- [ ] **H2 subheadings:** Descriptive, include variations
- [ ] **Internal link opportunities:** Note related content

---

## Output Format

### Draft File Structure
```markdown
---
# Metadata (for tracking)
title: "{Draft title}"
content_type: "{blog|case-study|announcement|linkedin|email}"
target_keyword: "{primary keyword}"
source_thread: "{thread path}"
pillar: "{content pillar}"
created: "{date}"
status: "draft"
word_count: {count}
---

# {Title}

{Full content following pattern}

---

## Editor Notes

**For human review:**
- [ ] Verify customer name approval (ElsaAI - check with legal?)
- [ ] Confirm metrics accuracy (25% → 18% return rate)
- [ ] Add internal links (related articles on return reduction)
- [ ] Review technical depth (enough for credibility?)

**Potential improvements:**
- Add quote from ElsaAI customer (if available)
- Include architecture diagram (if exists)
- Link to technical docs (where hosted?)
```

### Save Location

**Drafts awaiting review:**
```
threads/marketing/campaigns/{campaign-slug}/5-actions/drafts/{piece}-draft.md
```

**Notification in ops/today.md:**
```markdown
## Content Drafts Ready for Review

1. **Case Study: ElsaAI White-Label Success**
   - Type: Blog article (1,450 words)
   - Location: threads/marketing/campaigns/luxury-validation-nov-2024/5-actions/drafts/elsaai-case-study-draft.md
   - Keyword: "white-label SDK"
   - Action: Review for accuracy, approve for SEO optimization
```

---

## Edge Cases

### Insufficient Source Material

**If thread lacks details:**
- Flag: "Insufficient data for {content_type}"
- Request: Human provides additional context
- Or: Suggest alternative content type (announcement vs case study)

### Confidential Information

**If thread contains confidential data:**
- Anonymize: Remove customer names, specific metrics
- Generalize: "A luxury fashion brand" vs "ElsaAI"
- Or: Flag for human review before proceeding

### Customer Approval Required

**If using customer name/data:**
- Flag: "Customer approval needed for public use"
- Provide draft but mark as "pending approval"
- Don't proceed to publication without confirmation

### Multiple Threads as Source

**If opportunity combines multiple threads:**
- Read all source threads
- Synthesize learnings
- Note pattern: "Based on 8 deals across Q4"
- Higher confidence in conclusions

---

## Success Metrics

**Draft quality:**
- Human approval rate: >80% (drafts accepted with minor edits)
- Revision rounds: <2 (before final approval)
- Factual errors: 0 (all data accurate)

**Efficiency:**
- Time to draft: <2 hours (AI generation)
- Human review time: <30 minutes (80% complete)
- Total time to publish: <1 day (draft → review → optimize → publish)

**Content effectiveness (measured post-publication):**
- Organic traffic: {sessions per article}
- Engagement: {time on page, scroll depth}
- Conversions: {demos requested per article}

---

## Usage Example

**Input:**
```yaml
topic: "How Enterprise Fashion Brands Use White-Label SDKs"
content_type: "case study"
target_keyword: "white-label SDK"
source_thread: "threads/sales/elsa-white-label/"
pillar: "Product capabilities"
```

**Process:**
```
1. Load thread:
   - Read Campaign: threads/marketing/campaigns/luxury-validation-nov-2024/4-decision.md
   - Read Source: threads/sales/elsa-white-label/6-learning.md
   - Extract: Customer (ElsaAI), Problem (returns), Solution (white-label), Results (38% reduction)

2. Load positioning:
   - Read: strategy/canvas/07-uvp.md
   - Extract: "AI-powered fit recommendations reduce returns"

3. Load voice:
   - Read: artifacts/marketing/narrative/brand-voice.md
   - Apply: Educational, technical, data-driven tone

4. Select pattern:
   - Load: {baseDir}/references/case-study-pattern.md
   - Structure: Customer → Problem → Solution → Results

5. Generate draft:
   - 1,450 words
   - Includes: Metrics (25% → 18%), Technical details (React SDK), ROI ($305K net benefit)
   - Voice: Educational (explains why luxury prefers white-label)
   - No CTA: Soft link to technical docs only

6. Validate:
   - ✓ Brand voice (educational, technical)
   - ✓ Factual (all numbers from thread)
   - ✓ Complete (all sections present)
   - ✓ SEO-ready (keyword in title, H2s)

7. Output:
   - Save: threads/marketing/campaigns/luxury-validation-nov-2024/5-actions/drafts/elsaai-case-study-draft.md
   - Flag: ops/today.md for human review
```

---

## Remember

**Content generation is:**
- Transforming thread learning into educational content
- Applying brand voice (authoritative, not promotional)
- Following patterns (structure guides, not templates)
- Creating 80% complete drafts (human refines last 20%)

**Content generation is NOT:**
- Writing sales pitches disguised as content
- Inventing data or metrics
- Auto-publishing without human review
- Following rigid templates verbatim

**Success = Educational content that builds authority and converts organically.**