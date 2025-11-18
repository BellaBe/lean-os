---
name: seo-optimization
description: Optimize content drafts for search engines while maintaining educational quality. Applies target keywords naturally, structures content with proper H1/H2 hierarchy, adds meta descriptions, suggests internal links, and ensures technical SEO requirements met without keyword stuffing.
allowed-tools: "Read,Write"
---

# SEO Optimization

You optimize content for organic discovery without sacrificing quality.

## Purpose

Draft content + Target keyword → SEO-optimized content

**Core principle:** Optimize for discovery, not at the expense of educational value.

---

## Input Requirements

### Required Inputs

**1. Draft content:**
```
threads/marketing/campaigns/{campaign-slug}/5-actions/drafts/{piece}-draft.md
```

**2. SEO strategy:**
```
artifacts/marketing/narrative/seo-strategy.md
```

**3. Target keyword (from content opportunity):**
```
Primary: "white-label SDK"
Secondary: ["enterprise fashion SDK", "branded fit recommendation"]
```

---

## Optimization Process

### Step 1: Analyze Current State

**Read draft content:**
- Extract title, headings (H1, H2, H3)
- Count word length
- Identify keyword mentions (current)
- Note structure and sections

**Load SEO strategy:**
- Primary keyword details
- Secondary keyword opportunities
- Funnel stage (TOFU/MOFU/BOFU)
- Competitive content (if available)

### Step 2: Title Optimization

**Current title analysis:**
- Does it contain primary keyword?
- Is it 50-60 characters (optimal for SERP)?
- Is it compelling (not just keyword stuffed)?

**Optimization rules:**
```
✓ Include primary keyword naturally
✓ 50-60 characters (SERP display limit)
✓ Front-load keyword if possible
✓ Remain compelling and specific
✗ Don't keyword stuff
✗ Don't sacrifice clarity for SEO
```

**Examples:**

**Before (not optimized):**
```
"Our Customer Success Story with ElsaAI"
```

**After (optimized):**
```
"White-Label SDK Case Study: ElsaAI Reduces Returns 38%"
- Keyword: ✓ (white-label SDK)
- Length: ✓ (55 characters)
- Compelling: ✓ (specific result)
```

**Before (keyword stuffed):**
```
"White-Label SDK for White-Label Fashion White-Label Solutions"
```

**After (natural):**
```
"How Enterprise Fashion Brands Use White-Label SDKs"
- Keyword: ✓ (white-label SDK)
- Natural: ✓ (readable, not spammy)
- Secondary keyword: ✓ (enterprise fashion)
```

### Step 3: Meta Description

**Create meta description (150-160 characters):**

**Rules:**
```
✓ 150-160 characters (SERP display)
✓ Include primary keyword
✓ Compelling summary (drives clicks)
✓ Include benefit or result
✗ Don't repeat title exactly
✗ Don't keyword stuff
```

**Template:**
```
"{Specific result or benefit} {with/using} {keyword}. {Supporting detail or proof point}."
```

**Example:**
```
Draft title: "White-Label SDK Case Study: ElsaAI Reduces Returns 38%"

Meta description:
"Learn how ElsaAI reduced fashion returns by 38% using a white-label SDK. Implementation guide, metrics, and ROI analysis from a $200M luxury marketplace."

- Length: 158 characters ✓
- Keyword: ✓ (white-label SDK)
- Compelling: ✓ (specific metrics, actionable)
```

### Step 4: Heading Structure (H1, H2, H3)

**H1 (Title):**
- Should be title (already optimized in Step 2)
- One H1 per page
- Contains primary keyword

**H2 (Main sections):**
- Descriptive, not clever
- Include keyword variations naturally
- 3-7 H2s per article (depends on length)

**H3 (Subsections):**
- Support H2s
- Use related terms (LSI keywords)
- Optional: Include long-tail keywords

**Example structure:**

**Before (generic):**
```
H1: ElsaAI Case Study
H2: The Problem
H2: The Solution
H2: The Results
```

**After (SEO-optimized):**
```
H1: White-Label SDK Case Study: ElsaAI Reduces Returns 38%
H2: Why Luxury Fashion Brands Need White-Label Fit Recommendations
H2: Implementing a White-Label SDK: Technical Approach
H2: Results: 38% Return Reduction in 30 Days
H2: White-Label vs Co-Branded: Enterprise SDK Comparison
```

**Keyword distribution:**
- H1: Primary keyword ✓
- H2 #1: Keyword variation (white-label fit recommendations) ✓
- H2 #2: Primary keyword (white-label SDK) ✓
- H2 #4: Keyword variation (white-label vs co-branded) ✓

### Step 5: Keyword Integration

**Primary keyword placement:**

**Required:**
- [ ] H1 (title)
- [ ] First 100 words (natural mention)
- [ ] At least 2 H2 subheadings
- [ ] Meta description
- [ ] URL slug

**Optional (if natural):**
- Body paragraphs (2-4 times per 1,000 words)
- Image alt text
- Conclusion

**Keyword density target:**
- 0.5-2% of total words
- Example: 1,500-word article = 7-30 mentions
- Natural distribution (not clustered)

**Example integration:**

**First 100 words:**
```
When we launched our fit recommendation SDK, we assumed enterprise 
brands would prefer co-branded widgets. After 5 enterprise deals, 
we learned we were wrong.

100% of luxury brands chose white-label SDK integration. This wasn't 
about hiding technology—it was about brand consistency being 
non-negotiable in luxury e-commerce.

Here's what we learned from $5.5M in enterprise contracts about 
white-label SDKs and brand positioning.
```

**Keyword mentions:**
- "white-label SDK" (sentence 2) ✓
- "white-label SDK integration" (sentence 2) ✓
- "white-label SDKs" (sentence 3) ✓
- Density: 3 mentions / 85 words = 3.5% (acceptable for intro)

**Secondary keywords:**
- "enterprise brands" ✓
- "luxury brands" ✓
- "fit recommendation" ✓

### Step 6: Internal Linking

**Strategy:**
- 3-5 internal links per article
- Link to related content (same pillar or related pillars)
- Use descriptive anchor text (not "click here")
- Link to high-value pages (product pages, popular articles)

**Internal link opportunities:**

**Identify linkable phrases:**
```
In draft:
"Luxury fashion brands face 25-30% return rates due to fit issues."

Link opportunity:
"Luxury fashion brands face 25-30% return rates due to [fit issues](link-to-article-on-fit-problems)."
```

**Anchor text rules:**
```
✓ Descriptive (tells reader what they'll find)
✓ Natural in context
✓ Keyword-relevant (helps SEO)
✗ Generic ("click here", "learn more")
✗ Overly optimized ("best white-label SDK solutions")
```

**Example internal links:**
```markdown
## Why Luxury Fashion Brands Need White-Label Fit Recommendations

Luxury customers expect seamless brand experiences. When ElsaAI 
first implemented [co-branded fit widgets](/blog/co-branded-vs-white-label), 
customer feedback was negative:

Their previous approach to [reducing fashion returns](/blog/reduce-returns-guide) 
used generic size charts with 68% accuracy...

For more on [enterprise SDK pricing](/pricing/enterprise), see our 
technical documentation.
```

**Links added:**
1. `/blog/co-branded-vs-white-label` (related topic, same pillar)
2. `/blog/reduce-returns-guide` (different pillar, high-value content)
3. `/pricing/enterprise` (product page, conversion-focused)

### Step 7: Image Optimization

**For each image in content:**

**Alt text:**
- Descriptive (what's in the image)
- Include keyword if natural
- 125 characters max
- Not keyword-stuffed

**Example:**
```
Image: Screenshot of white-label SDK integration

✗ Bad alt text: "image1.png"
✗ Bad alt text: "white-label SDK white-label integration white-label"
✓ Good alt text: "White-label SDK integration showing branded fit recommendation widget in ElsaAI's checkout flow"
```

**File naming:**
```
✗ IMG_1234.jpg
✓ white-label-sdk-integration-screenshot.jpg
```

**File size:**
- Compress images <200KB
- Use WebP format if possible
- Lazy loading for below-fold images

### Step 8: URL Slug

**Create SEO-friendly URL:**

**Rules:**
```
✓ Include primary keyword
✓ Use hyphens (not underscores)
✓ Lowercase only
✓ Short (3-5 words ideal)
✓ Descriptive of content
✗ No stop words (a, the, and, or)
✗ No special characters
✗ No dates (unless time-sensitive)
```

**Examples:**

**From title:** "White-Label SDK Case Study: ElsaAI Reduces Returns 38%"
```
✗ white-label-sdk-case-study-elsaai-reduces-returns-38-percent
   (too long, includes stop words)

✓ white-label-sdk-case-study
   (concise, keyword-focused)

✓ elsaai-white-label-sdk
   (customer name + keyword)
```

### Step 9: Structured Data (Optional)

**For case studies and articles:**

**Add JSON-LD schema markup:**
```json
{
  "@context": "https://schema.org",
  "@type": "Article",
  "headline": "White-Label SDK Case Study: ElsaAI Reduces Returns 38%",
  "description": "Learn how ElsaAI reduced fashion returns by 38%...",
  "author": {
    "@type": "Organization",
    "name": "GlamYouUp"
  },
  "datePublished": "2024-11-16",
  "dateModified": "2024-11-16"
}
```

**For case studies specifically:**
```json
{
  "@context": "https://schema.org",
  "@type": "CaseStudy",
  "name": "ElsaAI White-Label SDK Implementation",
  "description": "How ElsaAI reduced returns by 38%...",
  "result": "38% reduction in return rate, $805K annual savings"
}
```

---

## Quality Validation

**Before outputting optimized content:**

### Keyword Optimization

- [ ] **Primary keyword in title:** Natural integration
- [ ] **Primary keyword in first 100 words:** Organic mention
- [ ] **Primary keyword in 2+ H2s:** Natural distribution
- [ ] **Keyword density 0.5-2%:** Not over-optimized
- [ ] **Secondary keywords included:** Natural variations

### Technical SEO

- [ ] **Title length 50-60 chars:** SERP-friendly
- [ ] **Meta description 150-160 chars:** Compelling, includes keyword
- [ ] **H1 unique:** Only one H1 (title)
- [ ] **H2 structure logical:** 3-7 main sections
- [ ] **URL slug optimized:** Keyword-focused, concise

### Content Quality

- [ ] **Readability maintained:** No keyword stuffing
- [ ] **Natural language:** SEO doesn't hurt readability
- [ ] **Educational value preserved:** Optimization adds, doesn't subtract
- [ ] **Internal links relevant:** 3-5 links, natural anchor text

### Image SEO

- [ ] **Alt text descriptive:** Includes keyword if natural
- [ ] **File names optimized:** Descriptive, keyword-relevant
- [ ] **File size <200KB:** Compressed for performance

---

## Output Format

### Optimized Content File
```markdown
---
# SEO Metadata
title: "White-Label SDK Case Study: ElsaAI Reduces Returns 38%"
meta_description: "Learn how ElsaAI reduced fashion returns by 38% using a white-label SDK. Implementation guide, metrics, and ROI analysis from a $200M luxury marketplace."
url_slug: "elsaai-white-label-sdk-case-study"
target_keyword: "white-label SDK"
secondary_keywords: ["enterprise fashion SDK", "white-label fit recommendation", "luxury fashion returns"]
canonical_url: "https://glamyouup.com/blog/elsaai-white-label-sdk-case-study"

# Content metadata
content_type: "case study"
pillar: "Product capabilities"
word_count: 1450
readability_score: "Grade 10"
keyword_density: "1.2%"

# SEO scores
title_score: "95/100"
meta_score: "90/100"
heading_score: "85/100"
keyword_score: "88/100"
internal_link_score: "90/100"

# Optimization notes
optimizations_applied:
  - "Added primary keyword to title"
  - "Optimized H2 headings with keyword variations"
  - "Added 4 internal links to related content"
  - "Created meta description with keyword and result"
  - "Optimized image alt text"

created: "2024-11-16"
status: "optimized"
---

# White-Label SDK Case Study: ElsaAI Reduces Returns 38%

{Optimized content with all SEO improvements applied}

---

## Internal Links Added

1. [co-branded vs white-label comparison](/blog/co-branded-vs-white-label)
   - Anchor: "co-branded fit widgets"
   - Context: Explaining ElsaAI's previous approach

2. [reducing fashion returns guide](/blog/reduce-returns-guide)
   - Anchor: "reducing fashion returns"
   - Context: Broader problem context

3. [enterprise SDK pricing](/pricing/enterprise)
   - Anchor: "enterprise SDK pricing"
   - Context: Call-out to product page

4. [luxury fashion e-commerce trends](/blog/luxury-ecommerce-trends)
   - Anchor: "luxury fashion brands"
   - Context: Industry background
```

### SEO Checklist Report
```markdown
## SEO Optimization Report

**Content:** elsaai-white-label-sdk-case-study.md
**Date:** 2024-11-16
**Target keyword:** white-label SDK

### Optimization Summary

**Title Optimization:**
- Original: "Our Customer Success Story with ElsaAI"
- Optimized: "White-Label SDK Case Study: ElsaAI Reduces Returns 38%"
- Score: 95/100 (keyword included, 55 chars, compelling)

**Meta Description:**
- Created: "Learn how ElsaAI reduced fashion returns by 38% using a white-label SDK. Implementation guide, metrics, and ROI analysis from a $200M luxury marketplace."
- Score: 90/100 (158 chars, keyword included, actionable)

**Heading Structure:**
- H1: 1 (title with keyword) ✓
- H2: 5 (3 include keyword variations) ✓
- H3: 8 (support H2s) ✓

**Keyword Integration:**
- Primary keyword mentions: 18 (1.2% density) ✓
- First 100 words: ✓
- H1: ✓
- H2s: 3/5 ✓
- Meta description: ✓

**Internal Links:**
- Total: 4 ✓
- Anchor text optimized: ✓
- Relevant targets: ✓

**Image Optimization:**
- Images: 3
- Alt text added: 3/3 ✓
- File names optimized: 3/3 ✓

**URL Slug:**
- Created: "elsaai-white-label-sdk-case-study"
- Keyword included: ✓
- Length: 4 words ✓

### Recommendations

1. **Consider adding:**
   - FAQ schema for common questions
   - Breadcrumb navigation
   - Related articles section

2. **Monitor performance:**
   - Track ranking for "white-label SDK"
   - Monitor click-through rate from SERP
   - Adjust if needed after 30 days

### Overall SEO Score: 89/100

**Ready for publication.**
```

---

## Edge Cases

### Low Keyword Opportunity

**If keyword search volume is low:**
- Optimize anyway (long-tail can convert well)
- Focus on related keywords
- Prioritize internal linking for authority

### Keyword Doesn't Fit Naturally

**If forcing keyword hurts readability:**
- Use keyword variations instead
- Prioritize quality over keyword placement
- Include keyword in meta/title only

### Existing Content Update

**If optimizing published content:**
- Preserve existing URL (avoid 301 redirects)
- Update modified date
- Add redirect if URL must change
- Monitor rankings after update

### Competitive Keyword

**If keyword highly competitive:**
- Focus on long-tail variations
- Build authority with internal links
- Create comprehensive content (longer, deeper)
- Consider secondary keywords

---

## Success Metrics

**Optimization quality:**
- SEO score: >85/100 (technical compliance)
- Readability maintained: No keyword stuffing
- Natural integration: Keywords flow organically

**Search performance (post-publication):**
- Ranking: Position 1-10 for target keyword (within 90 days)
- Click-through rate: >3% from SERP
- Organic traffic: {target sessions/month}

**Conversion performance:**
- Time on page: >3 minutes (engaging content)
- Scroll depth: >75% (readers finish article)
- Conversion rate: {demos/downloads per 100 visitors}

---

## Usage Example

**Input:**
```
Draft: threads/marketing/campaigns/luxury-validation-nov-2024/5-actions/drafts/elsaai-case-study/draft.md
Keyword: "white-label SDK"
Secondary: ["enterprise fashion SDK", "luxury fashion returns"]
```

**Process:**
```
1. Read draft:
   - Title: "Our Customer Success Story with ElsaAI"
   - Word count: 1,450
   - Current keyword mentions: 5 (sparse)

2. Optimize title:
   - New: "White-Label SDK Case Study: ElsaAI Reduces Returns 38%"
   - Keyword: ✓
   - Length: 55 chars ✓

3. Create meta description:
   - "Learn how ElsaAI reduced fashion returns by 38% using a white-label SDK..."
   - 158 chars ✓

4. Optimize headings:
   - H2: "Why Luxury Fashion Brands Need White-Label Fit Recommendations"
   - H2: "Implementing a White-Label SDK: Technical Approach"
   - Added keyword variations ✓

5. Add keywords naturally:
   - First 100 words: Added "white-label SDK" ✓
   - Body: 18 total mentions (1.2% density) ✓

6. Internal linking:
   - Added 4 links to related content ✓
   - Descriptive anchor text ✓

7. Image optimization:
   - Alt text: "White-label SDK integration showing branded fit widget"
   - File: white-label-sdk-screenshot.jpg ✓

8. URL slug:
   - Created: "elsaai-white-label-sdk-case-study" ✓

9. Validate:
   - SEO score: 89/100 ✓
   - Readability: Maintained ✓
   - Ready for publication ✓

10. Output:
    - Save: threads/marketing/campaigns/luxury-validation-nov-2024/5-actions/drafts/elsaai-case-study/optimized.md
    - Flag: ops/today.md for final approval
```

---

## Remember

**SEO optimization is:**
- Making great content discoverable
- Integrating keywords naturally
- Structuring content for search engines AND readers
- Building authority through internal linking

**SEO optimization is NOT:**
- Keyword stuffing
- Sacrificing readability for rankings
- Gaming search algorithms
- Over-optimizing at expense of quality

**Success = Content that ranks AND educates effectively.**