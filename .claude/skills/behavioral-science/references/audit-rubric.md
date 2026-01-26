# Behavioral Audit Rubric

Detailed scoring criteria for content audits. Use alongside SKILL.md AUDIT mode.

---

## Scoring Dimensions

### 1. Urgency/Scarcity (0-3)

| Score | Criteria | Examples |
|-------|----------|----------|
| 0 | No time or quantity limits whatsoever | "Buy our product" |
| 1 | Vague urgency without specifics | "Limited time offer", "Don't miss out" |
| 2 | Specific deadline OR quantity limit | "Ends Friday at midnight" or "Only 12 seats" |
| 3 | Both time + quantity + visible indicator | "3 left at this price - Sale ends in 2:34:17" |

**Evidence base:**
- Lee 2012: Scarcity = +37% purchase intent
- E-commerce testing: Scarcity messages = 2.9% revenue lift (highest of 29 tactics)

**Red flags:**
- Fake countdown timers that reset
- "Only X left!" that never changes
- Perpetual "limited time" offers

**Upgrade paths:**
- 0→1: Add any urgency language
- 1→2: Make it specific and verifiable
- 2→3: Add real-time indicator (countdown, stock level)

---

### 2. Loss Framing (0-3)

| Score | Criteria | Examples |
|-------|----------|----------|
| 0 | Only benefits listed, no loss frame | "Get faster results" |
| 1 | Mentions risks vaguely | "Don't fall behind" |
| 2 | Clear "without this, you lose X" | "Companies without this lose 23% of leads" |
| 3 | Quantified loss + emotional impact | "Every day without X costs you $847 and puts you 3 months behind competitors" |

**Evidence base:**
- Tversky/Kahneman: Losses feel 2x as painful as equivalent gains
- Gonzales 1988: Loss frame = 61% compliance vs gain frame = 39%

**Common mistakes:**
- Loss frame that sounds threatening rather than helpful
- Exaggerated losses that strain credibility
- All loss framing with no relief/solution

**Upgrade paths:**
- 0→1: Add any consequence of inaction
- 1→2: Quantify the loss with real numbers
- 2→3: Add emotional dimension + compound impact over time

---

### 3. Social Proof (0-3)

| Score | Criteria | Examples |
|-------|----------|----------|
| 0 | No social proof | [Nothing] |
| 1 | Vague claims | "Trusted by thousands", "Industry leader" |
| 2 | Specific numbers or names | "47,382 teams use X", "Used by Stripe and Airbnb" |
| 3 | Implied proof + specifics + relevance | Visible usage indicators, "92% of Fortune 500 banks use X" |

**Evidence base:**
- Coulter 2012: Implied social proof 20% more effective than stated
- Cialdini hotel study: Specific floor reference = +14% compliance

**Hierarchy of proof strength:**
1. Implied (visible usage, user-generated) — strongest
2. Specific + relevant ("CTOs like you")
3. Specific numbers
4. Named customers
5. Vague claims — weakest

**Upgrade paths:**
- 0→1: Add any social proof
- 1→2: Add specific numbers or recognizable names
- 2→3: Make proof specific to reader's context + add implied elements

---

### 4. Concrete Language (0-3)

| Score | Criteria | Examples |
|-------|----------|----------|
| 0 | Abstract claims throughout | "Premium quality", "Best-in-class solution" |
| 1 | Some specifics mixed with abstract | "Save time with our fast platform" |
| 2 | Measurable claims | "Save 4 hours per week", "15-minute setup" |
| 3 | Picturable, sensory language throughout | "In 15 minutes, you'll watch your first report generate automatically" |

**Evidence base:**
- GEICO: "15 minutes could save you 15%" — specific beats vague
- Song 2009: Hard-to-process language = perceived risk

**Abstract language red flags:**
- "Premium" / "Quality" / "Best"
- "Innovative" / "Revolutionary" / "Cutting-edge"
- "Seamless" / "Streamlined" / "Optimized"
- "Leverage" / "Synergy" / "Solutions"

**Upgrade paths:**
- 0→1: Replace ONE abstract claim with specific
- 1→2: Make all claims measurable
- 2→3: Add sensory/picturable details throughout

---

### 5. Friction Reduction (0-3)

| Score | Criteria | Examples |
|-------|----------|----------|
| 0 | Multiple steps, unclear CTA, friction | 3 CTAs, long forms, unclear next step |
| 1 | Clear CTA, some friction remains | "Get Started" but 5-field form |
| 2 | Single clear action, minimal friction | One button, email-only signup |
| 3 | Frictionless + progress indicators | One-click, social login, "Step 1 of 2" |

**Evidence base:**
- Each form field = ~5-10% conversion drop
- Amazon 1-click patent: friction removal = major competitive advantage

**Friction audit checklist:**
- [ ] How many clicks to complete desired action?
- [ ] How many form fields?
- [ ] Is the primary CTA obvious?
- [ ] Are there competing CTAs?
- [ ] Is progress shown?
- [ ] Can user save/return?

**Upgrade paths:**
- 0→1: Establish single clear CTA
- 1→2: Reduce form to essentials (name, email only)
- 2→3: Add social login, progress indicators, save state

---

### 6. Value Anchoring (0-3)

| Score | Criteria | Examples |
|-------|----------|----------|
| 0 | Price shown in isolation | "$99/month" with no context |
| 1 | Basic comparison present | "Cheaper than competitors" |
| 2 | Decoy option or clear anchor | 3-tier pricing with middle highlighted |
| 3 | Full price architecture | Decoy + anchor + temporal reframe + value stack |

**Evidence base:**
- Ariely Economist: Decoy shifted preference by 52 percentage points
- Williams-Sonoma: $429 breadmaker doubled $279 sales

**Price architecture elements:**
- Anchor: High reference point shown first
- Decoy: Dominated option making target look better
- Temporal reframe: $X/day instead of $X/year
- Value stack: List everything included to justify price

**Upgrade paths:**
- 0→1: Add any comparison point
- 1→2: Implement 3-tier pricing with clear target
- 2→3: Add decoy + temporal reframe + full value stack

---

## Score Interpretation

| Score Range | Assessment | Action |
|-------------|------------|--------|
| **15-18** | Strong | Minor optimizations only |
| **10-14** | Good foundation | 2-3 key improvements needed |
| **5-9** | Significant gaps | Prioritize top 3 dimensions |
| **0-4** | Major rewrite | Multiple fundamentals missing |

---

## Content-Type Specific Rubrics

### Landing Pages

**Must-haves:**
- [ ] Above-fold value proposition with concrete language (Dim 4 ≥ 2)
- [ ] Social proof visible without scrolling (Dim 3 ≥ 2)
- [ ] Single primary CTA (Dim 5 ≥ 2)
- [ ] Urgency if offer-based (Dim 1 ≥ 2)

**Bonus elements:**
- [ ] Loss-framed problem section
- [ ] Operational transparency (how it works)
- [ ] Price anchoring if pricing shown
- [ ] Risk reversal (guarantee, trial)

**Priority order:** Friction → Concrete → Social → Urgency → Loss → Anchor

---

### Emails

**Must-haves:**
- [ ] Subject line curiosity hook or loss frame
- [ ] Single clear CTA (Dim 5 ≥ 2)
- [ ] Concrete benefit in first 2 lines (Dim 4 ≥ 2)

**Bonus elements:**
- [ ] P.S. with scarcity/urgency
- [ ] Implied social proof
- [ ] Temporal reframe for any pricing

**Priority order:** Concrete → Friction → Urgency → Loss → Social → Anchor

---

### Sales Pages (Long-form)

**Must-haves:**
- [ ] Above-fold loss frame or curiosity hook
- [ ] Multiple social proof types (testimonials, logos, numbers)
- [ ] Price anchoring with decoy
- [ ] Risk reversal prominent
- [ ] Urgency near CTA

**Bonus elements:**
- [ ] Effort transparency (origin story, process)
- [ ] Future self projection
- [ ] Zeigarnik loops throughout (open loops closed at CTA)

**Priority order:** Loss → Social → Anchor → Concrete → Urgency → Friction

---

### Ads (Social/Display)

**Must-haves:**
- [ ] Pattern interrupt in first 1-2 seconds
- [ ] Concrete claim or specific number
- [ ] Single clear action

**Bonus elements:**
- [ ] Curiosity hook
- [ ] Social proof indicator
- [ ] Urgency if space allows

**Priority order:** Concrete → Urgency → Social → Loss → Friction → Anchor

---

## Extended Audit Output Template

```markdown
## Behavioral Audit: [Content Name]

**Content Type:** [Landing page / Email / Sales page / Ad / Other]
**Date:** [Date]
**Overall Score:** X/18

### Dimension Scores

| Dimension | Score | Notes |
|-----------|-------|-------|
| Urgency/Scarcity | X/3 | |
| Loss Framing | X/3 | |
| Social Proof | X/3 | |
| Concrete Language | X/3 | |
| Friction Reduction | X/3 | |
| Value Anchoring | X/3 | |

### Score Interpretation
[15-18: Strong / 10-14: Good / 5-9: Gaps / 0-4: Rewrite]

### Top 3 Opportunities

**1. [Highest impact dimension]**
- Current state: "[Quote or description]"
- Gap: [What's missing]
- Recommendation: "[Specific improved version]"
- Expected impact: [Evidence-based estimate]

**2. [Second priority]**
- Current state: ...
- Gap: ...
- Recommendation: ...
- Expected impact: ...

**3. [Third priority]**
- Current state: ...
- Gap: ...
- Recommendation: ...
- Expected impact: ...

### Quick Wins (< 5 min each)
- [ ] [Small change 1]
- [ ] [Small change 2]
- [ ] [Small change 3]

### Requires Deeper Work
- [ ] [Larger change 1] — estimated effort: [X hours]
- [ ] [Larger change 2] — estimated effort: [X hours]

### Biases Present (Working Well)
- [Bias]: [How it's being used effectively]

### Biases NOT Used (and why appropriate/inappropriate)
- [Bias]: [Reason for absence - deliberate or gap?]

### Testing Recommendations
1. [A/B test suggestion with hypothesis]
2. [Second test suggestion]
```

---

## Audit Shortcuts by Symptom

| If you see... | Check dimension | Likely issue |
|---------------|-----------------|--------------|
| High bounce rate | Concrete (4), Friction (5) | Abstract claims, unclear CTA |
| Traffic but no conversions | Friction (5), Urgency (1) | Too many steps, no reason to act now |
| Price page drop-off | Anchoring (6) | Price in isolation, no context |
| Low engagement | Loss (2), Social (3) | No stakes, no validation |
| "Sounds too good" feedback | Concrete (4), Social (3) | Vague claims, no proof |
