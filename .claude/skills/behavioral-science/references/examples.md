# Worked Examples

Before/after examples demonstrating each mode.

---

## AUDIT Mode Examples

### Example 1: SaaS Landing Page

**Input:** Landing page headline and hero section

```
Headline: "The Best Project Management Tool"
Subhead: "Teams love our software"
CTA: "Learn More"
```

**Output:**

## Behavioral Audit: SaaS Landing Page Hero

**Overall Score:** 4/18

| Dimension | Score | Gap |
|-----------|-------|-----|
| Loss Framing | 0/3 | No loss language, pure gain frame |
| Social Proof | 1/3 | Vague "teams love" with no specifics |
| Scarcity | 0/3 | No urgency whatsoever |
| Concrete Language | 0/3 | "Best" is abstract, unmeasurable |
| Friction | 1/3 | "Learn More" is weak, unclear next step |
| Anchoring | 2/3 | N/A for hero (would apply to pricing) |

### Top 3 Opportunities

1. **Concrete Language**: "The Best Project Management Tool" → "Ship 40% faster with half the meetings"
2. **Social Proof**: "Teams love our software" → "Join 2,847 engineering teams who ship on time"
3. **Friction**: "Learn More" → "Start Free — No Credit Card"

### Quick Wins (< 5 min)
- [ ] Replace "Best" with specific metric
- [ ] Add number to social proof claim
- [ ] Change CTA to action verb with friction reducer

---

### Example 2: Cold Email Subject Line

**Input:** "Following up on my previous email"

**Output:**

## Behavioral Audit: Email Subject Line

**Overall Score:** 2/18

| Dimension | Score | Gap |
|-----------|-------|-----|
| Loss Framing | 0/3 | No loss element |
| Social Proof | 0/3 | No proof |
| Scarcity | 0/3 | No urgency |
| Concrete Language | 1/3 | At least it's clear |
| Friction | 1/3 | Easy to read but no hook |
| Anchoring | 0/3 | N/A |

### Top 3 Opportunities

1. **Curiosity**: Create information gap → "The metric [Company] is missing"
2. **Loss Frame**: Add stakes → "You're losing $X to [problem]"
3. **Distinctiveness**: Break pattern → "Ignore this if you've solved [problem]"

### Quick Wins
- [ ] Delete "Following up" — never use this phrase
- [ ] Lead with insight or curiosity hook

---

## CREATE Mode Examples

### Example 1: Cold Email for B2B SaaS

**Context:** Analytics tool targeting Series B founders

**Output:**

## Cold Email: Series B Analytics Outreach

**Subject:** The dashboard gap killing Series B companies

Hey [Name],

I've been studying what separates Series B companies that nail their metrics from those that drown in dashboards.

The pattern: successful ones track 3 metrics obsessively. The rest track 30 and act on none.

[Similar Company] was in the second camp until Q2. They cut to 3 metrics, and their board meetings went from 4 hours to 45 minutes.

Quick question — do you know which 3 metrics actually predict your next round?

[Signature]

---
### Applied Biases

| Element | Bias | Why |
|---------|------|-----|
| Subject line | Curiosity + Loss | "Gap killing" creates info gap with stakes |
| Opening | Pattern break | No "hope this finds you well" |
| Middle | Social Proof | Peer company with specific result |
| CTA | Micro-commitment | Question, not meeting request |

### Alternatives to Test
- Subject A: "The 3 metrics that predict your Series C"
- Subject B: "[Similar Company]'s board meeting secret"
- CTA A: "Curious which 3?"
- CTA B: "Worth a 10-min call to find out?"

---

### Example 2: Pricing Page Headline

**Context:** Project management SaaS, targeting mid-market

**Output:**

## Pricing Page: Headline Options

**Option A (Loss Frame):**
"Stop losing 5 hours per project to status meetings"

**Option B (Social Proof + Concrete):**
"2,847 teams ship 40% faster. Here's how much it costs."

**Option C (Anchoring):**
"Replace your $150K project manager with a $49/month tool"

---
### Applied Biases

| Option | Primary Bias | Secondary |
|--------|--------------|-----------|
| A | Loss Aversion | Concrete (5 hours) |
| B | Social Proof | Concrete (40%, specific number) |
| C | Anchoring | Loss (replace = stop paying) |

### Recommendation
Test A vs C. Both leverage loss psychology. C has stronger anchor but may not resonate if audience isn't comparing to headcount.

---

## FIX Mode Examples

### Example 1: Low Email Open Rates

**Symptom:** 12% open rate on outbound sequence (benchmark: 25%+)

**Diagnosis:** Subject lines lack curiosity and distinctiveness. Generic "checking in" language.

### Before
```
Subject: Following up on [Product]
Subject: Quick question about your team
Subject: Can we schedule a call?
```

### After
```
Subject: The $400K mistake I see at companies your size
Subject: Why [Competitor] customers are switching
Subject: Closing your file Friday
```

### Rationale
- **Bias applied:** Curiosity (info gap), Loss Aversion, Scarcity
- **Mechanism:** Info gap creates need to resolve; loss frame 2x more motivating than gain; deadline creates urgency
- **Expected impact:** +50-100% open rate based on similar transformations

### Verify
- **Metric:** Open rate
- **Baseline:** 12%
- **Target:** 20-25%
- **Test:** A/B test new subjects vs control for 200 sends each

---

### Example 2: Pricing Page Conversion Drop

**Symptom:** 40% of visitors reach pricing page but only 2% convert

**Diagnosis:** Price shown in isolation without anchor. No decoy tier. Cheapest option too functional.

### Before
```
Starter: $29/mo - 5 users, all features
Pro: $79/mo - 20 users, all features  
Enterprise: Contact us
```

### After
```
Starter: $29/mo - 3 users, core features only, no integrations
Pro: $79/mo - 20 users, all features, priority support ← MOST POPULAR
Enterprise: $199/mo - Unlimited, SSO, dedicated success manager

"That's less than $4/user/day — cheaper than their coffee"
```

### Rationale
- **Bias applied:** Decoy Effect, Anchoring, Temporal Reframe
- **Mechanism:** 
  - Starter now clearly limited → Pro looks valuable
  - Enterprise visible → Pro seems reasonable
  - Per-day framing → price feels smaller
- **Expected impact:** +30-50% Pro tier selection based on Ariely decoy research

### Verify
- **Metric:** Tier distribution, overall conversion rate
- **Baseline:** 60% Starter / 35% Pro / 5% Enterprise
- **Target:** 30% Starter / 55% Pro / 15% Enterprise
- **Test:** Implement and measure for 2 weeks, 500+ pricing page views

---

### Example 3: Cart Abandonment

**Symptom:** 68% cart abandonment rate

**Diagnosis:** No urgency, no loss frame, payment friction (no BNPL)

### Before
```
Your Cart
- [Product] - $299
[Checkout Button]
```

### After
```
Your Cart (reserved for 15:00)
- [Product] - $299

⚠️ 3 other people are viewing this item

[Checkout Button]

Or pay $75/month with Klarna — first payment in 30 days
```

### Rationale
- **Bias applied:** Scarcity (time limit), Social Proof (others viewing), Present Bias (BNPL)
- **Mechanism:**
  - Cart expiration creates urgency
  - Others viewing triggers FOMO
  - BNPL defers pain of payment
- **Expected impact:** -15-25% abandonment based on e-commerce benchmarks

### Verify
- **Metric:** Cart abandonment rate, checkout completion
- **Baseline:** 68% abandonment
- **Target:** 50-55% abandonment
- **Test:** Implement elements sequentially to isolate impact

---

### Example 4: Weak CTA

**Symptom:** CTA button gets views but <1% click rate

**Diagnosis:** Generic "Submit" language, no value proposition, friction words

### Before
```
[Submit]
```

### After
```
[Start My Free Trial →]
No credit card required • Cancel anytime
```

### Rationale
- **Bias applied:** Friction Reduction, Loss Aversion (via risk reversal)
- **Mechanism:**
  - "My" creates ownership
  - "Free Trial" removes cost objection
  - Supporting text removes remaining friction
- **Expected impact:** +100-200% CTR based on button copy testing data

### Verify
- **Metric:** Button CTR
- **Baseline:** 0.8%
- **Target:** 2-3%
- **Test:** A/B test for 1,000 impressions minimum

---

## Pattern: FIX Mode Checklist

When applying FIX mode, always:

1. ☐ Quantify the symptom (metric + current value)
2. ☐ Identify which bias principle is violated/missing
3. ☐ Show exact before/after content
4. ☐ Explain mechanism (why the fix works)
5. ☐ Cite evidence where available
6. ☐ Define verification criteria
7. ☐ Suggest test methodology