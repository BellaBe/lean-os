# Landing Page Behavioral Playbook

Deep implementation guide for applying behavioral science to landing pages.

---

## The Behavioral Landing Page Framework

Every section has a job. Every element uses a specific bias. Nothing is neutral.

---

## Above the Fold

### Headline

**Job:** Stop the scroll, create interest, promise value

**Primary Biases:** Loss Framing, Distinctiveness, Curiosity

**Formula Options:**

| Type | Formula | Example |
|------|---------|---------|
| Loss | "Stop [losing/wasting/missing] [valuable thing]" | "Stop losing 5 hours/week to scattered docs" |
| Curiosity | "[Unexpected statement] about [their problem]" | "The real reason your demos don't convert" |
| Distinctive | "[Contrarian claim] that [benefit]" | "The CRM that deletes itself when it's not helping" |
| Concrete | "[Specific outcome] in [timeframe]" | "Ship 40% faster in 30 days" |

**Testing Rule:** Always A/B test loss vs gain framing. Loss usually wins for action-oriented pages.

### Subheadline

**Job:** Support headline with proof or clarity

**Primary Biases:** Social Proof, Specificity

**Formula:** "[Number] [companies like them] [achieve specific outcome]"

**Examples:**
- "2,847 B2B companies increased conversion 40% in 60 days"
- "Join 12,000 engineering teams shipping faster"
- "The analytics platform trusted by Stripe, Notion, and Linear"

### Above-Fold Social Proof

**Job:** Instant credibility before scroll

**Primary Biases:** Peer Social Proof

**Implementation:**
- Logos of recognizable companies (5-7 max)
- "Trusted by [industry] leaders"
- Aggregate metric if impressive ("500M+ events processed")

**Hierarchy:** Peer logos > Industry leaders > Aggregate numbers > Trust badges

### Primary CTA

**Job:** Clear next step, minimal friction

**Primary Biases:** Commitment, Loss Aversion

**Button Text Options:**
| Type | Text | When to Use |
|------|------|-------------|
| Gain | "Start [getting benefit]" | Aspirational products |
| Loss | "Stop [losing outcome]" | Problem-focused products |
| Low commitment | "See how it works" | Complex/expensive products |
| Direct | "Get started free" | Self-serve, low friction |

**Design Rules:**
- Contrast color (pops from page)
- Action-oriented verb
- No friction words ("Submit", "Register")
- Supporting text reduces anxiety ("No credit card required")

---

## Body Sections

### Problem Section

**Job:** Agitate pain, create motivation

**Primary Biases:** Loss Framing, Pain Amplification

**Structure:**
```
[State the problem clearly]

Without [solution], you're:
- Losing [specific loss 1]
- Missing [specific opportunity]
- Falling behind [benchmark/competitor]

Every [time period], that's [compounded loss].
```

**Psychology:** Increase motivation through loss awareness before presenting solution.

### Solution Section

**Job:** Present your answer to the problem

**Primary Biases:** Anchoring, Framing

**Structure:**
```
[Anchor to expensive alternative]
"Most companies hire a team ($150k/year) or cobble together tools ($X/month)."

[Present your solution]
"[Product] gives you [outcome] for [fraction of anchor]."

[Contrast]
"That's [X]x less than [alternative] with [better outcome]."
```

**Psychology:** Anchoring makes your price seem reasonable by comparison.

### How It Works

**Job:** Reduce uncertainty, show path to value

**Primary Biases:** Operational Transparency, Friction Reduction

**Structure:**
```
Step 1: [Simple action] (takes [X minutes])
Step 2: [Next step]
Step 3: [Outcome achieved]
```

**Rules:**
- 3 steps max (more = complex = friction)
- Include time estimates (reduces uncertainty)
- End step is the outcome, not a product action

### Proof Section

**Job:** Validate claims, reduce risk

**Primary Biases:** Social Proof, Authority, Messenger Effect

**Elements (use 2-3):**

| Element | Bias | Implementation |
|---------|------|----------------|
| Testimonials | Peer Social Proof | Quote + name + role + similar company |
| Logos | Social Proof | Recognizable brands in their space |
| Case studies | Specificity | Specific metrics achieved |
| Reviews | Authority | G2/Capterra scores |
| Press | Authority | "Featured in [publication]" |

**Testimonial Formula:**
"[Specific result]. [What they tried before]. [Why this worked]. [Emotional benefit]."

Not: "Great product, love the team!"
But: "We reduced churn 23% in 60 days. We'd tried 3 other tools that required too much setup. This just worked. Now I actually enjoy looking at our dashboards."

### Pricing Section

**Job:** Guide to optimal choice, minimize sticker shock

**Primary Biases:** Anchoring, Choice Architecture, Decoy Effect

**Structure:**

```
[Value anchor]
"Companies save an average of $50k/year with [Product]"

[3 tiers]
Starter: $X/mo - [Limited]
Pro: $Y/mo - [Full features] <- MOST POPULAR
Enterprise: $Z/mo - [Everything + premium]

[Temporal reframe]
"That's just $Y/day - less than [relatable thing]"
```

**Tier Optimization:**
- Starter: Functional but limited (creates upgrade desire)
- Pro: The target tier (most value, highlighted)
- Enterprise: High anchor (makes Pro look reasonable)

**Decoy Option:** Add a tier that's almost as expensive as Pro but with much less value. This makes Pro the obvious choice.

### Final CTA Section

**Job:** Close the page strong, create action

**Primary Biases:** Scarcity, Commitment, Peak-End Rule

**Structure:**
```
[Summary of value]
Get [outcome 1], [outcome 2], and [outcome 3].

[Scarcity if real]
[X] spots remaining this month / Offer ends [date]

[Strong CTA button]

[Risk reversal]
30-day money-back guarantee. No questions asked.
```

**Psychology:** End strong (peak-end rule), add urgency if legitimate, remove risk.

---

## Behavioral Elements

### Progress Indicators
**Bias:** Commitment
**Implementation:** Show progress as user scrolls or fills forms

### Exit Intent Popup
**Biases:** Loss Aversion, Scarcity

**Structure:**
```
"Wait - before you go..."

[Offer something valuable or different]
- Lead magnet
- Smaller commitment option
- Last-chance deal

[Different CTA than main page]
```

### Live Activity Indicators
**Bias:** Social Proof

**Examples:**
- "Sarah from Acme just signed up"
- "142 people viewing this page"
- "1,234 signups today"

**Rule:** Must be real. Fake activity = trust killer.

### Trust Signals
**Biases:** Authority, Social Proof

**Elements:**
- Security badges (if handling sensitive data)
- Review scores (G2, Capterra)
- Certifications (SOC 2, GDPR)
- Money-back guarantee

---

## Templates

### Problem-Agitation-Solution (PAS)

Best for: Pain-point focused products, B2B SaaS

```
HEADLINE: [Loss Frame + Concrete Number]
"Stop losing [specific amount] every [time period] to [problem]"

SUBHEAD: [Social Proof - Specific]
"Join [X,XXX] [relevant audience] who fixed this"

PROBLEM: [Deprivation Frame]
"Every day without [solution], you're:
- Losing [specific loss 1]
- Missing [specific opportunity]
- Falling behind [competitor/benchmark]"

AGITATION: [Future Pacing - Negative]
"In 6 months, that's [compounded loss]. While your competitors..."

SOLUTION: [Effort Transparency]
"After [X iterations/years], we built [solution] to [outcome]"

HOW IT WORKS: [Operational Transparency]
Step 1: [action] (X minutes)
Step 2: [action]
Step 3: [outcome]

PROOF: [Social + Messenger]
[Testimonial with specific result]
[Logo bar]

PRICING: [Decoy + Anchor]
[3 tiers with recommendation]

CTA: [Friction Reduction + Scarcity]
[Button] + "No credit card" + [Scarcity if real]

RISK REVERSAL:
"[X]-day money-back guarantee"
```

### Before-After-Bridge (BAB)

Best for: Transformation products, courses, coaching

```
HEADLINE: [Curiosity + Outcome]
"How [specific audience] [achieve result] in [timeframe]"

BEFORE: [Current State Pain]
"Right now, you're probably:
- Struggling with [problem]
- Frustrated by [friction]
- Worried about [fear]"

AFTER: [Future State - Picturable]
"Imagine [specific day-in-life]:
- [Concrete benefit 1]
- [Measurable benefit 2]
- [Emotional benefit 3]"

BRIDGE: [How - With Effort]
"[Product] is the result of [effort story]..."

PROOF: [Messenger + Specifics]
[Testimonial with transformation]
[Featured in...]

OFFER: [Stacked Value + Scarcity]
"What you get:
- [Core product] (worth $X)
- [Bonus 1] (worth $Y)
Total value: $[sum] / Your investment: $[Price]"

"Only [X] spots available"

CTA: [Action + Urgency]
```

---

## Audit Checklist

### Above Fold
- [ ] Headline uses loss frame or distinctive claim
- [ ] Subhead includes specific social proof
- [ ] Logos/proof visible without scroll
- [ ] Single primary CTA
- [ ] CTA button is contrast color
- [ ] No friction words in CTA

### Body
- [ ] Problem section quantifies loss
- [ ] Solution anchored to alternative cost
- [ ] How it works has 3 or fewer steps
- [ ] Testimonials include specific results
- [ ] Pricing has 3 tiers with recommendation

### Close
- [ ] Final CTA section is strong
- [ ] Scarcity included (if real)
- [ ] Risk reversal present
- [ ] Page ends on high note

### Behavioral Elements
- [ ] Exit intent captures abandoners
- [ ] Trust signals present
- [ ] No competing CTAs
- [ ] Forms are minimal fields
