---
name: behavioral-science
description: Applies behavioral science to any revenue touchpoint. Triggers on "persuade", "convert", "landing page", "email", "outbound", "sales", "copy", "audit", "review content", "increase conversions", "campaign", "pitch", "demo". Detects context automatically and delivers targeted behavioral recommendations.
---

# Behavioral Intelligence Skill

Apply the right psychological lever, for the right person, at the right moment.

## How This Skill Works

This is a **targeting system**, not a knowledge base. Given any revenue task, it:
1. Detects the touchpoint (where)
2. Identifies the goal (what outcome)
3. Profiles the audience (who)
4. Selects optimal biases (which levers)
5. Delivers context-specific implementation (how)

---

## Mode Detection

| Mode | Signal Words | Output |
|------|--------------|--------|
| **AUDIT** | review, audit, analyze, critique, assess, evaluate, score, check | Scored assessment + gaps + opportunities |
| **CREATE** | write, create, draft, generate, make, build, compose | Content with bias annotations + alternatives |
| **FIX** | fix, improve, optimize, boost, increase, rewrite, make better | Before/after transformation + rationale |

**Detection priority:**
- "Review this email" → AUDIT
- "Write an email" → CREATE
- "Fix this headline" / "Improve conversions" → FIX

---

## Step 1: Detect Touchpoint

| Touchpoint | Signal Words | Load Reference |
|------------|--------------|----------------|
| **OUTBOUND** | email sequence, cold email, outreach, prospecting | `references/playbooks/outbound.md` |
| **LANDING** | landing page, website, conversion, signup, pricing page | `references/playbooks/landing-page.md` |
| **SALES** | demo, call, meeting, proposal, negotiation, objection | `references/playbooks/sales.md` |
| **ADS** | ad, campaign, Facebook, LinkedIn, display, retargeting | `references/playbooks/ads.md` |
| **CONTENT** | blog, headline, copy, subject line, article | Use inline templates |

---

## Step 2: Identify Goal

| Goal | Primary Biases |
|------|----------------|
| **GET ATTENTION** | Distinctiveness, Curiosity, Pattern Interrupt |
| **CREATE INTEREST** | Social Proof, Reciprocity, Authority |
| **DRIVE ACTION** | Scarcity, Loss Aversion, Friction Reduction |
| **CLOSE DEAL** | Commitment, Anchoring, Social Proof |
| **RETAIN/EXPAND** | Sunk Cost, Commitment, Reciprocity |

---

## Step 3: Profile Audience

| Persona | Effective Biases | Less Effective |
|---------|------------------|----------------|
| **Executive** | Authority, Scarcity, Social Proof | Detailed arguments |
| **Technical** | Proof, Specificity, Logic | Pure social proof |
| **Risk-Averse** | Loss Framing, Guarantees | Aspirational framing |
| **Innovative** | Distinctiveness, Exclusivity | Herd behavior |

---

## The Core 10 Biases

1. **Loss Aversion**: Frame benefits as losses avoided (~2x impact)
2. **Scarcity/Urgency**: Limited time/quantity triggers action (must be real)
3. **Social Proof**: Specific numbers from relevant peers beat vague claims
4. **Anchoring**: First number shapes all comparisons
5. **Commitment/Consistency**: Small yeses lead to big yeses
6. **Reciprocity**: Give value first, ask second
7. **Distinctiveness**: Different gets remembered (Von Restorff)
8. **Framing**: Same info, different presentation = different decision
9. **Peak-End Rule**: Experiences judged by peak moment + ending
10. **Choice Architecture**: Defaults, decoys, ordering shape choice

Full catalog (40+ biases): [references/biases-catalog.md](references/biases-catalog.md)

---

## AUDIT Mode

### Dimensions

| Dimension | Check |
|-----------|-------|
| Loss Framing | Benefits framed as losses? Quantified? |
| Social Proof | Specific, relevant proof present? |
| Scarcity | Real time/quantity constraints? |
| Concrete Language | Measurable, picturable claims? |
| Friction | Single clear action path? |
| Anchoring | Price/value contextualized? |

Full rubric with 0-3 criteria: [references/audit-rubric.md](references/audit-rubric.md)

### Process
1. Score each dimension 0-3
2. Calculate total (max 18)
3. Identify top 3 gaps
4. Provide specific fixes with priority

### Output Format

```markdown
## Behavioral Audit: [Content Name]

**Overall Score:** X/18

| Dimension | Score | Gap |
|-----------|-------|-----|
| Loss Framing | X/3 | |
| Social Proof | X/3 | |
| Scarcity | X/3 | |
| Concrete Language | X/3 | |
| Friction | X/3 | |
| Anchoring | X/3 | |

### Top 3 Opportunities
1. **[Bias]**: [Current] → [Recommended]

### Quick Wins (< 5 min)
- [ ] [Change 1]
- [ ] [Change 2]
```

---

## CREATE Mode

### Process
1. Detect touchpoint → load relevant playbook
2. Identify goal → select primary biases (max 3-4)
3. Profile audience → adjust tone/approach
4. Generate content with bias integration
5. Annotate which biases used where

### Output Format

```markdown
## [Content Type]: [Title]

[Full content]

---
### Applied Biases
| Element | Bias | Why |
|---------|------|-----|
| [Headline] | [Bias] | [Rationale] |

### Alternatives to Test
- [A/B variation 1]
- [A/B variation 2]
```

Templates: [references/templates.md](references/templates.md)

---

## FIX Mode

### Process
1. **Identify**: What's underperforming? (metric, element, symptom)
2. **Diagnose**: Which bias principle is violated or missing?
3. **Fix**: Apply correct pattern with specific rewrite
4. **Verify**: Define how to measure improvement

### Common Fixes

| Symptom | Diagnosis | Fix |
|---------|-----------|-----|
| Low open rates | No curiosity/distinctiveness | Rewrite subject with info gap or pattern break |
| Low click-through | Competing CTAs, no urgency | Single CTA + Zeigarnik loop |
| Price objections | No anchor set | Show value/alternative cost before price |
| Cart abandonment | Present bias not addressed | Add BNPL, cart expiration urgency |
| No responses | Asked before giving | Lead with value, ask question not meeting |
| Choosing cheapest tier | No decoy effect | Add dominated option near target |
| Low trust | Vague social proof | Add specific numbers, peer companies |

Full challenge → bias mapping: [references/selectors.md](references/selectors.md)

### Output Format

```markdown
## Fix: [Element/Issue]

**Symptom:** [What's underperforming]
**Diagnosis:** [Bias principle violated]

### Before
[Original content]

### After
[Fixed content]

### Rationale
- **Bias applied:** [Name]
- **Mechanism:** [Why this works]
- **Expected impact:** [Based on evidence]

### Verify
- **Metric:** [What to measure]
- **Baseline:** [Current state]
- **Target:** [Expected improvement]
- **Test:** [How to validate]
```

Examples: [references/examples.md](references/examples.md)

---

## Anti-Patterns

- **Stacking patterns**: Max 4-5 biases; more feels manipulative
- **Fake scarcity**: Trust dies permanently when discovered
- **Loss everywhere**: Creates anxiety, not action
- **Generic proof**: "Millions trust us" is ignored
- **Friction neglect**: Best copy can't overcome bad UX

Full anti-pattern catalog: [references/anti-patterns.md](references/anti-patterns.md)

---

## Quick Reference: Challenge → Biases

| Struggling with... | Lead with... |
|--------------------|--------------|
| Low open rates | Curiosity, Distinctiveness, Loss Frame |
| Low click rates | Single CTA, Zeigarnik, Urgency |
| Price objections | Anchoring, Temporal Reframe |
| "Why you?" | Distinctiveness, Social Proof |
| No responses | Reciprocity, Micro-commitment |
| Cart abandonment | Loss Aversion, Present Bias |
| Low trust | Messenger Effect, Operational Transparency |

---

## Reference Files

| Need | File |
|------|------|
| Full bias catalog (40+) | `references/biases-catalog.md` |
| Audit scoring criteria | `references/audit-rubric.md` |
| Bias selection matrices | `references/selectors.md` |
| Content templates | `references/templates.md` |
| What to avoid | `references/anti-patterns.md` |
| Worked examples | `references/examples.md` |
| Outbound sequences | `references/playbooks/outbound.md` |
| Landing pages | `references/playbooks/landing-page.md` |
| Sales conversations | `references/playbooks/sales.md` |
| Paid advertising | `references/playbooks/ads.md` |

---

## Boundaries

**In scope:** Landing pages, emails, ads, pricing pages, CTAs, sales messaging, outbound sequences

**Out of scope:** Dark patterns, deceptive claims, technical implementation, A/B test infrastructure