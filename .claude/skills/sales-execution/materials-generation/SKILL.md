---
name: materials-generation
description: Generate sales collateral (pitch deck, one-pager, call scripts, email templates) from Canvas, narrative, and ICP with problem-first ordering and stage-appropriate messaging
allowed-tools: [Read, Write]
---

# Materials Generation Subskill

## Purpose

Generate ready-to-use sales materials from strategic inputs with automatic impact scoring for autonomous deployment vs human review.

**Operates on**: ONE product per invocation
**Enforces**: Problem-first ordering, feature-to-benefit translation, stage-appropriate messaging
**Autonomous deployment**: Impact score < 0.8

## Input Parameters

**Required**:
- `product`: Product name (from Canvas)
- `segment`: Segment name (from ICP)
- `canvas_path`: `strategy/canvas/`
- `icp_path`: `research/customer/icp/{segment}-icp.md`

**Optional**:
- `narrative_path`: `threads/sales/narrative/{segment}-*.md` (recommended)
- `stage`: "mvp" | "growth" | "enterprise" (defaults to Canvas stage if present)
- `force_regenerate`: boolean (skip change detection, always regenerate)

## Workflow

### 1. Load Context

**Read Canvas files** from `strategy/canvas/`:
- `customer-segments.md` - Who you're selling to
- `problem.md` - Pain points to emphasize
- `solution.md` - What you're selling
- `unique-value-proposition.md` - Why you're different
- `key-metrics.md` - Quantified outcomes

**Read ICP** from `research/customer/icp/{segment}-icp.md`:
- Observable firmographics/technographics
- Buyer personas (economic, technical, end-user)
- Qualification questions
- Problem signals

**Read Sales Narrative** from `artifacts/sales/{segment}/narratives/` (optional):
- `{segment}-economic-buyer.md` - Economic buyer messaging
- `{segment}-technical-buyer.md` - Technical buyer messaging
- `{segment}-objection-lib.md` - Objection handling library

**Read Optional Data**:
- `research/customer/icp/prospect-list.csv` - Real prospect examples
- `research/customers/proof-points.md` - Customer success stories
- `research/market/industry-stats.md` - Industry data

**Handle missing files**:
- Canvas missing: ERROR (required)
- ICP missing: Use generic B2B SaaS patterns + flag for customization
- Narrative missing: Extract from Canvas + flag "TODO: Refine with sales-narrative skill"
- Optional data missing: Generate with placeholders + TODO markers

---

### 2. Detect Changes & Score Impact

**Compare to previous generation** (if exists):

Check `artifacts/sales/{segment}/` for existing files:
- If files exist: Compare Canvas/ICP/Narrative last-modified timestamps
- If no files exist: First-time generation (impact score = 0.0, auto-deploy)

**Calculate impact score (0.0 - 1.0)**:

**High Impact (>= 0.8)** - Requires human review:
- ICP target segment change (different customer profile)
- Pricing structure change (>20% difference in tiers/pricing)
- Value proposition reframing (quantitative to qualitative shift)
- Problem angle shift (focus on different pain point)
- Stage change (MVP → Growth or Growth → Enterprise)

**Medium Impact (0.5 - 0.79)**:
- Added significant proof points (new case studies, major metrics)
- Buyer persona refinement (new decision-makers)
- Messaging tone shift (casual to formal or vice versa)

**Low Impact (< 0.5)** - Auto-deploy safe:
- Statistics updated (industry data refreshed)
- Wording improvements (grammar, clarity)
- Email template variants added
- Call script timing adjustments
- Formatting changes

**If `force_regenerate=true`**: Skip change detection, set impact=0.0 (always auto-deploy)

**Example scoring**:
```
Changes:
- ICP customer_size changed from "50-200" to "200-500" → +0.4 (major)
- Added industry stat to problem narrative → +0.1 (minor)
- Fixed typo in one-pager → +0.0 (trivial)
Total: 0.5 (Medium impact - requires review)
```

---

### 3. Generate Artifacts

Create four sales materials following frameworks from references:

#### 3.1 Pitch Deck (`pitch-deck.md`)

**Structure** (10-15 slides, one idea per slide):

```markdown
# Slide 1: Title + Problem Hook
[Product Name]
[One-sentence problem hook from Canvas]

# Slide 2: Problem Statement
[3-5 quantified pain points from Canvas problem.md]

# Slide 3: Current Alternatives
[How prospects solve today, why they fail - from Canvas]

# Slide 4: Your Solution
[High-level approach from Canvas solution.md]

# Slide 5: How It Works
[3-step process with feature → benefit mapping]

# Slide 6-7: Demo/Screenshots
[Visual proof - TODO if not available]

# Slide 8: Value Proposition
[Quantified benefits from Canvas key-metrics.md]

# Slide 9: Why You/Team
[Credibility signals - from Canvas or stage-appropriate]

# Slide 10: Traction
[Stage-appropriate metrics: MVP=pilots, Growth=customers, Enterprise=scale]

# Slide 11: Pricing
[From Canvas or ICP-based pricing guidance]

# Slide 12: Next Steps
[Clear CTA: trial, pilot, demo]
```

**Quality checks**:
- [ ] Problem (slides 2-3) comes BEFORE solution (slides 4-5)
- [ ] Each feature has corresponding benefit
- [ ] No vague claims ("best-in-class" without proof)
- [ ] Stage-appropriate language (MVP="pilot results", Enterprise="200+ customers")
- [ ] One idea per slide (not walls of text)

See `references/pitch-deck-structure.md` for detailed guidance.

---

#### 3.2 One-Pager (`one-pager.md`)

**Format constraints**:
- Single page when printed (8.5" x 11")
- Readable in B&W (no color dependency)
- 12pt+ font throughout
- Skimmable in 30 seconds

**Structure**:
```markdown
# [HEADLINE: Problem in 10 words or less]

## The Problem
- [Pain point 1 from Canvas]
- [Pain point 2 from Canvas]
- [Pain point 3 from Canvas]

## The Solution
- [How you solve it - approach not features]
- [Key differentiator from Canvas UVP]
- [For: ICP summary]

## Key Benefits
- [Quantified benefit 1 from Canvas metrics]
- [Quantified benefit 2]
- [Quantified benefit 3]

## How It Works
1. [Step 1 - customer perspective]
2. [Step 2]
3. [Step 3]

## Pricing
[Starting point or "Contact us"]

## Contact
[Company] | [Website] | [Email] | [Phone]
[CTA: Book a 15-minute demo]
```

**Quality checks**:
- [ ] Fits on one page
- [ ] Readable in B&W (no colored text)
- [ ] Problem before solution
- [ ] Benefits quantified (not vague)
- [ ] No jargon requiring explanation

See `references/one-pager-rules.md` for layout examples.

---

#### 3.3 Call Scripts (`call-scripts.md`)

**Three scripts with strict timing**:

**Discovery Call (30 minutes)**:
```markdown
# Discovery Call Script (30 minutes)

## Opening (1 minute)
[Permission-based opening]

## Qualification (5 minutes)
[ICP qualification questions - yes/no or numeric]
[If disqualified → polite exit]

## Problem Exploration (15 minutes) ← MOST IMPORTANT
[Open-ended discovery questions]
[Listen for pain, quantify impact]

## Light Pitch (5 minutes)
[Map your solution to THEIR problems mentioned]

## Next Steps (4 minutes)
[Schedule demo with specific times]
```

**Demo Call (30 minutes)**:
```markdown
# Demo Call Script (30 minutes)

## Recap (2 minutes)
[Confirm problems from discovery]

## Customized Demo (15 minutes) ← MOST IMPORTANT
[Problem 1 → Feature → Benefit → Their impact (5 min)]
[Problem 2 → Feature → Benefit → Their impact (5 min)]
[Problem 3 → Feature → Benefit → Their impact (5 min)]

## Objection Handling (5 minutes)
[Common objections + responses from references]

## Pricing (3 minutes)
[Their tier + ROI calculation]

## Close (5 minutes)
[Direct ask: trial, pilot, or contract]
```

**Follow-up Call (15 minutes)**:
```markdown
# Follow-up Call Script (15 minutes)

## Opening (1 minute)
[Reference previous conversation specifics]

## Address Questions (8 minutes)
[Answer open questions with proof]

## Provide Proof (2 minutes)
[Case study, data, ROI calculation]

## Clear Ask (4 minutes)
[Specific proposal: trial, pilot, contract]
[Timeline and next steps]
```

**Quality checks**:
- [ ] Time limits specified per segment
- [ ] Questions map to ICP qualification criteria
- [ ] Problem explored before solution pitched
- [ ] Objection responses prepared
- [ ] Clear CTA in each script

See `references/call-script-timing.md` for detailed timing management.

---

#### 3.4 Email Templates (`email-templates.md`)

**Max 5 sentences per email** (hard constraint):

**Cold Outreach**:
```markdown
Subject: [Problem-focused, not company name]

Line 1: [Problem hook with quantification]
Line 2: [Brief solution + credibility signal]
Line 3: [Specific ask for 15-min call]
Line 4: [Easy out]
Signature
```

**Follow-up Sequence**:
```markdown
# Follow-up #1 (3 days later)
Subject: Re: [Original subject]
[Value-add: stat, insight, article]
[How it relates to them]
[Soft ask]

# Follow-up #2 (1 week later)
Subject: [New angle on problem]
[Different problem perspective]
[How you solve it]
[Direct ask + calendar link]

# Follow-up #3 (2 weeks later - breakup)
Subject: Should I close your file?
[Acknowledge no response]
[Easy out or timeline question]
[Leave door open]
```

**Meeting Request** (after initial contact):
```markdown
Subject: 15 min to discuss [specific problem]?

[Thank them + reference their response]
[What you'll cover]
[Specific time options or calendar link]
```

**Post-Demo Follow-up**:
```markdown
Subject: Great chatting - [Their Company] + [Your Company]

[Thank + specific reference from demo]
[Attach resources promised]
[Quantified next step proposal]
[Make it easy]
```

**Quality checks**:
- [ ] Max 5 sentences (count them)
- [ ] Subject line is problem-focused
- [ ] Specific not generic (uses ICP characteristics)
- [ ] One CTA per email
- [ ] No vague claims without quantification

See `references/email-formulas.md` for detailed formulas and A/B testing.

---

### 4. Quality Validation

**Run all quality checks** before finalizing:

**Problem-First Ordering**:
- [ ] Pitch deck: Problem (slides 2-3) before solution (slides 4-5)
- [ ] One-pager: Problem section before solution section
- [ ] Call scripts: Problem exploration before pitch
- [ ] Emails: Problem hook in line 1

**Feature-to-Benefit Translation**:
- [ ] Every feature has corresponding benefit
- [ ] Benefits explain "why it matters"
- [ ] Impact quantified where possible
- [ ] No standalone feature lists

**Vague Claim Detection**:
- [ ] No "best", "leading", "innovative" without proof
- [ ] All claims either quantified or flagged as TODO
- [ ] Comparisons are specific
- [ ] Credibility signals are concrete

**Format Compliance**:
- [ ] Pitch deck: One idea per slide
- [ ] One-pager: Fits one page, readable B&W
- [ ] Call scripts: Time limits realistic
- [ ] Emails: Max 5 sentences each

**Stage-Appropriate Messaging**:
- [ ] MVP: "5 pilot customers" not "thousands of users"
- [ ] Growth: "35 customers" not "scrappy startup"
- [ ] Enterprise: "200+ customers" not "founder-led"

See references for detailed quality criteria:
- `references/problem-first-ordering.md`
- `references/feature-to-benefit-translation.md`
- `references/stage-appropriate-messaging.md`

**Flag quality issues** as TODOs in output:
```markdown
TODO: Quantify this claim - "significant improvement" → "35% reduction"
TODO: Translate feature to benefit - "AI-powered" → "{quantified outcome}"
TODO: Add proof point - "industry-leading" needs supporting data
```

---

### 5. Version & Deploy

**Based on impact score**, deploy or flag for review:

#### Impact Score < 0.8 (Auto-Deploy)

1. **Archive old materials** (if they exist):
   - Move existing files from `artifacts/sales/{segment}/materials/` to `artifacts/sales/{segment}/materials/archive/{date}/`
   - Only if files already exist (first-time generation skips this)

2. **Write files** to `artifacts/sales/{segment}/materials/`:
   - `pitch-deck.md`
   - `one-pager.md`
   - `call-scripts.md`
   - `email-templates.md`

3. **Return success**:
   ```
   Status: Deployed
   Location: artifacts/sales/{segment}/materials/
   Segment: {segment}
   Impact: {score} (Low - auto-deployed)
   Files: [pitch-deck.md, one-pager.md, call-scripts.md, email-templates.md]
   ```

---

#### Impact Score >= 0.8 (Requires Review)

1. **Write files** to `artifacts/sales/{segment}/drafts/{date}/`:
   - `pitch-deck.md`
   - `one-pager.md`
   - `call-scripts.md`
   - `email-templates.md`
   - `REVIEW-NEEDED.md` explaining high-impact changes

2. **Flag in ops dashboard**:
   ```markdown
   # ops/today.md

   ## 🚨 Review Required: Sales Materials

   **Segment**: {segment}
   **Impact Score**: {score} (High)
   **Reason**: {changes that triggered high score}
   **Location**: artifacts/sales/{segment}/drafts/{date}/
   **Action**: Review materials, approve deployment, or request changes
   ```

3. **Return pending status**:
   ```
   Status: Pending Review
   Location: artifacts/sales/{segment}/drafts/{date}/
   Segment: {segment}
   Impact: {score} (High - requires review)
   Reason: {specific high-impact changes}
   Action: Review at artifacts/sales/{segment}/drafts/{date}/REVIEW-NEEDED.md
   ```

---

## Example Impact Scoring

### Example 1: Low Impact (0.2)
```
Changes:
- Updated industry statistic in problem slide (2023 data → 2024 data)
- Fixed typo in one-pager ("recieve" → "receive")
- Adjusted call script demo timing (16 min → 15 min)

Impact Calculation:
- Stat update: +0.1
- Typo fix: +0.0
- Timing tweak: +0.1
Total: 0.2

Action: Auto-deploy
```

### Example 2: Medium Impact (0.6)
```
Changes:
- Added major case study ({Customer} {X}% {metric} improvement)
- Buyer persona refinement (added "{New Role}" to ICP)
- New email template variant for enterprise prospects

Impact Calculation:
- Major proof point: +0.3
- Persona refinement: +0.2
- Template variant: +0.1
Total: 0.6

Action: Auto-deploy (under 0.8 threshold)
```

### Example 3: High Impact (0.9)
```
Changes:
- ICP target changed from "50-200 employees" to "200-500 employees"
- Pricing increased from $400/month to $800/month
- Value prop shifted from "reduce costs" to "increase revenue"

Impact Calculation:
- ICP segment change: +0.4
- Pricing change (100%): +0.3
- Value prop reframe: +0.2
Total: 0.9

Action: Flag for human review (exceeds 0.8 threshold)
```

---

## Output Structure

```
artifacts/sales/
├── {segment-1}/
│   ├── materials/
│   │   ├── pitch-deck.md
│   │   ├── one-pager.md
│   │   ├── call-scripts.md
│   │   ├── email-templates.md
│   │   └── archive/
│   ├── narratives/
│   │   ├── {segment}-economic-buyer.md
│   │   ├── {segment}-technical-buyer.md
│   │   └── {segment}-objection-lib.md
│   ├── sequences/
│   │   └── archive/
│   └── drafts/
│       └── {date}/ (if high impact)
│           ├── pitch-deck.md
│           ├── one-pager.md
│           ├── call-scripts.md
│           ├── email-templates.md
│           └── REVIEW-NEEDED.md
├── {segment-2}/
└── {segment-3}/
```

---

## Error Handling

**Canvas missing**: STOP - Canvas is required input
```
ERROR: Canvas not found at strategy/canvas/
Required files: problem.md, solution.md, unique-value-proposition.md
Action: Create Canvas first using canvas-design skill
```

**ICP missing**: Use generic patterns + flag
```
WARNING: ICP not found at research/customer/icp/{segment}-icp.yaml
Using generic B2B SaaS ICP patterns
Action: Generate ICP using icp-generator skill for better targeting
```

**Narrative missing**: Extract from Canvas + flag
```
WARNING: Sales narrative not found at threads/sales/narrative/
Extracting messaging from Canvas directly
Action: Refine messaging using sales-narrative skill for better storytelling
```

**Invalid segment**: ERROR
```
ERROR: Segment '{segment}' not found
Available segments: [list from existing Canvas directories]
```

---

## References

This subskill relies on detailed frameworks in `references/`:

- `pitch-deck-structure.md` - 10-15 slide structure, examples
- `one-pager-rules.md` - Format constraints, layouts
- `call-script-timing.md` - Timing management per call type
- `email-formulas.md` - Cold outreach, follow-up patterns
- `problem-first-ordering.md` - Correct vs wrong ordering
- `feature-to-benefit-translation.md` - Translation patterns
- `stage-appropriate-messaging.md` - MVP vs Growth vs Enterprise
- `objection-handling-patterns.md` - Common objections + responses

**Note**: These references are in the parent `sales-materials` skill directory and are accessible via relative path.

---

## Success Criteria

Well-generated materials enable:
1. Pitch deck presentable in 15 minutes without edits
2. One-pager understandable in 30-second skim
3. Call scripts keep calls on time and on track
4. Email templates get >20% response rate (industry benchmark)
5. All materials pass quality checks (problem-first, quantified, specific)
