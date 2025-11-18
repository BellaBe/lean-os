---
name: outreach-sequencing
description: Generate multi-touch outreach cadences with email, phone, and LinkedIn touchpoints following Pete Kazanjy's founding sales framework for systematic prospect engagement
allowed-tools: [Read, Write]
---

# Outreach-Sequencing Subskill

## Purpose

Generate day-by-day outreach sequences with email, phone, and LinkedIn touchpoints following Pete Kazanjy's founding sales framework.

**Operates on**: ONE product per invocation
**Input**: Email templates + ICP segment + prospect list (optional)
**Output**: Day-by-day outreach sequence with personalization instructions

## Context

- Reads from: `artifacts/sales/{segment}/materials/email-templates.md`
- Reads from: `research/customer/icp/{segment}-icp.md` (segment characteristics)
- Reads from: `research/customer/prospects/{segment}-*.md` (optional - for personalization context)
- Writes to: `artifacts/sales/{segment}/sequences/`
  - Individual sequence files per prospect (e.g., `tier1-st-agni.md`)
  - Summary file: `ALL-SEQUENCES-SUMMARY.md`
  - Archives old sequences to `sequences/archive/{date}/` before generating new ones

## Key Workflows

### 1. Load Templates

**Read email templates**:
- Cold outreach email (Day 0)
- Follow-up emails (#1, #2, #3)
- Meeting request email
- Path: `artifacts/sales/{segment}/materials/email-templates.md`

**Read ICP segment characteristics**:
- Segment name and description
- Observable characteristics (size, geography, platform, etc.)
- Problem signals and pain points
- Path: `research/customer/icp/{segment}-icp.md`

**Read prospect list (optional)**:
- Company names for personalization
- Contact information
- Problem signals
- Path: `research/customer/prospects/{segment}-*.md`
- Used for: Auto-personalization instructions (company-specific inserts)

### 2. Determine Sequence Structure

**Pete Kazanjy's Framework** (Standard Sequence):

**Day 0: Initial Email**:
- Template: Cold Outreach #1 (Problem Hook)
- Goal: Get response or permission to continue
- Success: Reply (any response)
- Channel: Email

**Day 3: Follow-up #1**:
- Template: Follow-up #1 (Add Value/Insight)
- Goal: Provide additional value, remind of initial email
- Content: Industry insight, case study teaser, relevant stat
- Channel: Email

**Day 7: Follow-up #2**:
- Template: Follow-up #2 (Different Problem Angle)
- Goal: Approach from different angle if first problem didn't resonate
- Content: Alternative pain point, different benefit
- Channel: Email

**Day 10: Phone Call**:
- Script: Cold Call Discovery (15 min)
- Goal: Qualify fit, schedule demo if interested
- Voicemail: Reference email sequence ("I've sent a few emails about...")
- Channel: Phone

**Day 14: Follow-up #3 (Break-up Email)**:
- Template: Follow-up #3 (Break-up)
- Goal: Permission-based close, elicit response or remove from list
- Content: "Should I close your file?" approach
- Channel: Email

**Day 21: Final Touch** (Conditional):
- Template: Success Story / Case Study
- Condition: Only if relevant proof point available
- Goal: Last-chance value delivery
- Channel: Email

### 3. Channel Mix

**Email as Primary**:
- Most scalable
- Prospect controls when to engage
- Can be personalized at scale
- Measurable (open rates, reply rates)

**Phone as Critical**:
- Day 10 call is non-negotiable (Pete Kazanjy: "The phone is not dead")
- Higher quality conversations than email
- Cuts through noise
- Decision-makers respect persistence

**LinkedIn as Supplementary**:
- Connection request on Day 0 or Day 3
- View profile (creates notification) on Day 0
- InMail message (if no email response by Day 7)
- Not a replacement for email/phone

**Combination Pattern**:
```
Day 0: Email + LinkedIn view
Day 3: Email
Day 7: Email + LinkedIn connection request
Day 10: Phone call
Day 14: Email
Day 21: Email (if applicable)
```

### 4. Personalization Levels

**Level 1: Mass (Minimal Personalization)**:
- **Use**: Large prospect lists (100+ prospects)
- **Personalization**: Segment-level only
- **Template**: "{Segment problem} + generic value prop"
- **Example**: "DTC fashion brands typically struggle with 20-30% return rates due to sizing issues..."
- **Effort**: Low (no per-company research)
- **Response rate**: 1-3%

**Level 2: Auto-Personalized (Company-Specific Inserts)**:
- **Use**: Medium lists (20-50 prospects)
- **Personalization**: Company name + observable trait from prospect CSV
- **Template**: "Segment problem + {company_name} + {observed_trait}"
- **Example**: "ChicThreads, I noticed you're on Shopify and have a sizing guide - curious if return rates are still a challenge?"
- **Effort**: Medium (automated from prospect data)
- **Response rate**: 5-10%

**Level 3: Human-Personalized (Researched Custom Intro)**:
- **Use**: High-value targets (5-10 prospects, Tier 1 only)
- **Personalization**: Custom first line based on manual research
- **Template**: "Custom observation + segment problem + value prop"
- **Example**: "Sarah, saw your recent LinkedIn post about customer experience challenges. For DTC brands like ChicThreads, we've found that sizing issues drive 30% of returns - is that resonating with your team?"
- **Effort**: High (requires manual research per prospect)
- **Response rate**: 15-25%

**Personalization level rules**:
- If prospect_list_path provided AND list size > 100: Default to "mass"
- If prospect_list_path provided AND list size 20-50: Default to "auto"
- If prospect_list_path provided AND list size < 20: Recommend "human" (flag for manual research)
- If no prospect_list_path: Default to "mass" (segment-only)

### 5. Generate Sequence

**Output structure**:

```markdown
# Outreach Sequence: {Segment Name}

**Generated**: {date}
**Segment**: {segment_id}
**Personalization**: {mass|auto|human}
**Duration**: {days} days
**Channels**: Email, Phone, LinkedIn

---

## Sequence Overview

**Goal**: {segment goal - e.g., "Qualify DTC fashion brands with 20%+ return rates"}
**ICP**: {segment characteristics}
**Key Problem**: {primary pain point}
**Value Proposition**: {solution in 1 sentence}

**Success Metrics**:
- Response rate: {expected percentage based on personalization}
- Meeting booked rate: {expected percentage}
- Disqualification rate: {expected percentage}

---

## Day 0: Initial Email

**Channel**: Email
**Template**: Cold Outreach #1 (Problem Hook)
**Subject**: {subject line from template}
**Send Time**: Tuesday/Wednesday 10am local time

**Personalization Instructions**:
{Personalization level instructions}

**Email Body**:
{Template content with personalization tokens}

**Success Criteria**:
- Reply (any response) → Move to qualification
- Out of office → Note return date, resume sequence
- No response → Continue to Day 3

**LinkedIn Action** (optional):
- View prospect's LinkedIn profile (creates notification)
- Do NOT send connection request yet

---

## Day 3: Follow-up #1

{Repeat structure for each day}

---

## Response Handling

**If they respond at Day 0-3**: {instructions}
**If they respond at Day 7-10**: {instructions}
**If they respond at Day 14+**: {instructions}
**If they say "not interested"**: {instructions}
**If they say "not now"**: {instructions}
```

**Day-by-day details**:
- Day number and touchpoint name
- Channel (Email, Phone, LinkedIn)
- Template reference
- Subject line (for emails)
- Send time recommendations
- Personalization instructions (specific to level)
- Email body or phone script
- Success criteria (what indicates interest)
- Next steps (what to do if they respond)

**Response handling section**:
- What to do if they respond at different stages
- Qualification questions to ask
- Meeting scheduling instructions
- Disqualification criteria
- Re-engagement timing (if "not now")

## Input Parameters

**Required**:
- `product`: Product name (e.g., "GlamYouUp", "Detekta")
- `segment`: ICP segment name (e.g., "dtc-fashion-smb", "ria-50-200-employees")

**Optional**:
- `prospect_list_path`: Path to prospect CSV (default: none - generates segment-level sequence)
  - Used for: Auto-personalization token identification (company names, traits)
  - Note: Does NOT generate per-prospect sequences (too many files)
- `personalization_level`: "mass" | "auto" | "human" (default: "auto" if prospect list provided, "mass" if not)
- `sequence_type`: "standard" | "aggressive" | "patient" (default: "standard")
  - standard: Day 0/3/7/10/14/21 (most common)
  - aggressive: Day 0/2/4/7/10/14 (faster follow-ups, for hot leads)
  - patient: Day 0/5/10/15/21/30 (slower, relationship-building, for cold outreach)

## Output

**Location**: `artifacts/sales/{segment}/sequences/`

**Before writing new sequences**:
1. Check if sequences already exist in `artifacts/sales/{segment}/sequences/`
2. If they exist, move all files to `artifacts/sales/{segment}/sequences/archive/{date}/`
3. Write new sequences to the root sequences/ directory

**Files generated**:
- Individual prospect sequences: `tier{N}-{company-slug}.md` (one per prospect)
- Summary: `ALL-SEQUENCES-SUMMARY.md` (overview of all sequences)

**Individual sequence file structure**:
1. **Header**: Prospect metadata (company, contact, match score, problem signals)
2. **Sequence Overview**: Cadence, persona strategy, ROI calculation
3. **Day-by-day touchpoints**: Email 1-5 with personalization
4. **Why This Works**: Explanation for each email approach

## Sequence Variations

### Standard Sequence (Day 0/3/7/10/14/21)

**Use case**: Most B2B SaaS products, standard sales cycle (30-60 days)

**Timing**:
- Day 0: Initial email
- Day 3: Follow-up #1 (3 days later)
- Day 7: Follow-up #2 (4 days later)
- Day 10: Phone call (3 days later)
- Day 14: Break-up email (4 days later)
- Day 21: Final touch (7 days later, if applicable)

**Total duration**: 21 days
**Touchpoints**: 5-6 (5 emails + 1 phone, or 6 if final touch)

**Pros**:
- Balanced cadence (not too aggressive, not too slow)
- Enough time for prospects to see multiple emails
- Phone call at midpoint (after 3 emails, before break-up)

**Cons**:
- May be too slow for hot leads
- May be too fast for very cold outreach

### Aggressive Sequence (Day 0/2/4/7/10/14)

**Use case**: Hot leads, inbound requests, event follow-ups, competitor switch scenarios

**Timing**:
- Day 0: Initial email
- Day 2: Follow-up #1 (2 days later)
- Day 4: Follow-up #2 (2 days later)
- Day 7: Phone call (3 days later)
- Day 10: Follow-up #3 (3 days later)
- Day 14: Final touch (4 days later, if applicable)

**Total duration**: 14 days
**Touchpoints**: 5-6 (same as standard, compressed)

**Pros**:
- Faster response (good for hot leads)
- Capitalizes on prospect urgency
- Shorter sales cycle

**Cons**:
- Can feel pushy if prospect not interested
- Less time for prospect to evaluate
- May trigger spam filters (too frequent)

**When to use**:
- Inbound lead (filled out form, downloaded content)
- Event attendee (met at conference, webinar)
- Referral (warm introduction from mutual contact)
- Competitor mention (prospect mentioned competitor on social)

### Patient Sequence (Day 0/5/10/15/21/30)

**Use case**: Very cold outreach, senior executives, long sales cycles (6+ months), high-value accounts

**Timing**:
- Day 0: Initial email
- Day 5: Follow-up #1 (5 days later)
- Day 10: Follow-up #2 (5 days later)
- Day 15: Phone call (5 days later)
- Day 21: Follow-up #3 (6 days later)
- Day 30: Final touch (9 days later, if applicable)

**Total duration**: 30 days
**Touchpoints**: 5-6 (same as standard, spread out)

**Pros**:
- Less aggressive (better for cold outreach)
- More time for prospect to research
- Relationship-building approach

**Cons**:
- Slower response (may lose hot leads)
- Longer to disqualify (wasted time on bad fits)
- Prospect may forget initial email

**When to use**:
- C-level executives (very busy, need time)
- Enterprise accounts (long decision cycles)
- Completely cold lists (no prior engagement)
- High-value, strategic accounts (worth the wait)

## Personalization Examples

### Mass Personalization (Segment-Level)

**Email example**:
```
Subject: 20% return rates killing margins?

Hi {FirstName},

DTC fashion brands typically face 20-30% return rates, with sizing issues being the #1 driver. We've helped brands like Stitch Fix and Rent the Runway reduce returns by 35% using AI-powered virtual sizing.

Curious if this resonates with your team at {Company}?

Best,
{YourName}
```

**Personalization tokens**:
- `{FirstName}`: Decision-maker first name (from prospect list or generic "there")
- `{Company}`: Company name (from prospect list)
- Segment problem: "20-30% return rates"
- Generic value prop: "reduce returns by 35%"

**Effort**: 2-3 minutes per prospect (just fill in name/company)

### Auto-Personalized (Company-Specific)

**Email example**:
```
Subject: ChicThreads - 20% return rates?

Hi Sarah,

I noticed ChicThreads is on Shopify and has a detailed sizing guide on your site - curious if you're still seeing high return rates despite this?

We've helped similar DTC fashion brands reduce returns by 35% using AI-powered virtual sizing that goes beyond static sizing charts.

Quick 15-min call to share what we're seeing?

Best,
{YourName}
```

**Personalization tokens**:
- `{FirstName}`: Sarah (from prospect list or research)
- `{Company}`: ChicThreads (from prospect list)
- `{ObservedTrait}`: "on Shopify" + "has sizing guide" (from prospect research CSV)
- Segment problem: "high return rates"
- Specific value prop: "AI-powered virtual sizing" (goes beyond their current approach)

**Effort**: 5-10 minutes per prospect (research observable trait, insert into template)

### Human-Personalized (Researched Custom Intro)

**Email example**:
```
Subject: Your LinkedIn post on CX challenges

Hi Sarah,

Saw your recent LinkedIn post about improving customer experience at ChicThreads. For DTC fashion brands with great products like yours, we've found that sizing issues are often the hidden CX killer - 30% of returns are fit-related, driving up costs and frustrating customers.

We've helped similar brands reduce returns by 35% with AI-powered virtual sizing. Would love to share a quick case study from a brand your size.

15 minutes this week?

Best,
{YourName}
```

**Personalization tokens**:
- Custom intro: "Saw your recent LinkedIn post on CX challenges" (requires manual LinkedIn research)
- `{Company}`: ChicThreads
- `{ObservedTrait}`: "great products" + "DTC fashion" (contextual compliment)
- Segment problem: "sizing issues" (tied to their CX focus)
- Specific ask: "15 minutes this week?" (time-bound)

**Effort**: 15-20 minutes per prospect (LinkedIn research, custom first line, polish)

**Flags for human personalization**:
```markdown
**HUMAN PERSONALIZATION REQUIRED**:
- [ ] Research prospect's LinkedIn activity (recent posts, comments, profile updates)
- [ ] Find company-specific observation (product launch, funding, hiring, news mention)
- [ ] Write custom first line referencing observation
- [ ] Connect observation to segment problem
- [ ] Review for authenticity (does it sound researched or forced?)
```

## Constraints

### Email Template Length

**Hard limit**: 5 sentences per email (includes subject line as sentence 1)

**Rationale**: Pete Kazanjy research shows shorter emails get higher response rates

**Example validation**:
```
✓ Subject (1) + 4 sentences = 5 sentences total
✗ Subject (1) + 6 sentences = 7 sentences (TOO LONG)
```

**Enforcement**:
- Count sentences in email body
- If > 4 sentences (excluding subject), flag for editing
- Suggest combining sentences or removing fluff

### Phone Call References Email

**Requirement**: Phone script MUST reference email sequence

**Example**:
```
"Hi Sarah, this is {Your Name} from {Company}. I've sent you a couple emails about reducing return rates for DTC fashion brands - wanted to try to reach you by phone. Is now a good time for a quick conversation?"
```

**NOT allowed**:
```
✗ "Hi Sarah, calling to talk about our product..." (no email reference)
```

**Rationale**: Establishes continuity, reminds prospect of prior touchpoints

### Break-up Email Timing

**Requirement**: Break-up email MUST be Day 14 or later

**Rationale**:
- Give prospect time to respond (at least 2 weeks)
- Too early = impatient, unprofessional
- Day 14 = 4 prior touchpoints (3 emails + 1 phone), enough attempts

**Example validation**:
```
✓ Standard sequence: Day 14 break-up (after Day 0/3/7/10)
✓ Aggressive sequence: Day 10 break-up (after Day 0/2/4/7)
✗ Aggressive sequence: Day 7 break-up (TOO EARLY - only 2 emails)
```

### Personalization Matches List Size

**Requirement**: Personalization level MUST match prospect list size

**Rules**:
- List size 100+: Use "mass" (auto or human too time-consuming)
- List size 20-100: Use "auto" (mass too generic, human too slow)
- List size <20: Use "human" or "auto" (worth the effort for small list)

**Example validation**:
```
✓ 150 prospects + "mass" personalization
✓ 40 prospects + "auto" personalization
✓ 10 prospects + "human" personalization
✗ 150 prospects + "human" personalization (TOO SLOW - 150 * 20 min = 50 hours)
✗ 10 prospects + "mass" personalization (TOO GENERIC - waste high-value targets)
```

**Override**: User can override, but skill should warn about mismatch

## Sequence Output Example

**File: tier1-st-agni.md**

```markdown
# Outreach Sequence: St. Agni (Australia)

**Candidate Rank:** #1 (Match Score: 0.85)
**Contact:** Lara Bluett, Director & Co-Founder
**LinkedIn:** https://au.linkedin.com/in/lara-bluett-a78756b8
**Company:** St. Agni (Contemporary fashion, Byron Bay, Australia)
**Team Size:** 26 employees
**Revenue:** $5M (perfect ICP fit)
**Problem Signals:** Very strong (3/3) - sizing issues, return policy, customer complaints

---

## Sequence Overview

**Cadence:** 5 emails over 22 days
- Email 1: Day 0 (Initial outreach)
- Email 2: Day 4 (Value-add follow-up)
- Email 3: Day 11 (Different angle)
- Email 4: Day 18 (Case study proof)
- Email 5: Day 22 (Breakup email)

**Persona Strategy:** Founder/Designer (operational decision-maker, design-conscious, fit-critical brand)
**Angle:** Design ethos alignment + customer sizing pain point validation
**ROI Calculation:** $5M GMV × 30% est. return rate × 40% reduction × $45 = $27,000 annual savings for $3,588/year = 7.5× ROI

---

## Email 1: Initial Outreach (Day 0)

**Subject:** St. Agni's "considered design" + customer sizing intelligence

**Body:**

Hi Lara,

I love St. Agni's approach to "considered design and precise tailoring"—it's exactly the kind of brand that benefits from body shape intelligence. I noticed customer reviews mention sizing can be tricky ("runs narrow", "size up"), which is classic for contemporary fashion where fit is crucial.

We help brands like St. Agni reduce return rates by 40% through body shape + seasonal color analysis from a single selfie—giving your customers personalized guidance ("This silhouette flatters your body shape") and giving you production intelligence ("35% of your customers are hourglass, prioritize fitted styles"). For St. Agni at $5M revenue, that's $27K in annual savings plus customer data to inform your next collection.

Would 15 minutes make sense to show you how we align with St. Agni's considered design ethos?

Best,
[Your Name]

**Why This Works:**
- References St. Agni's specific brand language ("considered design and precise tailoring")
- Validates problem from customer reviews (sizing issues confirmed)
- Aligns with design-conscious founder (not just ROI, but brand ethos)
- Quantifies their specific savings ($27K for $5M revenue)

---

## Email 2-5: Follow-up Sequence

[Additional emails follow similar structure with prospect-specific personalization]

**Note**: Each sequence file contains 5 fully personalized emails with:
- Subject lines tailored to the prospect
- Email body with company-specific references
- "Why This Works" explanation for each email
- Timing guidance (Day 0, 4, 11, 18, 22)

```

---

**File: ALL-SEQUENCES-SUMMARY.md**

```markdown
# Outreach Sequences Summary: DTC Fashion SMB

**Generated**: 2024-11-16
**Segment**: dtc-fashion-smb
**Total Sequences**: 10
**Personalization Level**: Human (Tier 1), Auto (Tier 2-3)

---

## Tier 1: High-Priority Targets (Human Personalized)

1. **St. Agni** (Australia, $5M revenue) - Lara Bluett, Director & Co-Founder
2. **Aligne** (UK, $8M revenue) - Katie Llewellyn, Co-Founder
3. **Omnes** (UK, $6M revenue) - Hannah Traylen, Founder
4. **House of Sunny** (UK, $10M revenue) - Sunny Williams, Creative Director

## Tier 2: Medium-Priority Targets (Auto-Personalized)

[List of 4-6 prospects with key details]

## Tier 3: Standard Targets (Mass Personalized)

[List of remaining prospects]

---

## Campaign Tracking

**Start Date**: Week of Nov 18, 2024
**Expected Response Rate**: 15-25% (Tier 1), 8-12% (Tier 2), 3-5% (Tier 3)
**Demo Booking Target**: 2-4 demos from 10 prospects
**Campaign Thread**: threads/sales/campaigns/2024-11-18-dtc-beta-outreach/
```

---

## Response Handling

### If they respond at Day 0-3 (Early Response)

**Indicates**: High interest, active problem

**Next steps**:
1. Qualify fit (company size, platform, geography)
2. Confirm problem (return rates >15%, sizing issues)
3. Schedule discovery call (30 min)
4. Send calendar invite immediately

**Questions to ask**:
- "What's your current return rate?"
- "What percentage is fit/sizing related?"
- "What have you tried so far to reduce returns?"
- "Who else should be involved in evaluating a solution like this?"

### If they respond at Day 7-10 (Mid Response)

**Indicates**: Moderate interest, problem may not be urgent

**Next steps**:
1. Acknowledge delay (they're busy, appreciate response)
2. Qualify fit (faster qualification, they're lukewarm)
3. Offer quick demo (15 min, not 30 min)
4. If interested, schedule; if not, offer to reconnect later

### If they respond at Day 14+ (Late Response)

**Indicates**: Low urgency, might be polite response to break-up email

**Next steps**:
1. Assess urgency ("Is this something you're actively working on now, or exploring for future?")
2. If now: Qualify and schedule
3. If future: Add to re-engagement list, send resources
4. Don't push - respect their timing

### If they say "Not Interested"

**Next steps**:
1. Thank them for letting you know
2. Ask why (optional): "No problem. Just curious - is it not a fit, or just not a priority right now?"
3. Disqualify in CRM
4. Remove from sequence
5. Add to "do not contact" list (unless they said "not now")

**Reply template**:
```
"No problem, {FirstName}. Thanks for letting me know. If things change down the road, feel free to reach out. Best of luck with {Company}!"
```

### If they say "Not Now" / "Check back later"

**Next steps**:
1. Confirm timing: "When should I check back? 3 months? 6 months?"
2. Remove from current sequence
3. Add to re-engagement list with date
4. Send helpful resource (no sales pitch): case study, industry report, blog post
5. Set CRM reminder to re-engage at specified date

**Reply template**:
```
"Understood, {FirstName}. I'll check back in 6 months. In the meantime, here's a case study on how {CaseStudy} tackled this challenge - no strings attached. Happy to reconnect later!"
```

## Disqualification Criteria

**Remove from sequence immediately if**:
- Wrong company size (outside ICP range)
- Wrong geography (outside ICP target)
- Wrong platform (not using required tech stack)
- No problem (return rates <10%, not a pain point)
- No budget (asked about pricing, said too expensive without seeing demo)
- Competitor user (using competitive solution, happy with it)
- Explicit "not interested" (respect their time)

**Note**: "Not now" is NOT disqualification - it's re-engagement

## Re-engagement Timing

**If "not now" / timing issue**:
- Standard: 6 months from last contact
- High-priority account: 3 months from last contact
- Mentioned specific timing: Their specified date (e.g., "check back Q1 next year")

**Re-engagement approach**:
- New email (not reply to old thread)
- Reference prior conversation: "We spoke 6 months ago about return rates..."
- New value: Share recent case study, product update, or industry trend
- Soft ask: "Worth revisiting now, or still not a priority?"

---

## Sequence Customization Notes

**Timing adjustments**:
- If aggressive sequence: Compress to Day 0/2/4/7/10/14
- If patient sequence: Expand to Day 0/5/10/15/21/30
- If high-value account: Add +2 days between each touch (more breathing room)

**Channel adjustments**:
- If LinkedIn response rate high: Add more LinkedIn touches (Day 3, Day 7)
- If phone answer rate low: Remove Day 10 call, add Day 10 email instead
- If email open rate high: Keep email-heavy approach

**Personalization adjustments**:
- If list <20 prospects: Upgrade to human personalization (worth the effort)
- If response rate <2%: Upgrade personalization level (too generic)
- If response rate >15%: Maintain personalization (working well)
```

**Success Metrics** (track over time):
- Email open rate: 40-60% (auto-personalized)
- Email reply rate: 8-12% (auto-personalized)
- Phone answer rate: 5-10%
- Meeting booked rate: 3-5%
- Disqualification rate: 40-50%
- Re-engagement: 10-15% (of "not now" responses)
