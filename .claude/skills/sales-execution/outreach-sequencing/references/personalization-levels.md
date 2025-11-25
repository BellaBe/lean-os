# Personalization Levels

## Overview

Three levels of email personalization for B2B outreach: Mass (segment-level), Auto (company-specific), and Human (researched custom). When to use each, how to implement, and expected results.

## Personalization Level 1: Mass (Segment-Level)

### Definition

**Minimal personalization**: Segment characteristics only, no company-specific research

**Personalization tokens**:
- `{FirstName}`: Generic ("Hi there" if unknown)
- `{Company}`: Company name only
- Segment problem: Generic pain point for segment
- Value proposition: Generic solution for segment

**No research required**: Can send without looking at company website, LinkedIn, or prospect data

### When to Use Mass Personalization

**Best for**:
- Large prospect lists (100+ prospects)
- Initial cold outreach (no prior engagement)
- Budget/time constraints (limited resources for research)
- Testing messaging (want consistent message across segment)

**Example scenarios**:
- 500-prospect cold outreach campaign (no time for research)
- Testing new segment (want to see if segment responds to message)
- Broad outreach (casting wide net, will personalize for responders)

### Mass Personalization Template Example

**Subject**: {X}% {key metric} killing margins?

**Body**:
```
Hi {FirstName},

{Target segment} typically face {X-Y}% {key metric} rates, with {root cause} being the #1 driver. We've helped {industry} like {Reference Customer A} and {Reference Customer B} {achieve outcome} by {X}% using {solution approach}.

Curious if this resonates with your team at {Company}?

Best,
{YourName}
```

**Personalization breakdown**:
- `{FirstName}`: Filled in from prospect list (or "Hi there")
- `{Company}`: Company name from prospect list
- "{Target segment}": Segment-level (all prospects are {target segment})
- "{X-Y}% {key metric} rates": Segment-level problem (common across segment)
- "{Reference Customer A} and {Reference Customer B}": Segment-level social proof (competitors)
- "{Solution approach}": Generic value prop (same for all)

**Research time**: 0 minutes (no research, just fill in name/company)

### Expected Results (Mass Personalization)

**Email open rate**: 25-35% (subject line quality matters most)
**Email reply rate**: 1-3% (very low, but scalable)
**Meeting booked rate**: 0.5-1.5%

**Math**: 500 prospects × 2% reply rate = 10 replies × 50% qualification rate = 5 meetings

**ROI**: High (if volume is large enough to offset low conversion)

### Mass Personalization Quality Indicators

**Good mass email**:
- ✓ Segment problem is accurate (resonates with most prospects)
- ✓ Social proof is relevant (competitors or similar companies)
- ✓ Value prop is clear (easy to understand)
- ✓ Ask is simple (15-min call, not 1-hour demo)

**Bad mass email**:
- ✗ Generic problem (could apply to any industry)
- ✗ Irrelevant social proof ("We work with Fortune 500s" when targeting SMB)
- ✗ Vague value prop ("We help companies succeed")
- ✗ Big ask ("Sign up for a trial" with no conversation)

---

## Personalization Level 2: Auto (Company-Specific)

### Definition

**Company-specific inserts**: Use observable traits from prospect data (CSV, research notes)

**Personalization tokens**:
- `{FirstName}`: Decision-maker first name (researched or inferred)
- `{Company}`: Company name
- `{ObservedTrait}`: Platform, location, product type, hiring, funding, etc. (from prospect CSV)
- Segment problem: Contextualized with observed trait
- Value proposition: Tailored to their specific situation

**Research required**: Use data from prospect CSV (platform, size, geography, problem signals)

### When to Use Auto Personalization

**Best for**:
- Medium prospect lists (20-100 prospects)
- Prospects with observable traits (platform, tech stack, job postings)
- Standard outreach (most B2B SaaS campaigns)
- Balanced approach (personalization + scale)

**Example scenarios**:
- 50-prospect list with platform data (e.g., all on Shopify)
- Prospect CSV includes problem signals (e.g., job postings, return policy)
- Want higher response rate than mass, but can't do full manual research

### Auto Personalization Template Example

**Subject**: {Company} - {X}% {key metric}?

**Body**:
```
Hi {FirstName},

I noticed {Company} is {ObservedTrait} - curious if you're seeing high {problem area} despite this?

We've helped similar {target segment} {achieve outcome} by {X}% using {solution approach}. Quick 15-min call?

Best,
{YourName}
```

**Personalization breakdown**:
- `{FirstName}`: {Name} (from prospect list or LinkedIn)
- `{Company}`: {Company Name}
- `{ObservedTrait}`: "on {platform} and has a {observable feature} on your site" (from prospect CSV research notes)
- Problem: Contextualized ("high {problem area} despite this" - implies {current approach} isn't enough)
- Value prop: "similar {target segment}" (segment-specific)

**Research time**: 5-10 minutes per prospect (check prospect CSV for traits, verify on website)

### Observable Traits for Auto Personalization

**From prospect research CSV**:

1. **Platform/Tech stack**:
   - "on {platform}"
   - "using {tech stack tool} for {function}"
   - "with a {premium tier} store"

2. **Company characteristics**:
   - "with {N} employees on LinkedIn"
   - "based in {city}"
   - "selling {product category}"

3. **Problem signals**:
   - "has a generous {N}-day {policy type}"
   - "has a {feature type} on your site"
   - "hiring a {Problem-related role} role"

4. **Growth indicators**:
   - "recently raised {funding round}"
   - "hiring for {N} {role} roles"
   - "mentioned in {publication} last month"

5. **Product/Offering**:
   - "selling {product type}"
   - "with a wide {characteristic} range"
   - "offering {value proposition}"

### Auto Personalization Examples by Trait

**Example 1: Platform + Problem Signal**:
```
Hi {FirstName},

I noticed {Company} is on {platform} and has a generous {N}-day {policy type} - curious if {problem area} are driving this?

We've helped similar {target segment} {achieve outcome} by {X}%. Worth a conversation?

Best,
{YourName}
```

**Example 2: Growth Indicator + Problem Signal**:
```
Hi {FirstName},

Saw that {Company} is hiring for {N} {role} roles - is high {problem volume} driving the need?

We've helped growing {target segment} {achieve outcome} by {X}%, freeing up {function} capacity. Quick call?

Best,
{YourName}
```

**Example 3: Company Characteristic + Problem Signal**:
```
Hi {FirstName},

{Company} has a great {characteristic} range - are you seeing higher {key metric} for {specific case}?

We've helped {target segment} with {characteristic} reduce {problem area} by {X}%. Interested in learning how?

Best,
{YourName}
```

### Expected Results (Auto Personalization)

**Email open rate**: 45-60% (personalized subject line)
**Email reply rate**: 5-10% (much higher than mass)
**Meeting booked rate**: 2-4%

**Math**: 50 prospects × 8% reply rate = 4 replies × 60% qualification rate = 2-3 meetings

**ROI**: Medium-high (better conversion, more time investment)

### Auto Personalization Quality Indicators

**Good auto-personalized email**:
- ✓ Observed trait is specific ("{platform}" not "e-commerce platform")
- ✓ Trait connects to problem ("{N}-day {policy type}" suggests high {metric})
- ✓ Shows research (they know something about the company)
- ✓ Still concise (under 5 sentences)

**Bad auto-personalized email**:
- ✗ Generic trait ("you have a website" - everyone does)
- ✗ Trait doesn't connect to problem ("you're on {platform}" with no implication)
- ✗ Forced personalization ("I see you like the color blue on your site" - weird)
- ✗ Too long (7+ sentences because tried to include too many traits)

---

## Personalization Level 3: Human (Researched Custom)

### Definition

**Researched custom intro**: Manual research to find unique observation about company or decision-maker

**Personalization approach**:
- Custom first line (unique observation, recent activity, specific compliment)
- Connect observation to segment problem
- Tailored value prop (specific to their situation)
- Personal touch (shows you invested time)

**Research required**: 15-20 minutes per prospect (LinkedIn, website, news, social media)

### When to Use Human Personalization

**Best for**:
- Small, high-value prospect lists (5-20 prospects)
- Tier 1 prospects only (highest priority targets)
- Strategic accounts (relationship-building)
- After auto-personalization fails (upgrade for non-responders)

**Example scenarios**:
- 10 dream accounts (worth the time investment)
- Tier 1 prospects from qualified list (highest scores)
- Re-engaging cold prospects (need to upgrade personalization)
- Executive outreach (C-level requires custom approach)

### Human Personalization Template Example

**Subject**: Your LinkedIn post on {topic}

**Body**:
```
Hi {FirstName},

Saw your recent LinkedIn post about {topic} at {Company}. For {target segment} with great {characteristic} like yours, we've found that {root cause} is often the hidden {problem category} killer - {X}% of {problems} are {root cause}-related.

We've helped similar {industry} {achieve outcome} by {X}% with {solution approach}. Would love to share a quick case study from a company your size.

15 minutes this week?

Best,
{YourName}
```

**Personalization breakdown**:
- Custom intro: "Saw your recent LinkedIn post on {topic}" (requires LinkedIn research)
- Contextualized compliment: "great {characteristic} like yours" (genuine, not generic)
- Connect to problem: "{root cause} is hidden {problem category} killer" (ties their {topic} focus to your solution)
- Specific social proof: "company your size" (tailored, not generic "similar companies")
- Personal ask: "15 minutes this week?" (time-bound, conversational)

**Research time**: 15-20 minutes (LinkedIn profile, recent activity, company news, website)

### Research Process for Human Personalization

**Step 1: LinkedIn Profile Research** (5 minutes)
- Check decision-maker's recent posts (last 30 days)
- Check recent comments on others' posts
- Check profile updates (new role, promotion, company change)
- Check "About" section (interests, background)

**Step 2: Company Website Research** (5 minutes)
- Check "About Us" page (mission, values, story)
- Check "News" or "Press" page (recent announcements)
- Check product pages (unique offerings, differentiators)
- Check blog (recent posts, themes)

**Step 3: News/Social Media Research** (5 minutes)
- Google: "{Company name} news" (recent 3 months)
- Check company Twitter/Instagram (recent posts)
- Check Crunchbase (funding, acquisitions, hiring)

**Step 4: Find Unique Observation** (2-5 minutes)
- Look for: Recent activity, achievement, challenge, change
- Examples: LinkedIn post, funding round, product launch, hiring spree, award, article mention

### Human Personalization Examples by Research Finding

**Example 1: LinkedIn Post**:
```
Hi {FirstName},

Saw your LinkedIn post last week about the challenges of {topic} at {Company}. For growing {target segment}, we've found that {addressing problem} (especially {specific aspect}) can {achieve outcome} by {X-Y}%.

We've helped {industry} like yours {achieve outcome} by {X}%. Worth a conversation about the {business impact}?

Best,
{YourName}
```

**Example 2: Funding Announcement**:
```
Hi {FirstName},

Congrats on the {funding round} for {Company}! As you scale, {problem area} often become a bigger challenge (volume increases, margins tighten).

We've helped recently-funded {target segment} {achieve outcome} by {X}% before they become a major cost center. Quick call to share the playbook?

Best,
{YourName}
```

**Example 3: Product Launch**:
```
Hi {FirstName},

Saw {Company} just launched a new {product line} - congrats! New product lines often have higher {key metric} initially (customers unsure of {uncertainty}).

We've helped {industry} {achieve outcome} on new lines by {X}% using {solution approach}. Would love to share how.

Best,
{YourName}
```

**Example 4: Job Posting**:
```
Hi {FirstName},

Noticed {Company} is hiring for a {Problem-related role} role - is {problem volume} growing as you scale?

We've helped {target segment} {achieve outcome} by {X}%, often eliminating the need for dedicated {problem-related} roles. Ironic timing for a quick conversation?

Best,
{YourName}
```

**Example 5: Award/Recognition**:
```
Hi {FirstName},

Saw {Company} was named one of the "{Award Title}" - well deserved! As you grow, keeping {key metric} low will be critical for maintaining margins.

We've helped award-winning {industry} like yours {achieve outcome} by {X}%. Quick call to share best practices?

Best,
{YourName}
```

### Expected Results (Human Personalization)

**Email open rate**: 60-80% (very high due to custom subject)
**Email reply rate**: 15-25% (significantly higher than auto)
**Meeting booked rate**: 8-15%

**Math**: 10 prospects × 20% reply rate = 2 replies × 75% qualification rate = 1-2 meetings

**ROI**: Medium (high conversion, very high time investment)

**Note**: Only worth it for high-value prospects (worth 3-5 hours to book 1-2 meetings)

### Human Personalization Quality Indicators

**Good human-personalized email**:
- ✓ Observation is recent (last 30 days, feels timely)
- ✓ Observation is specific (not generic compliment)
- ✓ Connects to problem (not just flattery)
- ✓ Feels authentic (not forced or creepy)

**Bad human-personalized email**:
- ✗ Observation is stale ("I saw your LinkedIn post from 2 years ago...")
- ✗ Observation is generic ("I see you care about customers" - everyone does)
- ✗ Doesn't connect to problem (random compliment with no tie to solution)
- ✗ Feels stalker-y ("I saw your vacation photos on Instagram..." - TOO personal)

---

## Personalization Level Selection Matrix

| Prospect List Size | ICP Tier | Recommended Level | Expected Reply Rate | Time Investment |
|-------------------|----------|-------------------|---------------------|-----------------|
| 100+ | Mixed | Mass | 1-3% | 0 min/prospect |
| 50-100 | Mixed | Auto | 5-8% | 5-10 min/prospect |
| 20-50 | Tier 1-2 | Auto | 8-12% | 5-10 min/prospect |
| 10-20 | Tier 1 | Human | 15-20% | 15-20 min/prospect |
| <10 | Tier 1 | Human | 20-25% | 15-20 min/prospect |

### Selection Rules

**Rule 1: List size drives default level**
- 100+ prospects → Default to Mass (scale matters more than conversion)
- 20-100 prospects → Default to Auto (balance of scale + conversion)
- <20 prospects → Default to Human (worth the time for small list)

**Rule 2: ICP tier can upgrade level**
- Tier 1 prospects (score >= 0.75) → Upgrade to Human (if <20 prospects)
- Tier 2 prospects (score 0.5-0.74) → Stay at Auto
- Tier 3 prospects (score 0.3-0.49) → Downgrade to Mass (not worth Auto time)

**Rule 3: Response rate can trigger upgrade**
- If Mass reply rate <1% → Upgrade to Auto (message not resonating)
- If Auto reply rate <5% → Upgrade to Human for Tier 1 (need more personalization)

**Rule 4: Resource constraints can force downgrade**
- Limited time → Downgrade from Human to Auto
- Very limited time → Downgrade from Auto to Mass

### Selection Examples

**Example 1**: 150 prospects, mixed tiers
- **Recommended**: Mass for all (too many for Auto)
- **Alternative**: Mass for Tier 2-3, Auto for Tier 1 only (if Tier 1 list is <20)

**Example 2**: 50 prospects, mostly Tier 1
- **Recommended**: Auto for all (balanced approach)
- **Alternative**: Human for top 10 Tier 1, Auto for rest (if time allows)

**Example 3**: 15 prospects, all Tier 1
- **Recommended**: Human for all (worth the investment)
- **Time investment**: 15 × 20 min = 5 hours (worth it for high-quality meetings)

**Example 4**: 200 prospects, testing new segment
- **Recommended**: Mass for all (want consistent message to test)
- **Rationale**: Testing if segment responds to message (don't personalize until validated)

---

## Personalization Level Implementation

### Mass Personalization Workflow

1. Load prospect CSV (name, company, email)
2. Load email template (segment-level)
3. Mail merge: Fill {FirstName}, {Company} tokens
4. Send batch (can send 100+ per day)
5. Track opens/replies

**Tools**: HubSpot, Mailchimp, Outreach.io (batch sending)

**Time**: 1-2 hours for 100+ prospects (setup + send)

### Auto Personalization Workflow

1. Load prospect CSV (name, company, email, observed traits)
2. Load email template (with {ObservedTrait} tokens)
3. For each prospect:
   - Review observed trait from CSV
   - Verify trait on company website (5 min)
   - Fill {ObservedTrait} token
   - Customize subject line (add company name)
4. Send individually (personalized subject = better deliverability)
5. Track opens/replies

**Tools**: HubSpot, Outreach, SalesLoft (personalization tokens, individual sending)

**Time**: 5-10 hours for 50 prospects (5-10 min/prospect)

### Human Personalization Workflow

1. Load prospect list (name, company, LinkedIn URL)
2. For each prospect:
   - Research LinkedIn profile (5 min)
   - Research company website (5 min)
   - Research news/social (5 min)
   - Find unique observation (2-5 min)
   - Write custom intro (3-5 min)
   - Customize rest of email
   - Customize subject line
3. Send individually (fully custom emails)
4. Track opens/replies

**Tools**: LinkedIn, Google, CRM for notes, Email for sending (often Gmail/Outlook, not mass tool)

**Time**: 3-5 hours for 10 prospects (15-20 min/prospect)

---

## Personalization Level Quality Checklist

### Mass Personalization Quality Check

**Before sending, verify**:
- [ ] Segment problem is accurate (resonates with 80%+ of segment)
- [ ] Social proof is relevant (competitors or similar companies in segment)
- [ ] Value prop is clear (specific metric, not vague)
- [ ] Email is under 5 sentences (including subject)
- [ ] No placeholder tokens left ({{Company}} → ChicThreads)

### Auto Personalization Quality Check

**Before sending, verify**:
- [ ] Observed trait is verified (checked company website/LinkedIn)
- [ ] Trait connects to problem (logical connection, not forced)
- [ ] Trait is specific (not generic like "you have a website")
- [ ] Subject line includes company name (personalized)
- [ ] Email is under 5 sentences

### Human Personalization Quality Check

**Before sending, verify**:
- [ ] Observation is recent (<30 days old)
- [ ] Observation is unique (not something everyone could say)
- [ ] Observation connects to problem (not just flattery)
- [ ] Email feels authentic (not stalker-y or forced)
- [ ] Subject line is custom (not template)
- [ ] Email is under 5 sentences (even with custom intro)

---

## Personalization Level Red Flags

### Mass Personalization Red Flags

**Warning signs**:
- Reply rate <1% (message not resonating, need to upgrade)
- Open rate <25% (subject line weak, need to personalize subject)
- Disqualification rate >70% (wrong segment, need better ICP)
- "Unsubscribe" rate >5% (too generic, feels spammy)

### Auto Personalization Red Flags

**Warning signs**:
- Reply rate <5% (traits not compelling, need to upgrade to Human)
- Traits feel forced (random observations with no tie to problem)
- Too much research time (>15 min/prospect = should just do Human)
- Prospect CSV missing trait data (can't do Auto without data)

### Human Personalization Red Flags

**Warning signs**:
- Reply rate <15% (even Human not working, wrong list or message)
- Research taking >30 min/prospect (too slow, not scalable even for Human)
- Observations feel stalker-y (too personal, crosses boundary)
- Can't find unique observations (company has no recent activity, downgrade to Auto)

---

## Personalization Level Examples Summary

### Mass Example (Segment-Level)

```
Subject: {X}% {key metric} killing margins?

Hi {FirstName},

{Target segment} typically face {X-Y}% {key metric}. We've helped {industry} like {Reference Customer} {achieve outcome} by {X}%.

Curious if this resonates at {Company}?

Best,
{YourName}
```

**Personalization**: Name, company only
**Research time**: 0 minutes
**Expected reply rate**: 2%

### Auto Example (Company-Specific)

```
Subject: {Company} - {X}% {key metric}?

Hi {FirstName},

I noticed {Company} is on {platform} and has a {N}-day {policy type} - curious if {problem area} are driving this?

We've helped similar {target segment} {achieve outcome} by {X}%. Quick call?

Best,
{YourName}
```

**Personalization**: Name, company, observed traits (platform, policy)
**Research time**: 7 minutes
**Expected reply rate**: 8%

### Human Example (Researched Custom)

```
Subject: Your LinkedIn post on {topic}

Hi {FirstName},

Saw your recent LinkedIn post about {topic} at {Company}. {Root cause} is often the hidden {problem category} killer for {target segment} - {X}% of {problems} are {root cause}-related.

We've helped similar {industry} {achieve outcome} by {X}%. Would love to share a case study.

15 minutes this week?

Best,
{YourName}
```

**Personalization**: Custom intro (LinkedIn post), contextualized problem, tailored ask
**Research time**: 18 minutes
**Expected reply rate**: 20%

---

## When to Upgrade Personalization Level

### Upgrade from Mass to Auto

**Trigger conditions**:
- Reply rate <2% after 50+ prospects (message not resonating)
- Prospect list <100 (small enough for Auto)
- Observed trait data available (can do Auto efficiently)
- Conversion to meeting <1% (need better qualification)

**Example**: Sent Mass to 150 prospects, got 2 replies (1.3%). Upgrade to Auto for next batch of 50.

### Upgrade from Auto to Human

**Trigger conditions**:
- Reply rate <5% for Tier 1 prospects (need more personalization)
- List is <20 Tier 1 prospects (worth the time)
- High-value strategic accounts (worth 20 min/prospect)
- Second touch to non-responders (re-engage with Human)

**Example**: Sent Auto to 30 Tier 1 prospects, got 2 replies (6.7%). Upgrade to Human for non-responders.

### Downgrade from Human to Auto

**Trigger conditions**:
- Can't find unique observations (no recent activity)
- Time constraint (can't spend 20 min/prospect)
- List unexpectedly large (thought it was 10, actually 50)

### Downgrade from Auto to Mass

**Trigger conditions**:
- Prospect CSV missing trait data (can't personalize)
- List unexpectedly large (thought it was 50, actually 200)
- Time constraint (need to send today, no time for research)

---

## Personalization Best Practices

**Do**:
- ✓ Match personalization level to list size (scale matters)
- ✓ Upgrade for Tier 1 prospects (highest priority)
- ✓ Use observed traits only (no guessing or assumptions)
- ✓ Keep emails under 5 sentences (even with personalization)
- ✓ Track reply rates by level (measure what works)

**Don't**:
- ✗ Force personalization (generic traits feel fake)
- ✗ Over-personalize (stalker-y observations cross boundary)
- ✗ Personalize everything (balance scale + conversion)
- ✗ Guess traits (verify before using)
- ✗ Make emails longer because of personalization (still 5 sentences max)
