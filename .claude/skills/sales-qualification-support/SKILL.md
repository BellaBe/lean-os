---
name: sales-qualification-support
description: Generate discovery call prep materials, qualification checklists, and scoring frameworks to determine if a lead should be pursued based on problem fit, authority, budget, urgency, and solution fit. Use when preparing for discovery calls.
allowed-tools: [Read, Write]
---

# Qualification-Support Subskill

## Purpose

Generate discovery call prep materials, qualification checklists, and scoring frameworks to determine if a lead should be pursued.

**Operates on**: ONE product per invocation
**Input**: ICP qualification criteria + discovery call scripts + company context
**Output**: Call prep document with qualification framework, scoring, and next steps

## Context

- Reads from: `research/customer/icp/{segment}-icp.md` (qualification criteria)
- Reads from: `artifacts/sales/{segment}/materials/call-scripts.md` (discovery framework)
- Reads from: `research/customer/prospects/{segment}-prospects-{date}.csv` (optional - for company context)
- Writes to: `threads/sales/calls/prep-{company}-{date}.md` (call prep)
- Writes to: `threads/sales/calls/qualification-{company}-{date}.md` (qualification log)
- Used: Before/during discovery calls

## Key Workflows

### 1. Pre-Call Research Prompt

**Generate research checklist for specific company**:

**Company Website Research**:
- Review homepage (product offerings, value prop)
- Check "About Us" page (company size, mission, team)
- Review product/service pages (what they sell, to whom)
- Check pricing page (if public - revenue indicator)
- Look for problem signals:
  - FAQ mentions problem
  - Support/Help section addresses problem
  - Blog posts discuss problem
  - Testimonials mention problem
- Check technology stack:
  - Footer "Powered by {platform}" badge
  - Page source inspection (Shopify, WordPress, custom)
- Review team page (employee count, roles, decision-makers)

**LinkedIn Research**:
- Company page:
  - Employee count (validate ICP size match)
  - Location (validate ICP geography match)
  - Recent posts (company priorities, challenges)
  - Growth indicators (hiring, expansion)
- Decision-maker profile (if known):
  - Current role and tenure (authority indicator)
  - Recent posts/activity (interests, challenges)
  - Background (previous companies, experience)
  - Connections (mutual connections for warm intro context)

**Industry Context**:
- Industry trends affecting segment:
  - {Industry A}: {trend 1}, {trend 2}, {key metric}
  - {Industry B}: {trend 1}, {trend 2}
  - {Industry C}: {trend 1}, {trend 2}
- Competitive landscape:
  - Who else solves this problem?
  - What are prospects using today?
- Recent news:
  - Google: "{company name} news" (last 3 months)
  - Funding, acquisitions, product launches, leadership changes

**Problem Signal Validation**:
- From ICP problem signal patterns:
  - Website mentions problem explicitly
  - Reviews mention problem (Trustpilot, G2, etc.)
  - Job postings for roles that indicate problem ({Problem-related role} = {problem indicator})
  - Social media mentions problem
- Quantify if possible:
  - "{Observable indicator}" suggests {problem volume}
  - "Hiring {N} {Problem-related role} roles" suggests {implication}
  - "{Feature indicator}" suggests {problem area}

### 2. Discovery Question Framework

**Load qualification questions from ICP**:
- Read `research/customer/icp/{segment}-icp.md`
- Extract `qualification_questions` section
- Extract `disqualification_criteria` section
- Map to qualification dimensions (Problem, Authority, Budget, Urgency, Solution Fit)

**Load discovery call script**:
- Read `artifacts/sales/{segment}/materials/call-scripts.md`
- Extract "Discovery Call" section
- Use as framework for call flow
- Integrate qualification questions into script

**Organize by qualification dimension** (Pete Kazanjy BANT + Problem/Solution Fit):

#### Dimension 1: Problem Fit (Weight: 0.3)

**Goal**: Do they have the problem we solve?

**Questions**:
1. "Walk me through your current {process}" (open-ended, let them talk)
2. "What's your biggest challenge with {problem area}?" (identify pain)
3. "What percentage of {metric} do you experience?" (quantify problem)
4. "How does this impact your team/business?" (understand cost)
5. "What have you tried so far to solve this?" (alternatives, urgency)

**Scoring rubric**:
- **1.0**: Clear, quantified problem matching our solution (e.g., "{X-Y}% {key metric} rates, costing $500K/year")
- **0.7**: Problem exists but not quantified (e.g., "{Problem area} is high, not sure exact number")
- **0.5**: Problem exists but not prioritized (e.g., "It's a challenge but we're managing")
- **0.3**: Vague problem (e.g., "Things could be better")
- **0.0**: No problem or already solved (e.g., "We don't see this as an issue")

#### Dimension 2: Authority (Weight: 0.2)

**Goal**: Can they make buying decisions?

**Questions**:
1. "Who else would be involved in evaluating this?" (identify stakeholders)
2. "What's your typical process for bringing on new tools?" (buying process)
3. "Do you have budget authority for this?" (direct authority question)
4. "Who would ultimately sign off on this?" (find economic buyer)
5. "Have you made similar purchases before?" (gauge experience)

**Scoring rubric**:
- **1.0**: Decision-maker on the call, has budget authority (e.g., "I make these decisions, I have budget")
- **0.7**: Strong influencer, can champion but needs approval (e.g., "I'd evaluate and recommend to CFO")
- **0.5**: Influencer, multiple stakeholders (e.g., "Need to involve CMO, CFO, and CTO")
- **0.3**: Low influence, exploring only (e.g., "Just doing research for my boss")
- **0.0**: No authority, information gathering (e.g., "I'm an intern researching options")

#### Dimension 3: Budget (Weight: 0.2)

**Goal**: Will they pay our price?

**Questions**:
1. "What's the cost of this problem currently?" (quantify pain in dollars)
2. "How much would solving this be worth to you?" (value perception)
3. "Have you allocated budget for solving this?" (budget exists?)
4. "What's your typical budget range for tools like this?" (price sensitivity)
5. "What ROI would you need to see to justify this?" (decision criteria)

**Scoring rubric**:
- **1.0**: Clear budget, can justify cost (e.g., "We've allocated $100K for this, problem costs us $500K/year")
- **0.7**: Budget exists but needs approval (e.g., "We have budget, need to present ROI to CFO")
- **0.5**: Budget unclear, needs to build business case (e.g., "Would need to show ROI to secure budget")
- **0.3**: Budget concern, price-sensitive (e.g., "Budget is tight, what's your price?")
- **0.0**: No budget or cost is barrier (e.g., "We can't afford any new tools this year")

#### Dimension 4: Urgency (Weight: 0.15)

**Goal**: Is this a priority now?

**Questions**:
1. "When do you need this solved by?" (timeline)
2. "What happens if you don't solve this in the next 30/60/90 days?" (consequence)
3. "What other priorities are competing for attention?" (relative urgency)
4. "What triggered you to look into this now?" (catalyst event)
5. "Is there a deadline or event driving this?" (external pressure)

**Scoring rubric**:
- **1.0**: Urgent, needs solution within 30 days (e.g., "Peak season in 3 weeks, need to act now")
- **0.7**: Important, 30-60 day timeline (e.g., "Want to launch next quarter")
- **0.5**: Important but not urgent, 60-90 days (e.g., "Planning for next year")
- **0.3**: Low urgency, 90+ days (e.g., "Exploring options for future")
- **0.0**: Nice to have, no timeline (e.g., "Just seeing what's out there")

#### Dimension 5: Solution Fit (Weight: 0.15)

**Goal**: Should we sell to them?

**Questions**:
1. "Are you on {required platform}?" (technical fit)
2. "Do you have {required capability}?" (infrastructure fit)
3. "What's your {relevant metric}?" (size/volume fit)
4. "How technical is your team?" (implementation fit)
5. "What's your ideal solution look like?" (expectation alignment)

**Scoring rubric**:
- **1.0**: Perfect fit for our solution (e.g., "On {required platform}, 50-200 employees, {problem indicator}")
- **0.7**: Good fit, minor gaps (e.g., "On {acceptable alternative}, 180 employees")
- **0.5**: Can work but requires customization (e.g., "Custom platform, would need integration work")
- **0.3**: Poor fit, significant gaps (e.g., "Wrong platform, too small, doesn't match ICP")
- **0.0**: We can't help effectively (e.g., "Entirely different problem than we solve")

### 3. Qualification Scoring

**Scoring formula**:
```
Total Score = (Problem × 0.3) + (Authority × 0.2) + (Budget × 0.2) + (Urgency × 0.15) + (Solution Fit × 0.15)
```

**Example calculation**:
```
Company: {Company Name}
Problem: 0.9 (clear problem: "{X}% {key metric} rates, costing $400K/year")
Authority: 0.7 ({Role} on call, needs {Approver Role} approval for >${threshold})
Budget: 0.8 (budget allocated, need to show ROI)
Urgency: 0.6 (important for {timeframe}, {N}-day timeline)
Solution Fit: 1.0 (perfect fit: {required platform}, {employees} employees, {industry})

Total = (0.9 × 0.3) + (0.7 × 0.2) + (0.8 × 0.2) + (0.6 × 0.15) + (1.0 × 0.15)
     = 0.27 + 0.14 + 0.16 + 0.09 + 0.15
     = 0.81

Interpretation: High qualification (>0.8) → Schedule demo immediately
```

**Qualification tiers**:

**High qualification (>= 0.8)**:
- **Characteristics**: Strong fit across all dimensions, likely to close
- **Action**: Schedule demo immediately
- **Expected close rate**: 30-50%
- **Priority**: Highest (drop everything to move forward)

**Medium qualification (0.5 - 0.8)**:
- **Characteristics**: Good fit but gaps in 1-2 dimensions
- **Action**: Address gaps, schedule follow-up
- **Expected close rate**: 15-25%
- **Priority**: Medium (worth pursuing with effort)

**Low qualification (< 0.5)**:
- **Characteristics**: Poor fit, multiple dimensions scored low
- **Action**: Disqualify politely, add to nurture
- **Expected close rate**: <5%
- **Priority**: Low (don't waste time)

### 4. Objection Response Patterns

**Load common objections**:
- Read from `references/objection-patterns.md`
- Map objections to qualification dimensions:
  - "Too expensive" → Budget dimension
  - "Not a priority" → Urgency dimension
  - "Need to think about it" → Authority or Problem dimension
  - "Already have solution" → Solution Fit dimension

**Response frameworks**:

**Objection type 1: Price ("Too expensive")**:
- **Framework**: Reframe to ROI
- **Response**: "I understand price is a concern. Let's look at the cost of the problem - you mentioned $400K/year in returns. Our solution costs $X/month ($Y/year), and we typically see 35% reduction in returns. That's a $140K/year savings, or 7x ROI. Does that math work for you?"
- **Follow-up question**: "What ROI would you need to see to justify the investment?"

**Objection type 2: Timing ("Need to think about it")**:
- **Framework**: Identify specific concern
- **Response**: "Absolutely, it's an important decision. What specifically would you need to evaluate? Is it budget, getting other stakeholders involved, or understanding the solution better?"
- **Follow-up question**: "What would make this a clear 'yes' for you?"

**Objection type 3: Competition ("Already have a solution")**:
- **Framework**: Differentiate, don't bash
- **Response**: "That's great you're addressing this. How does your current solution handle {specific problem they mentioned}? [Listen for gap] We've found that {specific differentiator} is what makes the difference for companies like yours."
- **Follow-up question**: "If you could improve one thing about your current solution, what would it be?"

**Objection type 4: Urgency ("Not right now")**:
- **Framework**: Create urgency through consequence
- **Response**: "I understand. What would need to change to make this a priority? [Listen] You mentioned the problem is costing $400K/year - that's $33K/month you're losing while evaluating. What's the cost of waiting 3-6 months?"
- **Follow-up question**: "Is there an upcoming event (holiday season, quarter-end, funding round) that would make this more urgent?"

**Objection type 5: Authority ("Need to run this by my boss")**:
- **Framework**: Offer to include decision-maker
- **Response**: "That makes sense. Who else should be involved in this conversation? I'm happy to present to your team or CFO directly. What information would they need to see to make a decision?"
- **Follow-up question**: "Would it be helpful if I joined your internal discussion to answer questions?"

### 5. Next Step Recommendations

**Based on qualification score tier**:

#### High Qualification (>= 0.8)

**Immediate action**: Schedule demo

**Script**:
```
"Based on what you've shared, I think a 30-minute demo would be really valuable. We can show you exactly how {solution} addresses {their specific problem}. How does Tuesday at 2pm look?"
```

**Next steps checklist**:
- [ ] Schedule demo (send calendar invite immediately)
- [ ] Attach agenda (what we'll cover in demo)
- [ ] Send one-pager (artifacts/sales/{segment}/materials/one-pager.md)
- [ ] Send calendar reminder email 1 day before
- [ ] Prepare custom demo (based on their problem/use case)
- [ ] Log qualification score in thread for tracking

**Timeline**: Demo within 1 week of discovery call

#### Medium Qualification (0.5 - 0.8)

**Action depends on which dimension scored low**:

**If Authority scored low (<0.7)**:
- **Action**: Schedule decision-maker call
- **Script**: "It sounds like you'd need to involve your CFO in this decision. Would it make sense for us to have a brief call with both of you? I can present the business case and ROI directly."
- **Next steps**: Get decision-maker on next call

**If Budget scored low (<0.7)**:
- **Action**: Send ROI/value prop email
- **Script**: "Let me send you a detailed breakdown of the ROI we typically see, including a case study from a company your size. That should help with the budget conversation."
- **Next steps**: Email with ROI calculator, case study, pricing

**If Urgency scored low (<0.7)**:
- **Action**: Identify catalyst, set follow-up
- **Script**: "It sounds like this isn't urgent right now. What would make this a higher priority? [Listen for catalyst] Let's reconnect in 2 weeks to see if anything has shifted."
- **Next steps**: Calendar reminder to follow up in 2-4 weeks

**If Problem scored low (<0.7)**:
- **Action**: Provide education, requalify later
- **Script**: "It sounds like you're early in exploring this. Let me send you a resource on {problem} and how companies like yours are tackling it. Would it be helpful to reconnect in a month after you've had a chance to review?"
- **Next steps**: Send educational content, follow up in 30 days

**If Solution Fit scored low (<0.7)**:
- **Action**: Assess if gap is bridgeable
- **If yes**: "We'd need to do some custom work to support {their situation}. Let me check with our team on feasibility and get back to you."
- **If no**: "I don't think we're the right fit for {their specific situation}. Have you looked at {competitor who is better fit}?"

**Timeline**: Follow-up in 2-4 weeks (depending on gap)

#### Low Qualification (< 0.5)

**Action**: Disqualify politely, add to nurture

**Script**:
```
"Based on what you've shared, I don't think we're the right fit for you right now. [Specific reason: wrong size, no budget, different problem, etc.] I'd love to stay in touch and check back in {timeline} to see if things have changed. Can I add you to our quarterly newsletter?"
```

**Disqualification reasons** (be specific):
- **Wrong company size**: "You mentioned 20 employees, we typically work with companies 50-200 employees"
- **Wrong problem**: "It sounds like your main challenge is {X}, but we solve {Y}"
- **No budget**: "Without allocated budget, it's hard to move forward. Let's reconnect when budget opens up."
- **No urgency**: "It sounds like this isn't a priority for at least 6 months. Let's reconnect then."
- **No authority**: "Since you're researching for someone else, it would be better if I spoke directly with the decision-maker."
- **Wrong platform**: "We only support {required platform}, and you're on {other platform}. Not a good fit right now."

**Next steps checklist**:
- [ ] Thank them for their time (respectful, professional)
- [ ] Provide alternative if possible (competitor recommendation, free resource)
- [ ] Add to nurture list (quarterly check-in email)
- [ ] Log disqualification reason in: `threads/sales/disqualified-{date}.csv`
- [ ] Log for pattern detection (are we targeting wrong companies?)

**Timeline**: Re-engage in 6-12 months (if they're in ICP, just bad timing)

## Input Parameters

**Required**:
- `product`: Product name (e.g., "{Your Product}")
- `company_name`: Target company for call prep
- `company_domain`: Company domain for research

**Optional**:
- `call_type`: "discovery" | "demo" | "follow-up" (default: "discovery")
- `decision_maker_name`: If known (for LinkedIn research)
- `decision_maker_title`: If known (for authority assessment)
- `thread_id`: Sales thread ID (to log qualification)

## Output

**File 1**: `threads/sales/calls/prep-{company}-{date}.md`
- Pre-call research checklist
- Company context summary
- Qualification framework (questions + scoring)
- Objection handling guide
- Next step recommendations

**File 2** (post-call): `threads/sales/calls/qualification-{company}-{date}.md`
- Qualification scores per dimension
- Overall qualification score
- Next step recommendation
- Notes from call
- Follow-up timeline

**File 3** (if disqualified): `threads/sales/disqualified-{date}.csv`
- Company name, domain, date
- Disqualification reason
- Score breakdown
- Re-engagement timeline (if applicable)

## Call Prep Output Format

```markdown
# Discovery Call Prep: {Company Name}

**Segment**: {segment}
**Date**: {date}
**Call Type**: Discovery
**Company**: {company_name} ({company_domain})
**Decision-Maker**: {decision_maker_name} - {decision_maker_title}

---

## Pre-Call Research

**Company Website** ({company_domain}):
- [ ] Review homepage (product offerings, value prop)
- [ ] Check About Us page (size, mission, team)
- [ ] Look for problem signals:
  - [ ] FAQ mentions {problem}
  - [ ] Support section addresses {problem}
  - [ ] Blog discusses {problem}
- [ ] Check technology stack (footer, page source)
- [ ] Review team page (employee count, roles)

**LinkedIn Research**:
- [ ] Company page: linkedin.com/company/{company}
  - [ ] Employee count (ICP match?)
  - [ ] Location (ICP geography?)
  - [ ] Recent posts (priorities, challenges)
- [ ] Decision-maker profile: linkedin.com/in/{person}
  - [ ] Current role and tenure
  - [ ] Recent posts (interests, challenges)
  - [ ] Background (previous experience)

**Industry Context**:
- [ ] Industry trends: {relevant trends for segment}
- [ ] Competitive landscape: {competitors they might be using}
- [ ] Recent news: Google "{company} news" (last 3 months)

**Problem Signal Validation**:
- [ ] {Specific signal 1 from ICP}: e.g., "Check return policy (60+ days suggests high returns)"
- [ ] {Specific signal 2 from ICP}: e.g., "Check for job postings (Returns Coordinator = high volume)"
- [ ] {Specific signal 3 from ICP}: e.g., "Look for sizing guide (existing but insufficient)"

---

## Qualification Framework

### Problem Fit (Weight: 0.3)

**Goal**: Do they have the problem we solve?

**Questions to ask**:
1. "Walk me through your current {process}" *(open-ended, let them talk)*
2. "What's your biggest challenge with {problem area}?" *(identify pain)*
3. "What percentage of {metric} do you experience?" *(quantify problem)*
4. "How does this impact your team/business?" *(understand cost)*
5. "What have you tried so far to solve this?" *(alternatives, urgency)*

**Scoring guide**:
- 1.0 = Clear, quantified problem (e.g., "20-30% return rates, costing $500K/year")
- 0.7 = Problem exists but not quantified
- 0.5 = Problem exists but not prioritized
- 0.3 = Vague problem
- 0.0 = No problem or already solved

**Your score**: ____ / 1.0

**Notes**:
{Space for notes during call}

---

### Authority (Weight: 0.2)

**Goal**: Can they make buying decisions?

**Questions to ask**:
1. "Who else would be involved in evaluating this?" *(identify stakeholders)*
2. "What's your typical process for bringing on new tools?" *(buying process)*
3. "Do you have budget authority for this?" *(direct authority question)*
4. "Who would ultimately sign off on this?" *(find economic buyer)*
5. "Have you made similar purchases before?" *(gauge experience)*

**Scoring guide**:
- 1.0 = Decision-maker on call, has budget authority
- 0.7 = Strong influencer, can champion
- 0.5 = Influencer, multiple stakeholders
- 0.3 = Low influence, exploring only
- 0.0 = No authority

**Your score**: ____ / 1.0

**Notes**:
{Space for notes}

---

### Budget (Weight: 0.2)

**Goal**: Will they pay our price?

**Questions to ask**:
1. "What's the cost of this problem currently?" *(quantify pain)*
2. "How much would solving this be worth to you?" *(value perception)*
3. "Have you allocated budget for solving this?" *(budget exists?)*
4. "What's your typical budget range for tools like this?" *(price sensitivity)*
5. "What ROI would you need to see to justify this?" *(decision criteria)*

**Scoring guide**:
- 1.0 = Clear budget, can justify cost
- 0.7 = Budget exists but needs approval
- 0.5 = Budget unclear, needs business case
- 0.3 = Budget concern, price-sensitive
- 0.0 = No budget

**Your score**: ____ / 1.0

**Notes**:
{Space for notes}

---

### Urgency (Weight: 0.15)

**Goal**: Is this a priority now?

**Questions to ask**:
1. "When do you need this solved by?" *(timeline)*
2. "What happens if you don't solve this in next 30/60/90 days?" *(consequence)*
3. "What other priorities are competing for attention?" *(relative urgency)*
4. "What triggered you to look into this now?" *(catalyst event)*
5. "Is there a deadline or event driving this?" *(external pressure)*

**Scoring guide**:
- 1.0 = Urgent, needs solution within 30 days
- 0.7 = Important, 30-60 day timeline
- 0.5 = Important but not urgent, 60-90 days
- 0.3 = Low urgency, 90+ days
- 0.0 = Nice to have, no timeline

**Your score**: ____ / 1.0

**Notes**:
{Space for notes}

---

### Solution Fit (Weight: 0.15)

**Goal**: Should we sell to them?

**Questions to ask**:
1. "Are you on {required platform}?" *(technical fit)*
2. "Do you have {required capability}?" *(infrastructure fit)*
3. "What's your {relevant metric}?" *(size/volume fit)*
4. "How technical is your team?" *(implementation fit)*
5. "What's your ideal solution look like?" *(expectation alignment)*

**Scoring guide**:
- 1.0 = Perfect fit for our solution
- 0.7 = Good fit, minor gaps
- 0.5 = Can work but requires customization
- 0.3 = Poor fit, significant gaps
- 0.0 = We can't help effectively

**Your score**: ____ / 1.0

**Notes**:
{Space for notes}

---

## Qualification Scoring

**Calculation**:
```
Total Score = (Problem × 0.3) + (Authority × 0.2) + (Budget × 0.2) + (Urgency × 0.15) + (Solution Fit × 0.15)

Total Score = (____ × 0.3) + (____ × 0.2) + (____ × 0.2) + (____ × 0.15) + (____ × 0.15)
            = ____
```

**Interpretation**:
- **>= 0.8**: High qualification → Schedule demo immediately
- **0.5 - 0.8**: Medium qualification → Address gaps, schedule follow-up
- **< 0.5**: Low qualification → Disqualify politely, add to nurture

**Your score**: ____ → **Tier: ____**

---

## Objection Handling

### "Too expensive"
**Framework**: Reframe to ROI
**Response**: "I understand price is a concern. Let's look at the cost of the problem - you mentioned ${X} in {problem}. Our solution costs ${Y}/month, and we typically see {Z}% reduction. That's a ${ROI} savings. Does that math work for you?"
**Follow-up**: "What ROI would you need to see to justify the investment?"

### "Need to think about it"
**Framework**: Identify specific concern
**Response**: "Absolutely, it's an important decision. What specifically would you need to evaluate? Is it budget, getting other stakeholders involved, or understanding the solution better?"
**Follow-up**: "What would make this a clear 'yes' for you?"

### "Already have a solution"
**Framework**: Differentiate, don't bash
**Response**: "That's great you're addressing this. How does your current solution handle {specific problem}? [Listen for gap] We've found that {differentiator} is what makes the difference."
**Follow-up**: "If you could improve one thing about your current solution, what would it be?"

### "Not right now"
**Framework**: Create urgency through consequence
**Response**: "I understand. What would need to change to make this a priority? [Listen] You mentioned the problem is costing ${X}/year - that's ${X/12}/month you're losing. What's the cost of waiting?"
**Follow-up**: "Is there an upcoming event that would make this more urgent?"

### "Need to run this by my boss"
**Framework**: Offer to include decision-maker
**Response**: "That makes sense. Who else should be involved? I'm happy to present to your team or CFO directly. What information would they need?"
**Follow-up**: "Would it be helpful if I joined your internal discussion?"

---

## Next Steps Based on Score

### High (>= 0.8):
- [ ] **Schedule demo**: "Based on what you've shared, I think a 30-min demo would be valuable. How does Tuesday at 2pm look?"
- [ ] **Send calendar invite** with agenda
- [ ] **Attach one-pager**: artifacts/sales/{segment}/materials/one-pager.md
- [ ] **Prepare custom demo** based on their specific problem
- [ ] **Send reminder** 1 day before demo

### Medium (0.5 - 0.8):
- [ ] **Identify gap**: Which dimension scored low? Address in follow-up
- [ ] **If Authority low**: Schedule decision-maker call
- [ ] **If Budget low**: Send ROI/value prop email
- [ ] **If Urgency low**: Set follow-up in 2-4 weeks
- [ ] **If Problem low**: Send educational content, follow up in 30 days
- [ ] **If Solution Fit low**: Assess if gap is bridgeable

### Low (< 0.5):
- [ ] **Disqualify politely**: "Based on what you've shared, I don't think we're the right fit right now because {reason}"
- [ ] **Provide alternative**: Competitor recommendation or free resource
- [ ] **Add to nurture list**: Quarterly check-in
- [ ] **Log disqualification**: threads/sales/disqualified-{date}.csv with reason
- [ ] **Re-engagement timeline**: 6-12 months (if applicable)

---

## Call Script Reference

**Opening** (1 min):
"Hi {Name}, thanks for taking the time. I know you're busy, so I'll keep this brief. I've done some research on {Company}, and I'm curious to learn more about {problem area}. Does that sound good?"

**Qualification** (5 min):
[Ask Problem Fit questions, listen actively, take notes]

**Problem Exploration** (15 min):
[Deep dive into their problem, quantify impact, understand alternatives]

**Light Pitch** (5 min):
"Based on what you've shared, I think we might be able to help. We work with companies like {similar company} to {solve problem}. Would you be open to seeing a quick demo?"

**Next Steps** (4 min):
[Based on qualification score, propose appropriate next step]
```

## Constraints

### Qualification Questions MUST Map to ICP

**Requirement**: All qualification questions must tie back to ICP criteria

**Example validation**:
```
ICP criteria: Company size 50-200 employees
Qualification question: "How large is your team?" (Solution Fit dimension)

ICP criteria: 20%+ return rates
Qualification question: "What's your current return rate?" (Problem Fit dimension)

ICP criteria: Shopify platform
Qualification question: "What e-commerce platform are you on?" (Solution Fit dimension)
```

**If ICP criteria not addressed**: Add question to qualification framework

### Scoring MUST Be Objective

**Requirement**: Scores based on specific answers, not gut feelings

**Objective scoring example**:
```
Question: "What's your return rate?"
Answer: "25-30%"
ICP threshold: 20%+
Score: 1.0 (clear problem, quantified, above threshold)
```

**Subjective scoring example (WRONG)**:
```
Question: "What's your return rate?"
Answer: "I'm not sure exactly"
Feeling: "They seemed really interested"
Score: 0.8 (based on feeling, not data)
→ WRONG: Should be 0.5 or lower (problem not quantified)
```

**Rule**: If answer is vague, score must be lower (0.5 or below)

### Next Steps MUST Be Specific

**Requirement**: Specific action with timeline, not vague "follow up later"

**Specific next step examples**:
```
✓ "Schedule demo for Tuesday 2pm"
✓ "Send ROI calculator by EOD today, follow up Friday"
✓ "Reconnect in 2 weeks (April 15) to see if priority has shifted"
✓ "Disqualify, add to nurture list for Q3 check-in (July 1)"
```

**Vague next step examples (WRONG)**:
```
✗ "Follow up later"
✗ "Send them some stuff"
✗ "Check back in when they're ready"
✗ "Stay in touch"
```

**Rule**: Every next step must have WHO, WHAT, WHEN

### Disqualification MUST Include Reason

**Requirement**: Log specific disqualification reason for pattern detection

**Good disqualification reasons**:
```
✓ "Company size: 20 employees (ICP: 50-200)"
✓ "No problem: Return rate 5% (ICP threshold: 20%+)"
✓ "Wrong platform: Magento (ICP: Shopify)"
✓ "No budget: $0 allocated, can't justify cost"
✓ "No urgency: Timeline 6+ months, no catalyst"
```

**Vague disqualification reasons (WRONG)**:
```
✗ "Not a fit"
✗ "Bad timing"
✗ "Didn't feel right"
✗ "They said no"
```

**Rule**: Reason must reference specific ICP criteria or qualification dimension

**Why**: Pattern detection (are we targeting wrong companies? Do we need to adjust ICP?)

## Error Handling

**No ICP found**:
- Check `research/customer/icp/{segment}-icp.md` exists
- Return error: "ICP not found for {segment}. Generate ICP first using icp-generator skill."

**No call scripts found**:
- Check `artifacts/sales/{segment}/materials/call-scripts.md` exists
- Return error: "Call scripts not found. Generate sales materials first using materials-generation skill."

**Invalid company_domain**:
- Validate domain format (no http://, just domain.com)
- Return error: "Invalid domain format. Use 'company.com' not 'http://company.com'"

**Missing qualification questions in ICP**:
- Check ICP has `qualification_questions` section
- Return error: "ICP missing qualification_questions section. Update ICP."

## Quality Validation

**Before finalizing call prep, verify**:
- [ ] All qualification dimensions have 3-5 questions
- [ ] Questions map to ICP criteria
- [ ] Scoring guide is objective (specific answer → specific score)
- [ ] Objection handling includes common objections (price, timing, competition)
- [ ] Next steps are specific (WHO, WHAT, WHEN)
- [ ] Pre-call research checklist covers website, LinkedIn, industry, problem signals

**Output review**:
- [ ] Call prep is comprehensive (can use as standalone guide)
- [ ] Scoring math is correct (weighted average calculation)
- [ ] Qualification thresholds are clear (>0.8, 0.5-0.8, <0.5)
- [ ] Objection responses are consultative (not defensive)

## References

See `references/` directory for:
- `qualification-criteria.md`: Pete Kazanjy's qualification dimensions (BANT + Problem/Solution Fit)
- `objection-patterns.md`: Common objections and response frameworks (Feel-Felt-Found, LAER, etc.)
