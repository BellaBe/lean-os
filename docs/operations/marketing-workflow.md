# Marketing Workflow

Marketing is **learning-driven, not calendar-driven**. Content is created when business generates insights worth sharing. Distribution is **loop-driven, not funnel-driven**.

## Core Principles

> "Great product is not enough. Distribution wins."
> "Loops are so much better than funnels."

- Every piece of content must generate its own next input
- Velocity framing (before → after) in all content
- Track loop activations, not vanity metrics
- SEO is optional, loops are required

---

## Phase 1: Strategy (Once Per Product)

### Generate Marketing Narrative
```
Skill: marketing-narrative
Input: Canvas + Sales narratives (optional)
Output: artifacts/marketing/narrative/
  ├── distribution-model.md (loops, channels, velocity)
  ├── brand-voice.md (how we sound)
  ├── positioning.md (what we stand for)
  ├── content-pillars.md (3-5 strategic themes)
  ├── channel-guidelines.md (format specs)
  └── patterns/
      ├── loop-content.md (required for all content)
      ├── blog.md
      ├── case-study.md
      └── linkedin.md
```

**Distribution model defines:**
- What's dying (SEO, social + links)
- What's working (founder socials, loops, velocity)
- Loop mechanics for each content type
- Channel investment priorities
- Content triggers (learning-driven, not calendar)

**Brand voice:**
- Educational, not promotional
- Technical depth included
- Data-driven (specific metrics)
- No engagement bait

**Channel priorities (from distribution physics):**

| Channel | Investment | Loop Potential |
|---------|------------|----------------|
| Founder LinkedIn | HIGH | High — DMs, reshares |
| Email | MEDIUM | Medium — replies |
| Blog/SEO | LOW | Low — passive |
| Twitter/X | MEDIUM | High — quote tweets |

---

## Phase 2: Content Discovery (Continuous)

### Trigger: Loop Opportunity Detected
```
Skill: content-strategy

Scans for:
- User implements our method → Feature their before/after
- Community question answered → Expand to article
- Client success documented → Case study
- Strategic insight validated → Thought leadership
- Someone shares our content → Engage, amplify

Scoring:
Impact = (Loop Potential × Velocity Story × Audience Alignment) / 3

Thresholds:
- ≥0.7: Flag immediately
- 0.5-0.7: Backlog
- <0.5: Skip
```

**Output to ops/today.md:**
```markdown
### Loop Opportunity [Priority: 0.85]
Topic: {topic}
Source: {thread}
Loop mechanic: {how it loops}
Velocity proof: {before → after available}
Action: Approve to create campaign thread?
```

---

## Phase 3: Content Execution (Thread-Driven)

### Marketing Campaign Thread
```
threads/marketing/campaigns/{campaign-slug}/
├── metadata.yaml
├── 1-input.md (trigger — what learning occurred)
├── 2-hypothesis.md (content performance hypothesis)
├── 3-implication.md (expected loop activations)
├── 4-decision.md (content plan with loop design)
├── 5-actions/
│   ├── execution-log.md (progress + loop tracking)
│   └── drafts/ (temp, deleted after publish confirmed)
└── 6-learning.md (loop performance learnings)
```

### Stage 4: DECISION (Content Plan)

**Must include:**
- Content pieces to create
- Loop trigger type for each (implementation / question / challenge / offer)
- Velocity proof (before → after with time)
- First-comment text (for LinkedIn)
- Target channels (from distribution-model.md)

### Stage 5: ACTIONS (Execution)
```
Skill: marketing-execution
Subskills: content-generation, content-delivery, seo-optimization (optional)
```

**Workflow:**

| Step | Action | Subskill | Human |
|------|--------|----------|-------|
| 1 | Generate drafts with loop triggers | content-generation | — |
| 2 | Validate loop trigger + velocity | — | — |
| 3 | Flag for review | — | Review |
| 4 | Apply SEO (if blog, if requested) | seo-optimization | — |
| 5 | Format for channels | content-delivery | — |
| 6 | Flag "Ready to publish" | — | Publish |
| 7 | Post first-comment (LinkedIn) | — | Post |
| 8 | Confirm published, add URLs | — | Confirm |
| 9 | Delete drafts | — | — |
| 10 | Start loop tracking | content-delivery | — |

**Loop tracking schedule:**
- Day 1: First-comment engagement, early shares
- Day 3: Initial loop activations
- Day 7: Loop performance report
- Day 14: UGC detection
- Day 30: Final loop assessment

**Human touchpoints:**

1. **Draft review** — Validate loop trigger present, velocity proof, brand voice
2. **Pre-publish** — Review files, prepare first-comment
3. **Publish + first-comment** — Post within 5 minutes
4. **Loop fuel** — Amplify user-generated content when detected

### Stage 6: LEARNING (Loop Performance)
```markdown
# Learning - {Campaign Name}

## Loop Performance Summary

| Piece | Loop Activated | Activations | UGC Generated |
|-------|---------------|-------------|---------------|
| {piece} | yes/no | {count} | {count} |

## Metrics That Matter

| Track | Ignore |
|-------|--------|
| Shares | Impressions |
| Implementations | Likes |
| Inbound DMs | Followers |
| User-generated content | Page views alone |

## What Worked
- {Loop trigger observation}
- {Velocity proof effectiveness}

## What Didn't Work
- {Weak trigger analysis}

## Recommendations
1. {For next campaign}

## Update to distribution-model.md
{If learnings warrant}
```

---

## Marketing Execution Subskills

### content-generation
- **Requires:** distribution-model.md, brand-voice.md, positioning.md, patterns/
- **Input:** Content opportunity + source material
- **Output:** Drafts with loop triggers + velocity framing
- **Validation:** Loop trigger present, velocity proof included
- **Human review:** Technical accuracy, brand voice

### content-delivery
- **Input:** Approved drafts + loop trigger + first-comment
- **Output:** Channel-formatted files in artifacts/
- **Post-publish:** Loop tracking initiated
- **Tracking:** Shares, implementations, DMs, UGC
- **Amplification:** Flag user-generated content for action

### seo-optimization (Optional)
- **When:** Blog content, evergreen, explicitly requested
- **Skip:** Social-first, time-sensitive, loop mechanics priority
- **Note:** SEO is dying channel — loops matter more

---

## Loop Mechanics

### Content Loop
```
Create content about solving problem
         ↓
Reader with same problem resonates
         ↓
Engages (comment, DM, share)
         ↓
Tries solution / hires / buys
         ↓
Gets result
         ↓
Shares their result (user-generated)
         ↓
We amplify their story
         ↓
New readers discover...
```

### Loop Trigger Types

| Type | Best For | Example |
|------|----------|---------|
| Implementation | Tutorials, frameworks | "Try this and share your result" |
| Question | Insights, observations | "What's your version of this?" |
| Challenge | Methods, templates | "Rewrite yours. Tag me." |
| Offer | Problem posts | "Facing this? DM me" |

### Velocity Framing

Required in every piece:
```
{Time period} to {old way}.
{Shorter time} to {new way}.
```

Examples:
- "Three weeks to build. Twenty minutes to realize it was wrong."
- "Days of writing. Minutes of review."

### First-Comment (LinkedIn Critical)

Post within 5 minutes of publishing. Algorithm rewards early engagement.

**Examples:**
- "What's your version of this problem?"
- "Try this framework and share your rewrite below"
- "Facing this? What have you tried?"

---

## Closed-Loop Attribution

### Learning → Content → Learning
```
Sales/Business thread completes Stage 6
    ↓
content-strategy detects opportunity
    ↓
Human approves
    ↓
Marketing thread created (1-input through 4-decision)
    ↓
marketing-execution invoked
    ↓
Content published with loop triggers
    ↓
Loop activations tracked
    ↓
UGC amplified (loop fuel)
    ↓
New leads/conversations generated
    ↓
New threads created
    ↓
Loop continues
```

---

## Performance Metrics

### What to Track (Loop Metrics)

| Metric | Definition |
|--------|------------|
| Shares | Reposts, quote tweets |
| Implementations | Users trying the method |
| Inbound DMs | Conversations started |
| User-generated content | Others creating based on ours |
| Loop velocity | Time from publish to first UGC |

### What to Ignore (Vanity Metrics)

| Metric | Why Ignore |
|--------|------------|
| Impressions | Doesn't indicate value |
| Likes | Low-effort, no loop |
| Follower count | Lagging indicator |
| Page views alone | Without conversion meaningless |

### Success Definition

**Success = Loops activated, not content published.**