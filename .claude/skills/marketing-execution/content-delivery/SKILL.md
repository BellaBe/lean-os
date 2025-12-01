---
name: content-delivery
description: Publish content with loop triggers and track loop activations. Use when: content approved for publishing, need to post first-comment, tracking loop performance, or amplifying user-generated content. Combines distribution and performance tracking with loop focus.
allowed-tools: "Read,Write,Bash"
---

# Content Delivery

Publish content designed to loop. Track what matters — loop activations, not impressions.

## Core Principle

> "Loops > Funnels. Publish → Activate Loop → Amplify → Repeat"

Distribution and tracking are one cycle, not separate phases.

## Input

| Parameter | Required | Description |
|-----------|----------|-------------|
| `drafts_path` | Yes | Path to approved drafts |
| `campaign_slug` | Yes | Campaign identifier |
| `channels` | Yes | Array of target channels |
| `piece_name` | Yes | Content identifier |
| `loop_trigger` | Yes | The trigger text to activate loop |
| `first_comment` | Yes (LinkedIn) | Question/challenge for first comment |

## Process

### Phase 1: Publish

#### For Each Channel

**Blog:**
```markdown
Output: artifacts/{slug}/{piece}.md

Format:
---
title: "{title}"
description: "{meta}"
date: "{date}"
---

{Content}

---

{Loop trigger at end}
```

**LinkedIn:**
```markdown
Output: artifacts/{slug}/distribution/{piece}-linkedin.md

Format:
{Hook — first 2 lines visible}

{Body — insight, velocity proof}

{Loop trigger}

---

First comment (post immediately):
"{first_comment}"
```

**Critical:** First comment must be posted within 5 minutes of publishing. Algorithm rewards early engagement.

**Email:**
```markdown
Output: artifacts/{slug}/distribution/{piece}-email.md

Format:
Subject: {subject}
Preview: {preview}

{Body}

{Loop trigger — reply invitation}
```

**Twitter/X:**
```markdown
Output: artifacts/{slug}/distribution/{piece}-twitter.md

Format:
Thread:
1/ {Hook with velocity proof}
2/ {Key insight}
3/ {Method/framework}
4/ {Result}
5/ {Loop trigger — quote tweet invitation}
```

#### Output: distribution-metadata.yaml
```yaml
campaign: {slug}
piece: {piece-name}
published: {datetime}
channels:
  blog:
    file: {piece}.md
    url: {to be filled by human}
    loop_trigger: "{trigger text}"
  linkedin:
    file: distribution/{piece}-linkedin.md
    url: {to be filled by human}
    first_comment: "{comment text}"
    first_comment_posted: false
  email:
    file: distribution/{piece}-email.md
    sent: false
    segment: {segment}
status: ready_to_publish
```

### Phase 2: Activate Loop

**Human publishes, then:**

1. Posts first comment on LinkedIn (within 5 min)
2. Updates distribution-metadata.yaml with URLs
3. Confirms published

**Skill then:**

1. Marks `first_comment_posted: true`
2. Starts loop monitoring
3. Sets tracking schedule

### Phase 3: Track Loop Activations

**What to track (important):**

| Metric | Definition | Why It Matters |
|--------|------------|----------------|
| Shares | Reposts, quote tweets | Content spreading |
| Implementations | Users trying the method | Loop activating |
| Inbound DMs | Conversations started | Qualified interest |
| User-generated content | Others creating based on ours | Loop fuel |
| Replies to loop trigger | Direct responses | Engagement quality |

**What to ignore (vanity):**

| Metric | Why Ignore |
|--------|------------|
| Impressions | Doesn't indicate value |
| Likes | Low-effort, no loop |
| Follower count | Lagging indicator |
| Page views alone | Without conversion meaningless |

**Tracking schedule:**

| Timeframe | Action |
|-----------|--------|
| Day 1 | Check first-comment engagement, early shares |
| Day 3 | First loop activation check |
| Day 7 | Loop performance report |
| Day 14 | Identify UGC for amplification |
| Day 30 | Final loop assessment |

### Phase 4: Amplify Loop Fuel

**When user-generated content detected:**
```markdown
## Loop Fuel Detected

**User:** {name/handle}
**Platform:** {where}
**Content:** {what they created}
  - Implementation of our method
  - Before/after using our framework
  - Quote/reshare with commentary

**Amplification actions:**
- [ ] Comment on their post (engage authentically)
- [ ] Reshare with your commentary (amplify)
- [ ] DM to thank them (relationship)
- [ ] Feature in next content (loop continues)

**Priority:** {high if influential, medium otherwise}
```

**This is the loop completing.** Don't miss it.

## Output: Loop Performance Report
```markdown
# Loop Performance: {piece}

**Published:** {date}
**Channels:** {list}
**Loop trigger:** "{trigger text}"

## Loop Activations

| Metric | Day 1 | Day 7 | Day 30 |
|--------|-------|-------|--------|
| Shares | | | |
| Implementations shared | | | |
| Inbound DMs | | | |
| User-generated content | | | |
| Replies to trigger | | | |

## Conversations Generated

| Date | Person | Channel | Context | Status |
|------|--------|---------|---------|--------|
| | | | | |

## Loop Fuel (UGC)

| User | What They Created | Amplified? | Result |
|------|-------------------|------------|--------|
| | | | |

## Loop Assessment

**Loop activated:** {yes/no}
**Loop velocity:** {time from publish to first UGC}
**Loop strength:** {weak/medium/strong}

**What worked:**
- {observation}

**What didn't:**
- {observation}

**Next content should:**
- {recommendation}
```

## Channel Priorities

From distribution-model.md:

| Channel | Investment | Loop Potential |
|---------|------------|----------------|
| LinkedIn (founder) | HIGH | High — comments, DMs, reshares |
| Email | MEDIUM | Medium — replies, forwards |
| Blog | LOW | Low — passive consumption |
| Twitter/X | MEDIUM | High — quote tweets, threads |

**Prioritize channels with loop mechanics.** Blog is for SEO long-tail (dying), not loops.

## Human Touchpoints

**Before publish:**
```markdown
## Ready to Publish

**{Title}**

Files:
- Blog: artifacts/{slug}/{piece}.md
- LinkedIn: artifacts/{slug}/distribution/{piece}-linkedin.md

Loop activation:
- Trigger in content: "{trigger}"
- First comment: "{comment}"

Action:
1. Publish to each channel
2. Post first comment on LinkedIn IMMEDIATELY
3. Add URLs to distribution-metadata.yaml
4. Confirm published
```

**After UGC detected:**
```markdown
## Loop Fuel — Action Required

**User:** @{handle}
**Created:** {description}

Actions:
- [ ] Comment on their post
- [ ] Reshare with commentary
- [ ] Consider for next content feature
```

## Error Handling

| Condition | Action |
|-----------|--------|
| First comment not posted | Alert — critical for LinkedIn algorithm |
| No loop activations by Day 7 | Flag in 6-learning.md, analyze trigger |
| UGC detected | Flag immediately for amplification |
| High engagement, no conversions | Analyze audience quality |

## Boundaries

**DO:**
- Format content for each channel
- Include loop triggers in all outputs
- Track loop activations (shares, DMs, UGC)
- Flag user-generated content for amplification
- Report on conversations, not impressions

**DON'T:**
- Track vanity metrics (likes, impressions)
- Skip first-comment on LinkedIn
- Miss user-generated content
- Treat distribution and tracking as separate