---
name: marketing-execution
description: Motion-aware marketing campaign orchestrator. Use when: campaign has approved 4-decision.md, content needs generating/publishing, or tracking performance. Reads GTM motion from 15.go-to-market.md and coordinates subskills accordingly. Handles loop-driven, marketplace-driven, and sales-driven workflows.
allowed-tools: "Read,Write,Bash"
---

# Marketing Execution Orchestrator

Execute campaigns that serve your GTM motion.

## Core Principle

Execution adapts to motion. Loop tracking for content-led, review generation for partner-led, pipeline attribution for sales-led.

## Subskills

| Subskill | Purpose | When Used |
|----------|---------|-----------|
| `content-generation` | Generate drafts | All modes |
| `content-delivery` | Publish + track | All modes |
| `channel-optimization` | Optimize channels | When channel needs improvement |

## Prerequisites

**Required:**
- `strategy/canvas/15.go-to-market.md` — Motion, channels, stage
- `artifacts/marketing/narrative/brand-voice.md` — Voice guidelines
- `artifacts/marketing/narrative/positioning.md` — Positioning
- `threads/marketing/campaigns/{slug}/4-decision.md` — Approved content plan

If missing → Flag which file needed

## Motion Detection

Before invoking subskills:

```python
gtm = read("strategy/canvas/15.go-to-market.md")

if gtm.motion in ["PLG", "Content-Led"]:
    mode = "loop-driven"
elif gtm.motion == "Partner-Led":
    mode = "marketplace-driven"
elif gtm.motion == "SLG":
    mode = "sales-driven"
else:
    mode = "hybrid"
```

Pass `mode` to all subskill invocations.

## Campaign Structure

```
threads/marketing/campaigns/{slug}/
├── 4-decision.md         # Content plan
├── 5-actions/
│   ├── execution-log.md  # Progress tracking
│   └── drafts/           # Temporary
└── 6-learning.md         # Performance learnings

artifacts/marketing/campaigns/{slug}/
├── {piece}.md            # Final content
└── distribution/         # Channel-formatted versions
```

---

## Workflow: Loop-Driven (PLG, Content-Led)

### Steps

| Step | Action | Subskill | Human |
|------|--------|----------|-------|
| 1 | Read 4-decision.md | — | — |
| 2 | Generate drafts with loop triggers | content-generation | — |
| 3 | Validate loop trigger + velocity | — | — |
| 4 | Flag for review | — | Review |
| 5 | Format for channels | content-delivery | — |
| 6 | Flag "Ready to publish" | — | Publish |
| 7 | Post first-comment (LinkedIn) | — | Post |
| 8 | Confirm published, add URLs | — | Confirm |
| 9 | Delete drafts | — | — |
| 10 | Start loop tracking | content-delivery | — |

### 4-decision.md Must Include

- Content pieces to create
- Loop trigger type (implementation/question/challenge/offer)
- Velocity proof (before → after)
- First-comment text (LinkedIn)
- Target channels

### Validation

Before proceeding past Step 3:
- [ ] Loop trigger present at end of each draft
- [ ] Velocity proof in content
- [ ] Brand voice applied

If loop trigger missing → Reject, re-invoke content-generation

### Tracking Schedule

| Day | Action |
|-----|--------|
| 1 | First-comment engagement, early shares |
| 3 | Initial loop activations |
| 7 | Loop performance report |
| 14 | UGC detection |
| 30 | Final assessment |

### Metrics

| Track | Ignore |
|-------|--------|
| Shares | Impressions |
| Implementations | Likes |
| Inbound DMs | Followers |
| User-generated content | Page views alone |

---

## Workflow: Marketplace-Driven (Partner-Led)

### Steps

| Step | Action | Subskill | Human |
|------|--------|----------|-------|
| 1 | Read 4-decision.md | — | — |
| 2 | Generate marketplace content | content-generation | — |
| 3 | Validate platform guidelines | — | — |
| 4 | Flag for review | — | Review |
| 5 | Optimize listing (if applicable) | channel-optimization | — |
| 6 | Flag "Ready to publish" | — | Publish |
| 7 | Update listing/publish support content | — | Update |
| 8 | Start marketplace tracking | content-delivery | — |

### 4-decision.md Must Include

- Content type (listing/changelog/support/review-prompt)
- Platform (Shopify/Chrome/etc)
- Keywords (if listing)
- Success metrics

### Validation

Before proceeding past Step 3:
- [ ] Character limits met
- [ ] Keywords included naturally
- [ ] Platform guidelines followed

### Tracking Schedule

| Timeframe | Action |
|-----------|--------|
| Daily | Install velocity, rating changes |
| Weekly | Review responses, keyword rankings |
| Monthly | Trend analysis |

### Metrics

| Track | Ignore |
|-------|--------|
| Install velocity | Page views |
| Rating average | Social shares |
| Review count | Likes |
| Keyword rankings | |
| Uninstall rate | |

---

## Workflow: Sales-Driven (SLG)

### Steps

| Step | Action | Subskill | Human |
|------|--------|----------|-------|
| 1 | Read 4-decision.md | — | — |
| 2 | Generate sales content | content-generation | — |
| 3 | Validate ROI/objections | — | — |
| 4 | Flag for review | — | Review |
| 5 | Format for sales portal | content-delivery | — |
| 6 | Flag "Ready to publish" | — | Publish |
| 7 | Upload to portal, notify sales | — | Upload |
| 8 | Start usage tracking | content-delivery | — |

### 4-decision.md Must Include

- Content type (case-study/one-pager/battle-card/sequence)
- Target persona (user/champion/decision-maker/finance)
- Sales stage (awareness/consideration/decision)
- Key objections addressed

### Validation

Before proceeding past Step 3:
- [ ] ROI/metrics included
- [ ] Objections addressed
- [ ] Single clear CTA
- [ ] Persona-appropriate language

### Tracking Schedule

| Timeframe | Action |
|-----------|--------|
| Weekly | Content usage in deals |
| Monthly | Pipeline attribution |
| Quarterly | Win/loss analysis |

### Metrics

| Track | Ignore |
|-------|--------|
| Content used in deals | Downloads |
| Pipeline influenced | Page views |
| Deals closed with content | Social shares |
| Sales feedback | |

---

## Subskill Invocation

### content-generation

```
Parameters:
  campaign_slug: "{slug}"
  decision_path: "threads/marketing/campaigns/{slug}/4-decision.md"
  mode: "{loop-driven|marketplace-driven|sales-driven}"
  piece_name: "{piece}"
```

### content-delivery

```
Parameters:
  drafts_path: "threads/.../drafts/"
  campaign_slug: "{slug}"
  mode: "{loop-driven|marketplace-driven|sales-driven}"
  channels: ["{from decision}"]
```

### channel-optimization

```
Parameters:
  channel: "{channel to optimize}"
  # Only invoke when channel needs optimization, not per-campaign
```

---

## Human Touchpoints

### After Drafts Ready (All Modes)

```markdown
## Drafts Ready for Review

**Campaign:** {name}
**Mode:** {loop-driven|marketplace-driven|sales-driven}
**Piece:** {title}

**Location:** `threads/marketing/campaigns/{slug}/5-actions/drafts/`

**Validation:**
{Mode-appropriate checklist}

**Action:** Review, approve or request revision
```

### Ready to Publish (Loop-Driven)

```markdown
## Ready to Publish

**{Title}**

Files:
- Blog: artifacts/{slug}/{piece}.md
- LinkedIn: artifacts/{slug}/distribution/{piece}-linkedin.md

**First-comment (POST WITHIN 5 MINUTES):**
> {first_comment text}

**Action:**
1. Publish to each channel
2. Post first-comment on LinkedIn immediately
3. Add URLs to execution-log
4. Confirm published
```

### Ready to Publish (Marketplace-Driven)

```markdown
## Ready to Publish

**{Title}**

Files: {list}

**Action:**
1. Update app store listing
2. Submit for review if required
3. Monitor install velocity
4. Respond to reviews within 24h
```

### Ready to Publish (Sales-Driven)

```markdown
## Ready to Publish

**{Title}**

Files: {list}

**Action:**
1. Upload to sales portal
2. Notify sales team
3. Add to relevant sequences
4. Track usage in deals
```

---

## Execution Log Format

```markdown
# Execution Log - {Campaign Name}

**Campaign:** {slug}
**Mode:** {loop-driven|marketplace-driven|sales-driven}
**Created:** {date}
**Status:** {drafting|review|ready|published|tracking|complete}

---

## Content Piece: "{Title}"

### Design
{Mode-appropriate design details}

### Timeline
- [ ] Drafts created: {date}
- [ ] Validated: {date}
- [ ] Human reviewed: {date}
- [ ] Published: {date}
- [ ] Tracking started: {date}

### Published
{URLs or locations}

### Performance
{Mode-appropriate metrics table}

### Assessment
{Mode-appropriate assessment}
```

---

## 6-learning.md Update

After campaign complete:

```markdown
# Learning - {Campaign Name}

**Mode:** {mode}
**Period:** {start} to {end}

## Performance Summary
{Mode-appropriate metrics}

## What Worked
- {observation}

## What Didn't Work
- {observation}

## Recommendations
1. {recommendation}

## Updates Needed
{Any updates to GTM, narrative, or other artifacts}
```

---

## Error Handling

| Condition | Action |
|-----------|--------|
| GTM file missing | Stop, flag "Run go-to-market first" |
| 4-decision.md missing | Stop, flag "Complete Stage 4 first" |
| Mode mismatch (content doesn't fit motion) | Flag, discuss with human |
| Draft fails validation | Reject, re-invoke content-generation |
| Human delays >48hrs | Reminder in ops/today.md |

## Boundaries

**DO:**
- Read GTM motion first
- Pass mode to all subskills
- Apply mode-appropriate validation
- Track mode-appropriate metrics
- Update 6-learning.md with learnings

**DON'T:**
- Apply loop mechanics to sales content
- Track vanity metrics
- Skip mode detection
- Proceed without motion context
