---
name: marketing-content-delivery
description: Publish content and track performance based on GTM motion. Use when content approved for publishing, tracking performance, or amplifying engagement.
allowed-tools: "Read,Write,Bash"
---

# Content Delivery

Publish content and track what matters for your GTM motion.

## Core Principle

Distribution and tracking serve strategy. Different modes need different metrics. Mode is determined by orchestrator.

## Prerequisites

**Required:**

| File | Purpose | If Missing |
|------|---------|------------|
| Approved drafts | Content to publish | Cannot proceed |

**Note:** This skill does not read `15.go-to-market.md` directly. It receives `mode` from orchestrator.

## Input

| Parameter | Required | Description |
|-----------|----------|-------------|
| `drafts_path` | Yes | Path to approved drafts |
| `campaign_slug` | Yes | Campaign identifier |
| `channels` | Yes | Target channels |
| `piece_name` | Yes | Content identifier |
| `mode` | Yes | From orchestrator: `loop-driven`, `marketplace-driven`, or `sales-driven` |

**Mode is required.** If missing → Stop, flag "Invoke via marketing-execution orchestrator"

**Mode-specific:**

| Mode | Additional |
|------|------------|
| loop-driven | `loop_trigger`, `first_comment` |
| marketplace-driven | `platform` |
| sales-driven | `sales_stage`, `portal_path` |

---

## Mode: Loop-Driven (PLG, Content-Led)

### Publish

**LinkedIn:**
```markdown
Output: artifacts/{slug}/distribution/{piece}-linkedin.md

{Hook — first 2 lines visible}

{Body}

{Loop trigger}

---
First comment (within 5 min):
"{first_comment}"
```

**Blog:**
```markdown
Output: artifacts/{slug}/{piece}.md

---
title: "{title}"
description: "{meta}"
date: "{date}"
---

{Content with loop trigger at end}
```

**Email:**
```markdown
Output: artifacts/{slug}/distribution/{piece}-email.md

Subject: {subject}
Preview: {preview}

{Body}

{Loop trigger — reply invitation}
```

**Twitter/X:**
```markdown
Output: artifacts/{slug}/distribution/{piece}-twitter.md

1/ {Hook}
2/ {Insight}
3/ {Method}
4/ {Loop trigger}
```

### Track

| Track | Ignore |
|-------|--------|
| Shares | Impressions |
| Implementations | Likes |
| DMs | Followers |
| UGC | Page views alone |

### Schedule

| Day | Action |
|-----|--------|
| 1 | First-comment engagement |
| 3 | Loop activations |
| 7 | Performance report |
| 14 | UGC detection |
| 30 | Final assessment |

### Amplify UGC

```markdown
## Loop Fuel Detected

**User:** {handle}
**Content:** {description}

Actions:
- [ ] Comment on their post
- [ ] Reshare with commentary
- [ ] Feature in next content
```

### Output

```markdown
# Loop Performance: {piece}

| Metric | Day 1 | Day 7 | Day 30 |
|--------|-------|-------|--------|
| Shares | | | |
| Implementations | | | |
| DMs | | | |
| UGC | | | |

**Assessment:**
- Loop activated: {yes/no}
- Loop velocity: {time to UGC}
- Loop strength: {weak/medium/strong}
```

---

## Mode: Marketplace-Driven (Partner-Led)

### Publish

**App Store Listing:**
```markdown
Output: artifacts/{slug}/marketplace/{platform}-listing.md

Title: {title}
Tagline: {tagline}
Description: {description}
Keywords: {keywords}
```

**Changelog:**
```markdown
Output: artifacts/{slug}/marketplace/changelog-{version}.md

## {Version} — {Date}

### New
- {feature}

### Improved
- {improvement}

### Fixed
- {fix}
```

**Support:**
```markdown
Output: artifacts/{slug}/marketplace/support/{topic}.md

# {Title}
{Clear, actionable content}
```

### Track

| Track | Ignore |
|-------|--------|
| Install velocity | Page views |
| Rating | Impressions |
| Reviews | Social shares |
| Uninstall rate | Likes |
| Keyword rankings | |

### Schedule

| Timeframe | Action |
|-----------|--------|
| Daily | Installs, rating |
| Weekly | Reviews, rankings |
| Monthly | Trends |

### Review Response

```markdown
## Review Response Needed

**Rating:** {stars}
**Content:** "{text}"

**Response:** {template}

**SLA:** 24 hours
```

### Output

```markdown
# Marketplace Performance: {platform}

| Metric | This Week | Last Week | Trend |
|--------|-----------|-----------|-------|
| Installs | | | |
| Rating | | | |
| Reviews | | | |
| Uninstalls | | | |

**Ranking:** {keyword positions}

**Reviews:** {themes}
```

---

## Mode: Sales-Driven (SLG)

### Publish

**Case Study:**
```markdown
Output: artifacts/{slug}/sales/{customer}-case-study.md

Distribution:
- Sales portal: {path}
- Website (gated): {url}
```

**One-Pager:**
```markdown
Output: artifacts/{slug}/sales/{topic}-one-pager.md

Distribution:
- Sales portal: {path}
```

**Sequence:**
```markdown
Output: artifacts/{slug}/sales/sequences/{name}/

email-1.md
email-2.md
email-3.md

Load into: {tool}
```

**Battle Card:**
```markdown
Output: artifacts/{slug}/sales/battlecards/{competitor}.md

Distribution:
- Sales portal (internal)
```

### Track

| Track | Ignore |
|-------|--------|
| Content delivered to portal | Raw downloads |
| Content accessed by sales | Page views |
| Sales feedback received | Social shares |

**Note:** Pipeline influenced, deals closed, win/loss = Sales skill responsibility. Marketing tracks content availability and usage, not deal outcomes.

### Schedule

| Timeframe | Action |
|-----------|--------|
| Weekly | Content accessed |
| Monthly | Sales feedback |
| Quarterly | Content refresh needs |

### Content Tracking

```markdown
## Sales Content Delivery: {piece}

**Delivered:** {date}
**Location:** {portal path}

| Metric | This Week | Total |
|--------|-----------|-------|
| Accessed by sales | | |
| Feedback received | | |

**Sales Feedback:** {comments}

**Refresh needed:** {yes/no, why}
```

### Output

```markdown
# Sales Content Delivery: {period}

| Content | Delivered | Accessed | Feedback |
|---------|-----------|----------|----------|
| | | | |

**Active in portal:** {count}
**Needs refresh:** {list}
**Sales requests:** {list}
```

---

## Output: distribution-metadata.yaml

```yaml
campaign: {slug}
piece: {piece}
mode: {mode}
published: {datetime}

channels:
  {channel}:
    file: {path}
    url: {url}

tracking:
  schedule: {schedule}
  metrics: {list}

status: {status}
```

---

## Human Touchpoints

### Loop-Driven

```markdown
## Ready to Publish

**{Title}**

Files: {list}

**First-comment (WITHIN 5 MIN):**
> {text}

Action:
1. Publish
2. First-comment immediately
3. Add URLs
4. Confirm
```

### Marketplace-Driven

```markdown
## Ready to Publish

**{Title}**

Files: {list}

Action:
1. Update listing
2. Submit for review
3. Monitor installs
4. Respond to reviews (24h)
```

### Sales-Driven

```markdown
## Ready to Publish

**{Title}**

Files: {list}

Action:
1. Upload to portal
2. Notify sales
3. Add to sequences
4. Track usage
```

---

## Error Handling

| Mode | Condition | Action |
|------|-----------|--------|
| Loop | First-comment missed | Alert |
| Loop | No activations Day 7 | Flag |
| Marketplace | Rating drops | Alert |
| Marketplace | Negative review | Flag |
| Sales | Not used 30 days | Flag |
| All | Wrong mode | Allow override |

## Boundaries

**DO:**
- Apply mode-appropriate tracking
- Format for each channel
- Report mode-appropriate metrics

**DON'T:**
- Track loops for sales content
- Track pipeline for content-led
- Apply one-size-fits-all