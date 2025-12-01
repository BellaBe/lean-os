---
name: marketing-execution
description: Execute marketing campaigns with loop mechanics. Use when: campaign has approved 4-decision.md, content needs generating/publishing, or tracking loop activations. Coordinates content-generation, content-delivery, and optional seo-optimization. Tracks loop activations, not vanity metrics.
allowed-tools: "Read,Write,Bash"
---
# Marketing Execution Orchestrator

Execute campaigns designed for loops. Track what matters — loop activations, not impressions.

## Core Principle

> "Loops > Funnels. Publish → Activate Loop → Amplify → Repeat"

Success = content that generates its own next input.

## Subskills

| Subskill | Purpose | Priority |
|----------|---------|----------|
| `content-generation` | Generate loop-triggering drafts | Required |
| `content-delivery` | Publish + track loop activations | Required |
| `seo-optimization` | Basic SEO for evergreen content | Optional |

## Prerequisites

**Required context:**
- `artifacts/marketing/narrative/distribution-model.md` — Loop mechanics, channel priorities
- `artifacts/marketing/narrative/brand-voice.md` — Voice guidelines
- `threads/marketing/campaigns/{slug}/4-decision.md` — Approved content plan

If missing → Flag "Run marketing-narrative first" or "Complete Stage 4 decision"

## Campaign Structure
```
threads/marketing/campaigns/{slug}/
├── 4-decision.md         # Content plan with loop design
├── 5-actions/
│   ├── execution-log.md  # Progress + loop tracking
│   └── drafts/           # Temporary (delete after publish confirmed)
└── 6-learning.md         # Loop performance learnings

artifacts/marketing/campaigns/{slug}/
├── {piece}.md            # Final article
└── distribution/
    ├── {piece}-linkedin.md
    ├── {piece}-twitter.md
    ├── {piece}-email.md
    └── distribution-metadata.yaml
```

## Workflow

### 1. Read Stage 4 Decision
```
Read: threads/marketing/campaigns/{slug}/4-decision.md

Extract:
- Content pieces to create
- Loop trigger type for each (implementation / question / challenge / offer)
- Velocity proof (before → after)
- Target channels (from distribution-model.md priorities)
- First-comment text (for LinkedIn)
```

### 2. For Each Content Piece

| Step | Action | Subskill | Wait For |
|------|--------|----------|----------|
| a | Generate drafts with loop triggers | `content-generation` | Files in drafts/ |
| b | Validate loop trigger + velocity proof | — | — |
| c | Flag for human review | — | Human approval |
| d | Apply SEO (Only if: blog + evergreen + requested) | `seo-optimization` | Drafts updated |
| e | Format for channels | `content-delivery` | Files in artifacts/ |
| f | Flag "Ready to publish" | — | Human publishes |
| g | Human posts first-comment (LinkedIn) | — | Human confirms |
| h | Delete drafts/ | — | — |
| i | Start loop tracking | `content-delivery` | — |

### 3. Post-Publish: Loop Monitoring

Once human confirms published:

1. Update execution-log.md with publish time + URLs
2. Start loop tracking schedule (Day 1, 3, 7, 14, 30)
3. Monitor for loop activations
4. Flag user-generated content immediately for amplification
5. Update 6-learning.md with loop performance

## Subskill Invocation

### content-generation

**When:** Step 2a — after reading 4-decision.md

**Invoke:**
```
Parameters:
  campaign_slug: "{slug}"
  decision_path: "threads/marketing/campaigns/{slug}/4-decision.md"
  piece_name: "{piece}"
  loop_trigger_type: "{type from decision}"
  velocity_proof: "{before → after from decision}"
```

**Output:**
```
threads/marketing/campaigns/{slug}/5-actions/drafts/
├── {piece}-article.md
├── {piece}-linkedin.md
├── {piece}-twitter.md
└── {piece}-email.md
```

**Validation before proceeding:**
- [ ] Loop trigger present at end of each draft
- [ ] Velocity proof in content
- [ ] Brand voice applied

If loop trigger missing → Reject, re-invoke with explicit requirement

---

### seo-optimization (Optional)

**When:** Step 2d — only if:
- Content type is blog/article
- Explicitly requested, OR
- High-value evergreen content

**Skip if:**
- Social-first content (LinkedIn, Twitter)
- Time-sensitive content
- Loop mechanics more important than SEO

**Invoke:**
```
Parameters:
  draft_path: "threads/.../drafts/{piece}-article.md"
  target_keyword: "{keyword from decision}"
  secondary_keywords: ["{list from decision}"]
```

**Output:** Overwrites draft with SEO metadata + optimizations

**Note:** Low priority per distribution-model.md. SEO is declining channel.

---

### content-delivery

**When:** Step 2e — after human approves drafts

**Invoke:**
```
Parameters:
  drafts_path: "threads/.../drafts/"
  campaign_slug: "{slug}"
  channels: ["{from decision}"]
  piece_name: "{piece}"
  loop_trigger: "{trigger text}"
  first_comment: "{question/challenge for LinkedIn}"
```

**Output:**
```
artifacts/marketing/campaigns/{slug}/
├── {piece}.md
└── distribution/
    ├── {piece}-linkedin.md
    ├── {piece}-twitter.md
    ├── {piece}-email.md
    └── distribution-metadata.yaml
```

**Post-publish tracking:**
- Day 1: Early engagement, first-comment performance
- Day 3: Initial loop activations
- Day 7: Loop performance report
- Day 14: UGC detection
- Day 30: Final loop assessment

## Human Touchpoints

### After content-generation (Step 2c)
```markdown
## Drafts Ready for Review

**Campaign:** {campaign name}
**Piece:** {title}

**Location:** `threads/marketing/campaigns/{slug}/5-actions/drafts/`

**Validation:**
- Loop trigger: {✓ present / ✗ missing}
- Velocity proof: {✓ present / ✗ missing}
- Brand voice: {✓ applied / ⚠️ review needed}

**Files:**
- {piece}-article.md
- {piece}-linkedin.md
- {piece}-twitter.md
- {piece}-email.md

**Action:** Review all drafts, approve or request revision
```

---

### After content-delivery (Step 2f)
```markdown
## Ready to Publish

**Campaign:** {campaign name}
**Piece:** {title}

**Files ready:**
| Channel | File | Loop Trigger |
|---------|------|--------------|
| Blog | artifacts/{slug}/{piece}.md | "{trigger}" |
| LinkedIn | artifacts/{slug}/distribution/{piece}-linkedin.md | "{trigger}" |
| Twitter | artifacts/{slug}/distribution/{piece}-twitter.md | "{trigger}" |
| Email | artifacts/{slug}/distribution/{piece}-email.md | "{trigger}" |

**LinkedIn first-comment (POST WITHIN 5 MINUTES):**
> {first_comment text}

**Action:**
1. Publish to each channel
2. Post first-comment on LinkedIn immediately
3. Add URLs to execution-log.md
4. Reply "published" to confirm
```

---

### After loop activation detected
```markdown
## Loop Fuel Available — Action Required

**Detected:** {date}
**User:** {name/handle}
**Platform:** {LinkedIn/Twitter/etc}
**Content:** {what they created}
  - {description of their implementation/share/commentary}

**Amplification actions:**
- [ ] Comment on their post (authentic engagement)
- [ ] Reshare with your commentary
- [ ] DM to thank them
- [ ] Consider featuring in next content

**Priority:** {HIGH if influential / MEDIUM otherwise}

This is the loop completing. Don't miss it.
```

## Execution Log Format
```markdown
# Execution Log - {Campaign Name}

**Campaign:** {slug}
**Created:** {date}
**Status:** {drafting | review | ready | published | tracking | complete}

---

## Content Piece 1: "{Title}"

### Loop Design
- **Trigger type:** {implementation | question | challenge | offer}
- **Trigger text:** "{exact trigger}"
- **First-comment:** "{LinkedIn comment}"
- **Expected activations:** {what we expect}

### Velocity Proof
- **Before:** {time + old state}
- **After:** {time + new state}
- **Multiplier:** {Nx}

### Execution Timeline
- [ ] Drafts created: {date}
- [ ] Loop trigger validated: ✓
- [ ] Velocity proof validated: ✓
- [ ] Human reviewed: {date}
- [ ] SEO applied: {date | skipped}
- [ ] Channel files created: {date}
- [ ] Human published: {date}
- [ ] First-comment posted: {date}
- [ ] Drafts deleted: {date}
- [ ] Tracking started: {date}

### Published URLs
| Channel | URL | First-Comment |
|---------|-----|---------------|
| Blog | {url} | N/A |
| LinkedIn | {url} | ✓ Posted |
| Twitter | {url} | N/A |
| Email | {sent to segment} | N/A |

### Loop Performance
| Metric | Day 1 | Day 7 | Day 30 |
|--------|-------|-------|--------|
| Shares | | | |
| Implementations shared | | | |
| Inbound DMs | | | |
| User-generated content | | | |
| Conversations started | | | |

### Loop Fuel Generated
| Date | User | What They Created | Amplified | Result |
|------|------|-------------------|-----------|--------|
| | | | | |

### Loop Assessment
- **Loop activated:** {yes | no | partial}
- **Loop velocity:** {time to first UGC}
- **Loop strength:** {weak | medium | strong}
- **Learning:** {what worked/didn't}

---

## Content Piece 2: "{Title}"

(Repeat structure)
```

## Metrics That Matter

| Track (Loop Metrics) | Ignore (Vanity Metrics) |
|---------------------|------------------------|
| Shares / reposts | Impressions |
| Implementations shared | Likes |
| Inbound DMs | Follower count |
| User-generated content | Page views alone |
| Conversations started | Comments (without substance) |
| Referrals / mentions | Reach |

**Success = Loops activated, not content published.**

## Error Handling

| Condition | Action |
|-----------|--------|
| 4-decision.md missing | Stop, flag "Complete Stage 4 first" |
| distribution-model.md missing | Stop, flag "Run marketing-narrative first" |
| Draft missing loop trigger | Reject draft, re-invoke content-generation |
| Draft missing velocity proof | Flag warning, proceed only if human approves |
| First-comment not posted | Alert — critical for LinkedIn algorithm |
| No loop activations by Day 7 | Flag in 6-learning.md, analyze trigger effectiveness |
| UGC detected | Flag immediately for amplification |
| Human delays publish >48hrs | Reminder in ops/today.md |

## 6-learning.md Update

After Day 30 (or campaign complete):
```markdown
# Learning - {Campaign Name}

**Campaign:** {slug}
**Period:** {start} to {end}

## Loop Performance Summary

| Piece | Loop Triggered | Activations | UGC Generated |
|-------|---------------|-------------|---------------|
| {piece 1} | {yes/no} | {count} | {count} |
| {piece 2} | {yes/no} | {count} | {count} |

## What Worked

- {Observation about successful loop trigger}
- {Observation about velocity proof effectiveness}
- {Observation about channel performance}

## What Didn't Work

- {Observation about weak loop trigger}
- {Observation about missed opportunities}

## Hypotheses Validated/Invalidated

| Hypothesis | Status | Evidence |
|------------|--------|----------|
| {H1} | {validated/invalidated} | {data} |

## Recommendations for Next Campaign

1. {Specific recommendation}
2. {Specific recommendation}
3. {Specific recommendation}

## Update to distribution-model.md

{If learnings warrant updating channel priorities or loop mechanics}
```

## Boundaries

**DO:**
- Validate loop triggers in every draft before proceeding
- Ensure first-comment is posted on LinkedIn
- Track loop activations (shares, implementations, DMs, UGC)
- Flag user-generated content immediately for amplification
- Update 6-learning.md with loop performance data
- Feed learnings back to distribution-model.md

**DON'T:**
- Approve drafts without loop triggers
- Skip first-comment on LinkedIn
- Report vanity metrics (impressions, likes, follower count)
- Miss user-generated loop fuel
- Treat SEO as required (it's optional, low priority)
- Delete drafts before human confirms published