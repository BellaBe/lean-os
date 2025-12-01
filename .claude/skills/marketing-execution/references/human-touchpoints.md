# Human Touchpoints

## 1. Draft Review

**Trigger:** content-generation completes

**Flag:**
```markdown
## Drafts Ready for Review

**Piece:** {title}
**Location:** threads/.../drafts/

**Validation:**
- Loop trigger: {✓ | ✗}
- Velocity proof: {✓ | ✗}

**Action:** Review and approve
```

**If loop trigger missing:** Do not approve. Request revision.

---

## 2. Pre-Publish

**Trigger:** content-delivery completes

**Flag:**
```markdown
## Ready to Publish

**Piece:** {title}

**Files:**
- Blog: artifacts/{slug}/{piece}.md
- LinkedIn: artifacts/{slug}/distribution/{piece}-linkedin.md

**First-comment (LinkedIn):**
> {comment text}

**Action:**
1. Publish all channels
2. Post first-comment within 5 minutes
3. Add URLs to execution-log
4. Confirm "published"
```

---

## 3. First-Comment Reminder

**Trigger:** Human confirms published but first-comment not noted

**Flag:**
```markdown
## First-Comment Required

**LinkedIn post:** {url}

**Comment to post:**
> {comment text}

**Action:** Post now. Algorithm rewards early engagement.
```

---

## 4. Loop Fuel Amplification

**Trigger:** UGC detected during tracking

**Flag:**
```markdown
## Loop Fuel — Action Required

**User:** {handle}
**Platform:** {where}
**Created:** {description}

**Actions:**
- [ ] Comment on their post
- [ ] Reshare with commentary
- [ ] DM to thank
- [ ] Feature in next content?

**Priority:** {HIGH | MEDIUM}
```

---

## 5. Loop Stalled

**Trigger:** No activations by Day 7

**Flag:**
```markdown
## Loop Not Activating

**Piece:** {title}
**Published:** {date}
**Days since:** 7

**Observed:**
- Shares: 0
- Implementations: 0
- DMs: 0

**Possible issues:**
- Trigger too vague?
- Wrong audience?
- Timing?

**Action:** Review trigger, consider boost or revision
```