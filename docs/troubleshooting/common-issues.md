# Common Issues & Solutions

## Marketing Issues

### Content opportunities not detected

**Symptoms:**
- Sales threads complete Stage 6 but no content flagged
- ops/today.md shows no content opportunities
- Expected learning not triggering content

**Diagnosis:**
```bash
# Check thread completion
ls threads/sales/*/6-learning.md

# Check if learning has quantified results
cat threads/sales/{deal}/6-learning.md
```

**Solutions:**
1. Manually trigger content-strategy scan
2. Check priority threshold (opportunities <0.7 won't auto-flag)
3. Verify source thread has validated hypothesis (not just data)
4. Ensure learning includes specific metrics/results

---

### Content draft quality low

**Symptoms:**
- Drafts lack technical depth
- Metrics incorrect or missing
- Voice doesn't match brand guidelines

**Diagnosis:**
```bash
# Check source thread quality
cat threads/sales/{deal}/6-learning.md

# Check brand voice exists
cat artifacts/marketing/narrative/brand-voice.md

# Check content patterns loaded
ls .claude/skills/marketing-execution/content-generation/references/
```

**Solutions:**
1. Improve source thread learning (more specific results)
2. Update brand-voice.md with examples
3. Request revisions with specific feedback
4. Regenerate with corrected information

---

### SEO optimization not working

**Symptoms:**
- Keywords stuffed (density >2%)
- Target keyword not naturally integrated
- Title/meta not optimized

**Diagnosis:**
```bash
# Check target keyword specified
cat threads/marketing/content/{topic}/metadata.yaml

# Check SEO strategy exists
cat artifacts/marketing/narrative/seo-strategy.md
```

**Solutions:**
1. Specify target keyword in metadata
2. Update seo-strategy.md with keyword guidelines
3. Manually edit optimized draft if needed

---

### Content not publishing

**Symptoms:**
- Draft approved but not appearing in artifacts/
- Distribution record missing
- UTM parameters not generated

**Diagnosis:**
```bash
# Check approval status
cat threads/marketing/content/{topic}/metadata.yaml
# status should be "approved" not "draft"

# Check distribution record
ls distribution-record-*.yaml
```

**Solutions:**
1. Verify human approval received
2. Check blog publishing endpoint works (test with simple post)
3. Manually trigger content-distribution if needed
4. Verify UTM parameters in distribution-record.yaml

---

### Performance tracking not updating

**Symptoms:**
- No performance data after 7/30/90 days
- performance.yaml missing or stale
- Attribution not tracking

**Diagnosis:**
```bash
# Check distribution record exists
ls distribution-record-*.yaml

# Check analytics access (if automated)
# May require manual data entry if no API
```

**Solutions:**
1. Manually update performance.yaml if needed
2. Verify analytics tracking codes present
3. Check attribution metadata in sales threads

---

## Sales Issues

### ICP too narrow / Can't find prospects

**Symptoms:**
- prospect-research returns <10 companies
- Observable filters too restrictive
- Segment size smaller than expected

**Solutions:**
1. Relax one filter at a time
2. Expand to adjacent segments
3. Validate segment size was correctly estimated
4. Test broader filters, then refine based on fit

---

### Sales materials don't match brand

**Symptoms:**
- Pitch deck positioning misaligned with Canvas
- Messaging doesn't resonate with ICP
- Technical details incorrect

**Diagnosis:**
```bash
# Check Canvas currency
cat strategy/canvas/07-uvp.md
cat strategy/canvas/04-segments.md

# Check when materials last generated
ls -la artifacts/sales/{segment}/materials/
```

**Solutions:**
1. Update Canvas if positioning changed
2. Regenerate materials with current Canvas
3. Verify ICP still accurate
4. Manual review for technical accuracy

---

### Outreach response rate low (<5%)

**Symptoms:**
- Sent 100 emails, <5 responses
- Prospects not opening emails
- Wrong contacts being reached

**Diagnosis:**
```bash
# Check ICP accuracy
cat research/customer/icp/{segment}-icp.yaml

# Check email templates
cat artifacts/sales/{segment}/materials/email-templates.md

# Check contact quality
cat research/customer/prospects/{segment}-contacts-{date}.csv
```

**Solutions:**
1. Validate ICP (are these the right companies?)
2. Improve subject lines (test variants)
3. Verify contacts are decision-makers
4. Test shorter email copy
5. Add personalization (company-specific details)

---

### Deals stalling in qualification/demo

**Symptoms:**
- High lead volume but low progression
- Prospects ghost after demo
- Qualification score high but no close

**Diagnosis:**
```bash
# Check qualification criteria
cat research/customer/icp/{segment}-qualification.md

# Review stalled deal threads
cat threads/sales/{company}/6-learning.md
```

**Solutions:**
1. Tighten qualification (raise score threshold)
2. Validate problem severity (are they feeling pain?)
3. Check pricing alignment (is it within budget?)
4. Improve demo (focus on specific pain points)
5. Add pilot offering (reduce commitment risk)

---

## Canvas Issues

### Assumptions not being validated

**Symptoms:**
- Confidence scores flat over time
- Stage 6 not updating Canvas
- 10-assumptions.md stale

**Diagnosis:**
```bash
# Check thread completions
ls threads/*/*/6-learning.md

# Check assumption linkage
grep "Tests:" threads/*/*/2-hypothesis.md
```

**Solutions:**
1. Ensure Stage 2 (Hypothesis) links to assumptions
2. Verify Stage 6 includes confidence update
3. Manually update if auto-update failed
4. Check assumption IDs match 10-assumptions.md

---

### Canvas sections conflicting

**Symptoms:**
- UVP doesn't match solution
- Pricing doesn't align with value prop
- Segments don't match ICP definitions

**Solutions:**
1. Run Canvas audit (30 min review of all sections)
2. Update sections to align
3. Regenerate downstream artifacts (ICP, narratives, materials)
4. Document Canvas update in business thread

---

## Thread Issues

### Thread stuck at Stage X

**Symptoms:**
- Thread hasn't progressed in >7 days
- Waiting on external input
- Missing information for next stage

**Diagnosis:**
```bash
# Check last update
ls -la threads/{type}/{name}/

# Check ops/velocity.md for bottlenecks
cat ops/velocity.md
```

**Solutions:**
1. Stage 1-3: Go back, gather missing info
2. Stage 4: Make decision (DEFER if not ready)
3. Stage 5: Check if waiting on human approval
4. Stage 6: Compile available metrics, proceed

---

### Too many threads active

**Symptoms:**
- >20 active threads
- ops/today.md overwhelming
- Human can't keep up with approvals

**Solutions:**
1. Close inactive threads (DEFER decisions)
2. Increase priority threshold (>0.7 → >0.8)
3. Batch content approvals (weekly instead of daily)
4. Focus on fewer segments initially

---

## Operations Dashboard Issues

### ops/today.md not generating

**Symptoms:**
- File missing or stale
- Last update >24 hours ago

**Solutions:**
1. Manually trigger ops-dashboard skill
2. Check thread data exists
3. Verify file permissions

---

### False positives (unnecessary flags)

**Symptoms:**
- Low-priority items flagged as high-priority
- Alerts for non-issues
- Too much noise in ops/today.md

**Solutions:**
1. Raise priority threshold
2. Adjust implication analysis in Stage 3
3. Refine anomaly detection in ops/patterns.md

---

### Missed priorities (should have flagged)

**Symptoms:**
- Important decisions not surfaced
- High-value opportunities buried
- Strategic issues not detected

**Solutions:**
1. Lower priority threshold temporarily
2. Manual review of recent threads
3. Improve Stage 3 (Implication) analysis
4. Add explicit flags in Stage 6

---

## General Troubleshooting Process

1. **Identify symptom:** What's not working?
2. **Check source data:** Canvas current? Thread complete?
3. **Verify skill execution:** Did skill run? Any errors?
4. **Review outputs:** Files generated? Content correct?
5. **Manual override:** Fix immediate issue
6. **Root cause:** Why did it happen?
7. **Prevent recurrence:** Update Canvas, skill, or process

---

## When to Ask for Help

**Skill bugs:**
- Skill produces incorrect outputs consistently
- Skill fails to execute

**Architecture questions:**
- Unsure which skill to use
- Don't understand thread flow
- Canvas structure unclear

**Performance issues:**
- AI autonomy <90%
- Human time >2 hours/day
- Metrics degrading over time

---

For more help, see:
- [FAQ](faq.md)
- [Architecture](../overview/architecture.md)
- [How It Works](../overview/how-it-works.md)