# Marketing Measure Template

**Action Type:** `marketing:measure`

## Objective
Track campaign performance and extract insights.

## Process (AI-automated, 7 days post-campaign)

### 1. Metrics Collection (AI-automated)

**Reach:**
- Impressions: {count}
- Unique visitors: {count}
- Audience overlap: {percent}%

**Engagement:**
- CTR: {percent}%
- Time on page: {seconds}s
- Scroll depth: {percent}%
- Social engagement: {likes + comments + shares}

**Conversion:**
- Demo requests: {count}
- Qualified leads: {count}
- Pipeline: ${amount}
- Cost per conversion: ${CPC}

### 2. Attribution Analysis (AI-automated)

**Lead Sources:**
- LinkedIn ads: {count} leads
- Organic LinkedIn: {count} leads
- Blog: {count} leads
- Email: {count} leads
- Direct: {count} leads

**Multi-touch:**
- First touch: {channel}
- Last touch: {channel}
- Assist: {channels}

### 3. Performance vs Targets

**Targets vs Actuals:**
```
| Metric | Target | Actual | Variance |
|--------|--------|--------|----------|
| Reach | {target} | {actual} | {percent}% |
| CTR | {target}% | {actual}% | {percent}% |
| Conversions | {target} | {actual} | {percent}% |
| CPA | ${target} | ${actual} | {percent}% |
```

### 4. Insights Extraction (AI-automated)

**What Worked:**
- {Finding 1 with data}
- {Finding 2 with data}

**What Didn't:**
- {Finding 1 with data}
- {Finding 2 with data}

**Recommendations:**
- {Action 1}
- {Action 2}

## Success Criteria
- [ ] All metrics collected
- [ ] Attribution analysis complete
- [ ] Performance vs targets documented
- [ ] 3-5 actionable insights extracted

## Output Format
```markdown
# Measure: {Campaign Name}
**Date:** {YYYY-MM-DD}
**Campaign period:** {start} - {end}

## Performance Summary

**Reach:** {impressions} impressions, {visitors} unique visitors
**Engagement:** {CTR}% CTR, {time}s avg time
**Conversion:** {demos} demo requests, {qualified} qualified
**Pipeline:** ${amount} (projected ARR)
**ROI:** {multiplier}x (${revenue} / ${cost})

## Target Achievement
- Reach: {actual}/{target} ({percent}%)
- CTR: {actual}%/{target}% ({variance})
- Conversions: {actual}/{target} ({percent}%)
- CPA: ${actual}/${target} ({variance})

## Key Insights
1. {Insight with supporting data}
2. {Insight with supporting data}
3. {Insight with supporting data}

## Recommendations
- {Action 1 for next campaign}
- {Action 2 for optimization}
```

## Typical Duration
**7 days** (performance stabilization + analysis)

## Cost
**$0** (AI-automated analytics)