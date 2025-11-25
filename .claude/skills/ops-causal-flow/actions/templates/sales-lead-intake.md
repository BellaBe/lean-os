# Sales Lead Intake Action

**Type:** sales:lead-intake
**Human Required:** No (AI auto-executes)
**Duration:** 1 day

## Purpose
Capture lead data, detect segment, score against ICP, and initialize thread metadata.

## AI Auto-Execution

### Step 1: Capture Lead Data

Extract from input source (email, form, referral):
- Company name
- Company domain
- Contact name
- Contact title
- Contact email
- Lead source (inbound/outbound/referral)
- Initial inquiry/context

### Step 2: Company Research

Use web_search to gather:
- Industry/vertical
- Company size (employee count)
- Revenue estimate (if available)
- Platform/tech stack ({platform}, etc.)
- Geography/headquarters

### Step 3: Segment Detection

Load all ICP files for product:
```bash
research/customer/icp/*.md
```

Score lead against each segment:
- Observable characteristics match (platform, size, geography)
- Problem signals detected (website, reviews, job postings)
- Calculate match score (0.0 to 1.0) per segment

**Assign segment:** Highest scoring ICP
**Minimum threshold:** 0.6 (below = "unsegmented" for human review)

### Step 4: Update Thread Metadata
```json
{
  "segment": "{best-matching-segment}",
  "icp_file": "research/customer/icp/{segment}-icp.md",
  "icp_match_score": 0.85,
  "narrative_path": "threads/sales/narratives/{segment}/",
  "materials_version": "2025-11-14"
}
```

### Step 5: Priority Assignment

Based on ICP match score:
- >= 0.8: High priority (strong ICP fit)
- 0.6-0.8: Medium priority (moderate ICP fit)
- < 0.6: Low priority (poor ICP fit, human review segment assignment)

### Step 6: Create CRM Record

Log in ops/sales-pipeline.md:
- Lead name
- Segment
- ICP score
- Priority
- Next action: sales:qualification

## Output

**Status:** READY_FOR_QUALIFICATION
**Segment:** {detected-segment}
**ICP Score:** {score}
**Priority:** {high|medium|low}

**Next Action:** sales:qualification
