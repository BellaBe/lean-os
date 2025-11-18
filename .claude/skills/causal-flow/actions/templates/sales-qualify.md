# Sales Qualification Action

**Type:** sales:qualification
**Human Required:** Yes
**Duration:** 3-5 days

## Pre-Call Preparation (AI-Generated)

### Step 1: Generate Call Prep

Invoke qualification-support subskill:
```bash
sales-execution:
  activity_type: "qualification"
  product: "{metadata.product}"
  segment: "{metadata.segment}"
  company_name: "{lead.company}"
  company_domain: "{lead.domain}"
```

**Generated outputs:**
- Pre-call research checklist
- Company context summary
- ICP validation questions (from ICP file)
- Qualification scoring framework
- Objection handling guide

### Step 2: Load Materials

**Call script:**
- File: `artifacts/sales/current/call-scripts.md`
- Section: Discovery Call (30-45 min)

**ICP criteria:**
- File: `research/customer/icp/{segment}-icp.md`
- Section: qualification_questions

**One-pager (for follow-up):**
- File: `artifacts/sales/current/one-pager.md`
### Step 3: Auto-Schedule

AI sends calendar invite:
- Duration: 45 min
- Attendees: Lead contact, Bella
- Agenda: Discovery call + ICP validation
- Attach: One-pager PDF

## Discovery Call (Human Execution)

**Duration:** 30-45 min
**Attendees:** Lead contact, Bella
**Script:** Use call-scripts.md (discovery section)

### ICP Validation Framework

Score each dimension (0.0 to 1.0):

**Problem Fit (Weight: 0.3)**
- Do they have the problem we solve?
- Is it quantified? (e.g., "20% return rate")
- Is it a priority?

**Authority (Weight: 0.2)**
- Can this person make buying decisions?
- Who else is involved?
- What's the approval process?

**Budget (Weight: 0.2)**
- Have they allocated budget?
- What's the cost of the problem?
- What's their willingness to pay range?

**Urgency (Weight: 0.15)**
- When do they need this solved?
- What's driving the timeline?
- What happens if they don't solve it?

**Solution Fit (Weight: 0.15)**
- Do they meet our requirements? (platform, size, etc.)
- Can we actually help them?
- Are there technical constraints?

### Overall Qualification Score

**Formula:**
```
Total = (Problem × 0.3) + (Authority × 0.2) + (Budget × 0.2) + (Urgency × 0.15) + (Fit × 0.15)
```

**Interpretation:**
- >= 0.8: QUALIFIED (high confidence, proceed to demo)
- 0.5-0.8: MAYBE (medium confidence, need decision-maker or more info)
- < 0.5: DISQUALIFIED (poor fit, add to nurture list)

## Post-Call (AI Auto-Execution)

### Step 1: Send Follow-up

AI generates email:
- Thank prospect for time
- Summarize key points discussed
- Attach one-pager
- Propose next steps (demo or follow-up call)

### Step 2: Update CRM

Log in thread:
- Qualification score by dimension
- Overall score
- Key insights captured
- Objections raised
- Next action determined

### Step 3: Create Next Action

If QUALIFIED (>= 0.8):
```bash
create_action(type="sales:demo", human_required=True)
```

If MAYBE (0.5-0.8):
```bash
create_action(type="sales:qualification", note="follow-up with decision-maker")
```

If DISQUALIFIED (< 0.5):
```bash
skip_remaining_actions()
proceed_to_results("deal_lost", reason="disqualified")
add_to_nurture_list()
```

## Output

**Status:** QUALIFIED | MAYBE | DISQUALIFIED
**Score:** {overall-score}
**Problem Fit:** {score}
**Authority:** {score}
**Budget:** {score}
**Urgency:** {score}
**Solution Fit:** {score}

**Key Insights:**
- {insight-1}
- {insight-2}

**Objections:**
- {objection-1}

**Next Action:** {sales:demo | sales:qualification | none}
