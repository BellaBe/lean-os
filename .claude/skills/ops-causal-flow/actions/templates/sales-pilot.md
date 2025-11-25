# Sales Pilot Action

**Type:** sales:pilot
**Human Required:** Yes
**Duration:** 14-30 days (pilot) + 7 days (setup/negotiation)

## Pilot Preparation (AI-Generated)

### Step 1: Generate Pilot Agreement

Load pilot template:
```bash
artifacts/sales/current/pilot-agreement.md
```

Customize for lead:
- Company name, contact info
- Pilot duration (typically 30 days)
- Use cases (3-5 specific scenarios)
- Success criteria (from ICP qualification questions)
  - Technical: Latency, accuracy, uptime targets
  - Business: ROI, user satisfaction metrics
- Support terms
- Pricing: Free pilot or discounted

Output: `threads/sales/{thread-id}/pilot-agreement-custom.md`

### Step 2: Define Success Criteria

Based on ICP and qualification insights:

**Technical Metrics:**
- Performance targets (response time, accuracy)
- Scalability requirements
- Integration success

**Business Metrics:**
- Problem solved (quantified improvement)
- User feedback (NPS or satisfaction score)
- ROI demonstration

### Step 3: Schedule Pilot Kickoff

AI sends calendar invite:
- Duration: 30 min
- Attendees: Lead technical team, Founder
- Agenda: Pilot overview, success criteria, timeline
- Attach: Pilot agreement

## Pilot Negotiation (Human Execution)

**Duration:** 30 min call + follow-up
**Attendees:** Lead stakeholders, Founder

### Negotiation Points

- Pilot duration: 14-30 days (standard: 30)
- Use cases: 3-5 scenarios
- Success criteria: Align on metrics
- Support level: Daily check-ins or async
- Cost: Free (pre-revenue) or discounted (post-revenue)

### Sign Pilot Agreement

Once terms agreed:
- Send final pilot agreement
- Get signature (DocuSign or email confirmation)
- Schedule kickoff

## Pilot Execution (Human + AI Support)

### Week 1: Setup & Integration
- Technical integration
- Training/onboarding
- Use case setup

### Week 2-3: Active Usage
- Monitor metrics daily
- Address issues/bugs
- Collect user feedback

### Week 4: Results & Analysis
- Compile metrics
- Calculate ROI
- Prepare pilot results report

### AI Support During Pilot

**Daily:**
- Monitor usage metrics
- Alert on issues (downtime, errors)
- Track progress toward success criteria

**Weekly:**
- Send progress report to lead
- Schedule check-in calls if needed
- Update CRM with pilot status

## Pilot Results (AI-Generated)

### Step 1: Compile Results

Generate pilot results report:
- Technical metrics vs targets
- Business metrics vs targets
- User feedback summary
- Issues encountered + resolutions
- ROI calculation

Output: `threads/sales/{thread-id}/pilot-results.md`

### Step 2: Send Results

AI generates email:
- Attach pilot results report
- Highlight successes (metrics exceeded)
- Address any concerns
- Propose: Move to contract

### Step 3: Create Next Action

If pilot successful:
```bash
create_action(type="sales:close", human_required=True)
```

If pilot failed:
```bash
skip_remaining_actions()
proceed_to_results("deal_lost", reason="pilot_failed")
log_failure_reasons()
```

## Output

**Status:** SUCCESS | FAILED
**Technical Metrics:** {targets vs actuals}
**Business Metrics:** {targets vs actuals}
**User Feedback:** {score}
**Issues:** {count resolved/unresolved}
**Next Action:** {sales:close | none}
