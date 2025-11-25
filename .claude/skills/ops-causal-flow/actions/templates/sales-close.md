# Sales Close Action

**Type:** sales:close
**Human Required:** Yes
**Duration:** 7-14 days

## Contract Preparation (AI-Generated)

### Step 1: Generate Contract

Load contract template:
```bash
artifacts/sales/current/contract-template.md
```

Customize for lead:
- Company name, legal entity, address
- Contact info (billing, technical, executive)
- Pricing tier (from Canvas pricing section)
  - Base price
  - Add-ons (e.g., {premium feature}, {advanced tier})
- Contract term (1 year, 2 years)
- Payment terms (annual, quarterly, monthly)
- SLA commitments (uptime, support response time)
- Implementation timeline

Output: `threads/sales/{thread-id}/contract-custom.md`

### Step 2: Load Pricing

From Canvas:
```bash
strategy/canvas/11-pricing.md
```

Calculate total ARR:
- Base tier: ${amount}
- Add-ons: ${amount}
- Total: ${ARR}

### Step 3: Schedule Negotiation Call

AI sends calendar invite:
- Duration: 30-60 min
- Attendees: Lead decision-makers, Founder
- Agenda: Contract terms, pricing, timeline
- Attach: Draft contract

## Contract Negotiation (Human Execution)

**Duration:** 30-60 min + follow-up rounds
**Attendees:** Lead decision-makers (economic buyer, legal), Founder

### Negotiation Points

**Pricing:**
- ARR amount
- Payment terms (annual vs quarterly)
- Multi-year discount

**Terms:**
- Contract length (1-2 years standard)
- Auto-renewal clause
- Termination terms

**SLA:**
- Uptime guarantee (99.9% standard)
- Support response time
- Escalation process

**Implementation:**
- Timeline (30-60 days standard)
- Onboarding support included
- Training sessions

### Negotiation Rounds

Track in CRM:
- Round 1: Initial proposal
- Round 2: Counter-offer
- Round 3: Final terms

Typical rounds: 2-3 before agreement

## Legal Review (Human Coordination)

### Internal Legal (When Available)
- Review contract terms
- Flag non-standard clauses
- Approve or request changes

### Lead Legal Review
- They review contract
- Redlines/comments received
- Negotiate redlines

**Note:** Legal review workflow to be defined later. For now, Founder handles directly.

## Contract Signing (Human + AI Support)

### Step 1: Final Contract

Once terms agreed:
- Incorporate all redlines
- Generate final contract PDF
- Send for signature (DocuSign or email)

### Step 2: Track Signing

AI monitors:
- Contract sent: {date}
- Awaiting signature from: {stakeholder}
- Signed: {date}

Send reminders if not signed within 3 days.

### Step 3: Post-Signature

Once signed:
- Welcome email with onboarding info
- Schedule implementation kickoff
- Hand off to customer success (future)
- Update CRM: Deal WON

## Output

**Status:** WON | LOST
**ARR:** ${amount}
**Contract Term:** {years}
**Start Date:** {date}
**Negotiation Rounds:** {count}
**Days to Close:** {days from demo to signature}

**If LOST:**
**Reason:** {pricing | terms | timing | competition | other}
**Next Action:** {add to nurture | none}
