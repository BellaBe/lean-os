# LeanOS Roadmap

Future development phases for the engineering layer.

---

## Current State: Phase 1 Complete

**Version:** 1.2 (Generic Framework Release)

**Engineering skills operational:**
- `engineering-system-architecture` - Requirements → Mathematical specs
- `engineering-backend-prover` - Specs → Verified backend code
- `engineering-frontend-prover` - Specs → Type-safe frontend
- `engineering-infrastructure-prover` - Specs → Deployment configs
- `engineering-proof-composer` - Validate proof chain
- `engineering-standardization-definer` - Define cross-cutting standards
- `engineering-standardization-applier` - Apply standards to services

---

## Phase 2: Inverse Transformations & Effect System

**Focus:** Bidirectional verification and legacy system import

### New Sub-Skills (3)

#### 1.10 effect-system-analyzer (system-architect)
```
Input:  Type signatures from specifications
Output: effects.yaml
```
**Purpose:** Make side effects explicit (IO, Error, State)

**Why:** Prevent hidden IO in "pure" functions. Functions claiming to be pure but performing database calls or HTTP requests break compositional reasoning.

**Example output:**
```yaml
effects:
  sync_merchant:
    - IO: HTTP (Shopify API)
    - Error: NetworkError | ValidationError
    - State: MerchantCache (read/write)
  calculate_commission:
    - Pure: true  # No effects
```

#### 1.11 spec-to-requirements-extractor (system-architect)
```
Input:  specifications/v{X}/
Output: requirements-reconstructed.md
```
**Purpose:** Verify specs satisfy original requirements (inverse direction)

**Why:** Validate roundtrip correctness. If we can't reconstruct requirements from specs, something was lost in translation.

**Verification:**
```
Requirements → Specs → Reconstructed Requirements
         ↓                      ↓
    Compare: Should be equivalent
```

#### 2.5 code-to-spec-analyzer (backend-prover)
```
Input:  Existing Python codebase
Output: specifications-inferred/v{X}/
```
**Purpose:** Import legacy systems into LeanOS

**Why:**
- Analyze existing code for migration
- Competitive analysis of open-source projects
- Onboard brownfield projects

**Use cases:**
- Import existing FastAPI/Django codebase
- Generate specs from competitor's SDK
- Document undocumented legacy systems

```

---

## Phase 3: Behavioral Equivalence & Optimization

**Focus:** Runtime correctness and code optimization

### New Sub-Skills (2)

#### 4.5 contract-test-generator (frontend-prover)
```
Input:  api.openapi.json
Output: Property-based tests
```
**Purpose:** Verify behavioral correctness (not just types)

**Why:** Type correspondence proves structural compatibility. Contract tests prove behavioral compatibility:
- Pagination actually returns next page
- Error codes match documented responses
- Auth tokens expire when specified
- Rate limits enforced correctly

**Output:**
```python
# Generated property-based tests
@given(page=st.integers(min_value=1, max_value=100))
def test_pagination_returns_correct_page(page):
    response = api.list_items(page=page)
    assert response.meta.current_page == page
    assert len(response.items) <= response.meta.per_page
```

#### 1.6 system-optimizer enhancement
```
New capability: Coproduct optimization
Input:  Platform = {Platform-A} + {Platform-B} + {Platform-C}
Output: Unified interface + adapters
```
**Purpose:** Reduce code duplication for sum types

**Why:** When supporting multiple platforms (coproduct/sum type), naive implementation duplicates logic. Optimizer extracts shared implementation.

**Example:**
```
Before: 3 separate implementations (1000 lines each = 3000 lines)
After:  1 shared implementation + 3 thin adapters (1000 + 3×100 = 1300 lines)
Result: 57% code reduction
```

**Optimization patterns:**
- Extract common interface
- Generate adapter layer
- Prove behavioral equivalence

```

---

## Complete Build Pipeline (All Phases)

```bash
# Phase 1 (Current - Complete)
01-parse-requirements.sh
02-generate-adt-specs.sh
03-prove-type-correctness.sh
04-generate-architecture.sh
05-validate-composition.sh
06-generate-api-spec.sh
07-generate-backend-maps.sh
08-validate-backend-maps.sh
09-generate-backend-code.sh
10-generate-frontend-types.sh
11-prove-type-correspondence.sh
12-generate-infrastructure.sh
13-prove-topology.sh
14-compose-system-proof.sh

# Phase 2 (Planned)
15-verify-effect-system.sh
16-validate-requirements-equivalence.sh
17-analyze-existing-code.sh             # Optional
18-verify-inferred-specs.sh             # Optional

# Phase 3 (Planned)
19-generate-contract-tests.sh
20-run-contract-tests.sh
21-verify-coproduct-optimization.sh
22-final-verification.sh
```

---

## Phase 4: Business Operations Layers (6 New Layers, 29 Sub-skills)

**Focus:** Complete business automation beyond engineering

| Layer | Orchestrator | Sub-skills | Priority |
|-------|--------------|------------|----------|
| Financial Modeling | `financial-modeling` | 6 | ✅ CRITICAL |
| Legal | `legal-layer` | 5 | ✅ CRITICAL |
| Compliance | `compliance-layer` | 5 | ✅ CRITICAL |
| Fundraising | `fundraising-layer` | 5 | ⚠️ VENTURE only |
| Partnerships | `partnership-layer` | 5 | ⚠️ Post-PMF |
| Customer Success | `customer-success-layer` | 5 | ⚠️ After 10 customers |

---

### Financial Modeling (6 sub-skills) - ✅ CRITICAL

**Orchestrator:** `financial-modeling`

**Purpose:** Generate financial projections, scenario analysis, and cash flow forecasts based on Canvas assumptions and actual performance data.

**Mode-aware:** VENTURE (fundraising scenarios, burn/runway) vs BOOTSTRAP (profitability, cash flow)

**Input:**
- Canvas: `11-pricing.md`, `12-costs.md`, `13-metrics.md`, `00-business-model-mode.md`
- Actual performance: Sales threads (Stage 6 - closed deals), `business-metrics-tracker` output
- Scenario parameters: Growth rate assumptions, pricing changes, cost changes

**Output:**
- `artifacts/business/financial-models/{scenario}-{date}.md` - Full projection
- `artifacts/business/financial-models/scenarios-comparison-{date}.md` - Side-by-side scenarios
- Updates Canvas `13-metrics.md` with actuals vs projections

**Core capabilities:**
- 12-24 month revenue/cost projections
- Break-even analysis
- Sensitivity analysis (best/worst/likely cases)
- Cash flow forecasting (BOOTSTRAP)
- Burn rate and runway projection (VENTURE)
- Funding scenario modeling (VENTURE)
- Unit economics validation

**Sub-skills:**

#### 4.1.1 revenue-projector
**Purpose:** Project future revenue based on sales pipeline, conversion rates, and growth assumptions.

**Input:**
- Current MRR/ARR (from `business-metrics-tracker`)
- Sales pipeline (from sales threads)
- Conversion rates (historical from threads)
- Growth assumptions (from Canvas or scenario parameters)
- Pricing tiers (from Canvas `11-pricing.md`)

**Output:**
- Monthly revenue projections (12-24 months)
- Revenue by segment breakdown
- New vs expansion vs churn breakdown
- Confidence intervals (best/worst/likely)

**Calculation logic:**
```
New customers: Pipeline × conversion rate + organic growth
Expansion revenue: Existing customers × expansion rate × ARPU increase
Churn: Customer count × churn rate × ARPU
Net revenue = New + Expansion - Churn
```

#### 4.1.2 cost-projector
**Purpose:** Project future costs based on customer growth, headcount plans, and infrastructure scaling.

**Input:**
- Current cost structure (from Canvas `12-costs.md`)
- Customer growth projections (from `revenue-projector`)
- Hiring plans (if any)
- Infrastructure scaling assumptions

**Output:**
- Monthly cost projections (12-24 months)
- Cost breakdown: COGS, fixed, variable
- Cost per customer trends
- Gross margin projections

**Calculation logic:**
```
COGS: Customer count × unit cost (scales with growth)
Fixed costs: Infrastructure, tools, salaries (step function)
Variable costs: Support, payment processing (scales linearly)
```

#### 4.1.3 cash-flow-analyzer
**Purpose:** Project cash flow timing, working capital needs, and liquidity risks.

**Input:**
- Revenue projections (from `revenue-projector`)
- Cost projections (from `cost-projector`)
- Payment terms (from Canvas `11-pricing.md`)
- Current cash balance (from Canvas `13-metrics.md`)

**Output:**
- Monthly cash flow projections
- Cumulative cash balance
- Working capital requirements
- Liquidity risk flags (cash < 3 months runway)

**Calculation logic:**
```
Cash in: Revenue × collection rate (accounts for payment delays)
Cash out: Costs (actual payment timing)
Net cash flow = Cash in - Cash out
Cumulative balance = Starting balance + Net cash flow
```

#### 4.1.4 scenario-modeler
**Purpose:** Generate multiple financial scenarios (best/worst/likely) and compare side-by-side.

**Input:**
- Base case assumptions (from Canvas)
- Scenario parameters:
  - Growth rate ranges: -20% to +50%
  - Conversion rate ranges: ±20%
  - Churn rate ranges: ±30%
  - Pricing changes: ±15%

**Output:**
- 3-5 scenarios with full projections
- Side-by-side comparison table
- Risk analysis (probability of each scenario)
- Decision recommendations

**Scenarios:**
- **Best case:** High growth, low churn, high conversion
- **Likely case:** Expected performance based on historical data
- **Worst case:** Low growth, high churn, low conversion
- **Custom scenarios:** User-defined parameters

#### 4.1.5 break-even-calculator
**Purpose:** Calculate break-even point (customers, revenue, months) and validate business model viability.

**Input:**
- Fixed costs (from `cost-projector`)
- Variable costs per customer (from `cost-projector`)
- Average revenue per customer (from `revenue-projector`)
- Growth rate (from scenario parameters)

**Output:**
- Break-even customer count
- Break-even revenue (MRR/ARR)
- Break-even timeline (months)
- Unit economics validation (LTV > CAC × 3)

**Calculation logic:**
```
Break-even customers = Fixed costs / (ARPU - Variable cost per customer)
Break-even timeline = Break-even customers / Customer acquisition rate
Validate: LTV/CAC ratio, gross margin, payback period
```

#### 4.1.6 fundraising-scenario-modeler (VENTURE mode only)
**Purpose:** Model funding scenarios, dilution, and post-money valuation for fundraising decisions.

**Input:**
- Current valuation (from Canvas or assumptions)
- Funding amount needed (from `cash-flow-analyzer`)
- Expected dilution range (10-25%)
- Use of funds breakdown

**Output:**
- Pre-money and post-money valuation
- Dilution percentage
- Ownership breakdown (founders, investors, ESOP)
- Runway extension (months)
- Milestones achievable with funding

**Calculation logic:**
```
Post-money valuation = Funding amount / Dilution percentage
Pre-money valuation = Post-money - Funding amount
New runway = (Current cash + Funding) / Projected burn rate
```

---

### Legal Layer (5 sub-skills) - ✅ CRITICAL

**Orchestrator:** `legal-layer`

**Purpose:** Handle contracts, terms, regulatory reviews, and IP protection through strategic legal decision-making (NOT operational enforcement).

**Separation from compliance:** Legal = strategic/contractual, Compliance = operational/automated

**Input:**
- Contracts (customer agreements, vendor contracts)
- Legal questions (regulatory interpretation, IP)
- Canvas: `02-market.md` (target market), `05-problem.md` (regulated industries)

**Output:**
- `threads/legal/{contract-name}/` - Contract review threads
- `artifacts/legal/templates/` - Standard agreements (MSA, NDA, ToS, Privacy Policy)
- `artifacts/legal/reviews/{contract-name}-review-{date}.md` - Risk analysis
- Escalation flags in `ops/today.md` for external counsel

**Core capabilities:**
- Contract review and risk analysis
- Standard agreement generation
- Regulatory risk assessment
- IP protection tracking
- External counsel coordination

**Sub-skills:**

#### 4.2.1 contract-reviewer
**Purpose:** Analyze inbound contracts (customer, vendor, partnership) and flag legal risks.

**Input:**
- Contract document (PDF, DOCX)
- Contract type (customer MSA, vendor agreement, partnership)
- Deal value (from sales thread if applicable)

**Output:**
- Risk analysis report
- Redline suggestions
- Escalation flag (if high-risk clauses detected)
- Comparison to standard template

**Risk categories flagged:**
- **High risk:** Unlimited liability, broad indemnification, IP assignment, non-standard termination
- **Medium risk:** Auto-renewal, exclusivity, pricing caps, SLA penalties
- **Low risk:** Standard terms, minor deviations

**Escalation triggers:**
- Deal value >$50K
- Unlimited liability clauses
- IP ownership disputes
- Regulatory compliance concerns
- Non-standard jurisdiction

#### 4.2.2 agreement-generator
**Purpose:** Generate standard legal agreements from templates based on deal parameters.

**Input:**
- Agreement type (MSA, NDA, ToS, Privacy Policy, DPA)
- Deal parameters: Customer name, services, pricing, term length
- Jurisdiction (US, EU, GCC)

**Output:**
- Generated agreement (DOCX format)
- Fillable fields highlighted
- Usage instructions

**Templates maintained:**
- Master Services Agreement (MSA)
- Non-Disclosure Agreement (NDA)
- Terms of Service (ToS)
- Privacy Policy
- Data Processing Agreement (DPA - GDPR)
- API Terms of Use

#### 4.2.3 regulatory-advisor
**Purpose:** Flag regulatory risks and determine when external legal counsel is required.

**Input:**
- Business activity description
- Target market (from Canvas `02-market.md`)
- Data handling practices
- Industry (finance, healthcare, e-commerce)

**Output:**
- Regulatory requirements checklist
- Risk level assessment
- External counsel recommendation (yes/no)
- Next steps

**Regulated areas monitored:**
- **GDPR:** EU data processing
- **GCC financial:** Central bank regulations
- **Consumer protection:** E-commerce, returns, refunds
- **Export controls:** Software, AI/ML models
- **Securities:** If fundraising (VENTURE mode)

**Escalation triggers:**
- Regulated industry operations (finance, healthcare)
- Cross-border data transfers
- Large fines possible (>$100K)
- Ambiguous regulatory interpretation

#### 4.2.4 ip-protector
**Purpose:** Track and protect intellectual property (trademarks, copyrights, trade secrets).

**Input:**
- Product names, brand names
- Marketing content (for copyright)
- Proprietary algorithms, methods (trade secrets)

**Output:**
- IP inventory (trademarks, copyrights, trade secrets)
- Registration status tracking
- Infringement monitoring alerts
- Protection recommendations

**IP types tracked:**
- **Trademarks:** Product names, logos
- **Copyrights:** Marketing content, documentation, software
- **Trade secrets:** Algorithms, customer lists, business methods
- **Domain names:** Ownership, renewals

#### 4.2.5 litigation-coordinator
**Purpose:** Coordinate legal disputes, claims, and litigation (if needed).

**Input:**
- Dispute description (customer complaint, IP claim, contract dispute)
- Parties involved
- Financial exposure

**Output:**
- Case summary
- Recommended response strategy
- External counsel engagement
- Timeline and cost estimate

**Triggers:**
- Customer threatens legal action
- IP infringement claim received
- Contract dispute escalates
- Regulatory investigation initiated

---

### Compliance Layer (5 sub-skills) - ✅ CRITICAL

**Orchestrator:** `compliance-layer`

**Purpose:** Operational enforcement of legal and regulatory requirements through automated monitoring, reporting, and workflows.

**Separation from legal:** Compliance = operational enforcement (automated), Legal = strategic/contractual (human judgment)

**Input:**
- Legal policies (from `legal-layer`: ToS, Privacy Policy, DPA)
- Data handling practices (from engineering systems)
- User requests (GDPR data subject requests)

**Output:**
- `threads/compliance/{incident-type}-{date}/` - Incident threads
- `artifacts/compliance/audit-reports/` - Automated audit trails
- `artifacts/compliance/violations/` - Detected violations
- Escalation flags in `ops/today.md` for high-risk violations

**Core capabilities:**
- GDPR/data privacy enforcement
- Audit trail generation
- Violation detection and alerting
- Security incident response
- Data subject request automation

**Sub-skills:**

#### 4.3.1 gdpr-enforcer
**Purpose:** Automate GDPR data subject requests (access, deletion, portability, rectification).

**Input:**
- Data subject request type (access, deletion, portability, rectification)
- User identifier (email, customer ID)
- Request verification (authenticated user)

**Output:**
- Data inventory report (access request)
- Deletion confirmation (deletion request)
- Data export file (portability request)
- Audit log entry
- Response timeline tracking (30-day deadline)

**Workflows:**
- **Access request:** Scan all databases, compile user data, generate report
- **Deletion request:** Identify data across systems, execute deletion, confirm completion
- **Portability request:** Export user data in machine-readable format (JSON, CSV)
- **Rectification request:** Update incorrect data, log changes

**Systems scanned:**
- Customer database (PostgreSQL)
- Analytics data (if separate)
- Backups (flag for manual deletion)
- Third-party services (generate API calls)

#### 4.3.2 audit-generator
**Purpose:** Generate automated audit reports for compliance, security, and regulatory reviews.

**Input:**
- Audit period (monthly, quarterly, annual)
- Audit scope (GDPR, security, data handling)
- Regulatory framework (GDPR, GCC, SOC2)

**Output:**
- Audit report (PDF/DOCX)
- Findings summary (compliant, violations, recommendations)
- Evidence attachments (logs, screenshots, configs)
- Remediation plan (if violations found)

**Audit types:**
- **GDPR compliance:** Data processing, consent management, data subject requests
- **Security:** Access controls, encryption, incident response
- **Data handling:** Retention policies, deletion workflows, backups
- **API usage:** Rate limiting, authentication, authorization

**Report structure:**
1. Executive summary
2. Scope and methodology
3. Findings (compliant, non-compliant)
4. Evidence (logs, configs, screenshots)
5. Recommendations
6. Remediation timeline

#### 4.3.3 violation-detector
**Purpose:** Monitor data handling practices and flag compliance violations in real-time.

**Input:**
- Data access logs (from engineering systems)
- Data retention policies (from `legal-layer`)
- User consent records (from customer database)

**Output:**
- Violation alerts (real-time)
- Violation summary (daily digest in `ops/today.md`)
- Risk level (low, medium, high)
- Remediation recommendations

**Violations detected:**
- **Data retention:** Data kept beyond retention period
- **Access control:** Unauthorized data access attempts
- **Consent:** Marketing emails sent without consent
- **Encryption:** Unencrypted data transmission
- **Logging:** Missing audit logs for sensitive operations

**Alert thresholds:**
- **High:** Unauthorized data access, unencrypted sensitive data
- **Medium:** Retention policy violations, missing consent
- **Low:** Minor logging gaps, non-critical access attempts

#### 4.3.4 incident-responder
**Purpose:** Automate security incident detection, triage, and response workflows.

**Input:**
- Incident trigger (security alert, breach notification, vulnerability)
- Incident severity (low, medium, high, critical)
- Affected systems/data

**Output:**
- Incident thread (6-stage causal flow)
- Incident response playbook execution
- Notification to affected parties (if required)
- Post-incident report
- Escalation flag (if critical)

**Incident types:**
- **Data breach:** Unauthorized data access or exfiltration
- **System compromise:** Malware, ransomware, intrusion
- **Vulnerability:** Critical security flaw discovered
- **DDoS:** Service disruption attack
- **Insider threat:** Employee data misuse

**Response workflow:**
1. **Detection:** Alert triggered (automated monitoring)
2. **Triage:** Assess severity, scope, impact
3. **Containment:** Isolate affected systems, revoke access
4. **Investigation:** Analyze logs, identify root cause
5. **Remediation:** Patch vulnerability, restore systems
6. **Notification:** Inform affected parties (if legally required)
7. **Post-incident:** Document learning, update policies

**Escalation triggers:**
- Critical severity (data breach, system compromise)
- Regulatory notification required (GDPR 72-hour rule)
- Financial impact >$10K
- Customer data exposed

#### 4.3.5 data-retention-enforcer
**Purpose:** Automate data retention and deletion workflows based on legal policies.

**Input:**
- Data retention policies (from `legal-layer`)
- Data creation timestamps (from databases)
- Data type (customer data, analytics, logs)

**Output:**
- Deletion queue (data eligible for deletion)
- Deletion confirmation (after execution)
- Audit log (retention compliance)
- Exception handling (legal holds)

**Retention policies:**
- **Customer data:** Retained while account active + 30 days after deletion request
- **Analytics data:** 24 months (GDPR recommended)
- **Audit logs:** 7 years (regulatory requirement)
- **Marketing data:** Until consent withdrawn + 30 days

**Deletion workflow:**
1. Scan databases for data exceeding retention period
2. Generate deletion queue
3. Execute deletion (automated or flagged for approval)
4. Verify deletion completion
5. Log deletion in audit trail

---

### Fundraising Layer (5 sub-skills) - ⚠️ VENTURE only

**Orchestrator:** `fundraising-layer`

**Purpose:** Manage investor pipeline, generate pitch materials, coordinate due diligence, and track fundraising progress.

**Mode restriction:** VENTURE only (disabled in BOOTSTRAP mode)

**Input:**
- Canvas: All sections (pitch deck source)
- Business metrics (from `business-metrics-tracker`)
- Financial projections (from `financial-modeling`)

**Output:**
- `threads/fundraising/investors/{investor-name}/` - Investor threads
- `artifacts/fundraising/pitch-deck-{date}.pptx` - Pitch deck
- `artifacts/fundraising/data-room/` - Due diligence materials
- `artifacts/fundraising/investor-updates/` - Monthly updates

**Core capabilities:**
- Investor pipeline management
- Pitch deck generation (from Canvas)
- Due diligence coordination
- Investor update automation
- Term sheet analysis

**Sub-skills:**

#### 4.4.1 investor-pipeline-manager
**Purpose:** Track investor relationships, outreach, and meeting progression.

**Input:**
- Investor name, firm, focus areas
- Outreach status (cold, warm, intro)
- Meeting history (initial, diligence, partner meeting)

**Output:**
- Investor pipeline dashboard
- Next action recommendations
- Meeting prep materials
- Follow-up reminders

**Pipeline stages:**
1. **Identified:** Target investor researched
2. **Outreach:** Email/intro sent
3. **Initial meeting:** First call scheduled/completed
4. **Diligence:** Data room access granted
5. **Partner meeting:** Pitch to full partnership
6. **Term sheet:** Terms under negotiation
7. **Closed:** Investment completed

**Metrics tracked:**
- Investors contacted
- Meetings booked
- Conversion rates (stage to stage)
- Time in each stage
- Drop-off reasons

#### 4.4.2 pitch-deck-generator
**Purpose:** Generate investor pitch deck from Canvas content and business metrics.

**Input:**
- Canvas: All sections (problem, solution, market, traction)
- Business metrics (from `business-metrics-tracker`)
- Financial projections (from `financial-modeling`)
- Team information (from Canvas `08-team.md`)

**Output:**
- Pitch deck (PPTX format)
- Slide-by-slide narrative
- Speaker notes
- Supporting appendix

**Slide structure (standard VC deck):**
1. **Cover:** Company name, tagline, date
2. **Problem:** Customer pain (Canvas `05-problem.md`)
3. **Solution:** Product overview (Canvas `09-solution.md`)
4. **Market:** TAM/SAM/SOM (Canvas `02-market.md`)
5. **Product:** Demo/screenshots (Canvas `09-solution.md`)
6. **Traction:** Metrics, growth (`business-metrics-tracker`)
7. **Business model:** Pricing, revenue (Canvas `11-pricing.md`)
8. **Competition:** Differentiation (Canvas `03-competition.md`)
9. **Go-to-market:** Sales/marketing strategy (Canvas `06-channels.md`)
10. **Team:** Founders, advisors (Canvas `08-team.md`)
11. **Financials:** Projections (`financial-modeling`)
12. **Ask:** Funding amount, use of funds, milestones

#### 4.4.3 due-diligence-coordinator
**Purpose:** Coordinate investor due diligence by organizing data room and responding to requests.

**Input:**
- Investor due diligence checklist
- Company documents (legal, financial, technical)
- Data room access requests

**Output:**
- Virtual data room structure
- Document upload tracking
- Request response tracking
- Missing document alerts

**Data room sections:**
- **Company:** Articles of incorporation, cap table, board minutes
- **Legal:** Contracts (customer, vendor), IP assignments, litigation history
- **Financial:** Financial statements, tax returns, banking information
- **Product:** Technical architecture, roadmap, security audits
- **Customers:** Customer list (anonymized), case studies, NPS scores
- **Team:** Employee agreements, org chart, compensation structure

#### 4.4.4 investor-update-generator
**Purpose:** Generate monthly investor updates with key metrics, progress, and asks.

**Input:**
- Business metrics (from `business-metrics-tracker`)
- Recent achievements (from threads)
- Upcoming milestones (from Canvas `15-milestones.md`)

**Output:**
- Investor update email (markdown)
- Metrics dashboard (key numbers)
- Progress narrative (wins, challenges, asks)

**Update structure:**
- **Headline:** One-sentence summary of month
- **Metrics:** MRR/ARR, growth rate, customer count, burn rate
- **Key wins:** Product launches, customer wins, partnerships
- **Challenges:** Problems faced, how addressing
- **Upcoming milestones:** Next 30 days priorities
- **Asks:** Specific help needed (intros, feedback, hiring)

#### 4.4.5 term-sheet-analyzer
**Purpose:** Analyze investor term sheets and flag unfavorable terms.

**Input:**
- Term sheet document (PDF, DOCX)
- Current cap table
- Fundraising goals (valuation, dilution targets)

**Output:**
- Term sheet analysis report
- Favorable/unfavorable terms highlighted
- Negotiation recommendations
- Dilution calculation
- Post-funding cap table projection

**Terms analyzed:**
- **Valuation:** Pre-money, post-money
- **Dilution:** Founder ownership impact
- **Liquidation preference:** 1x, participating vs non-participating
- **Anti-dilution:** Full ratchet vs weighted average
- **Board composition:** Investor seats, founder control
- **Protective provisions:** Veto rights, major decisions
- **Vesting:** Founder re-vesting requirements

**Red flags:**
- >25% dilution in single round
- Participating liquidation preference
- Full ratchet anti-dilution
- Investor board control
- Excessive protective provisions

---

### Partnership Layer (5 sub-skills) - ⚠️ Post-PMF

**Orchestrator:** `partnership-layer`

**Purpose:** Manage strategic partnerships, integration opportunities, and channel relationships (separate from direct sales).

**Difference from sales:** Sales = direct customer revenue, Partnerships = ecosystem plays, integrations, co-marketing

**Input:**
- Partnership opportunity (integration, co-marketing, channel)
- Canvas: `03-competition.md` (ecosystem players), `06-channels.md` (distribution)

**Output:**
- `threads/partnerships/{partner-name}/` - Partnership threads
- `artifacts/partnerships/agreements/` - Partnership agreements
- `artifacts/partnerships/integrations/` - Integration specs

**Core capabilities:**
- Partnership opportunity identification
- Integration roadmap planning
- Co-marketing coordination
- Channel partner management
- Ecosystem relationship tracking

**Sub-skills:**

#### 4.5.1 partnership-opportunity-detector
**Purpose:** Identify potential strategic partnerships based on Canvas and market analysis.

**Input:**
- Canvas: `02-market.md` (ecosystem), `03-competition.md` (complementary products)
- Customer feedback (from sales threads)
- Integration requests (from support)

**Output:**
- Partnership opportunity list
- Priority ranking (impact × feasibility)
- Outreach strategy
- Value proposition for partner

**Partnership types:**
- **Integration partners:** Complementary products (e.g., Shopify for e-commerce)
- **Channel partners:** Resellers, agencies, consultants
- **Co-marketing partners:** Shared audience, non-competing
- **Technology partners:** Infrastructure, platform providers
- **Strategic partners:** Joint ventures, large enterprises

**Opportunity signals:**
- Customer requests integration (N=5+)
- Ecosystem player mentions product
- Competitor has similar partnership
- Partner announces relevant initiative

#### 4.5.2 integration-roadmap-planner
**Purpose:** Plan technical integrations with partner platforms and prioritize based on customer demand.

**Input:**
- Integration requests (from customers, sales threads)
- Partner API documentation
- Engineering capacity (from Canvas `08-team.md`)

**Output:**
- Integration roadmap (prioritized list)
- Technical requirements per integration
- Effort estimates (hours/weeks)
- Customer impact projection (revenue, retention)

**Integration types:**
- **API integration:** Bi-directional data sync
- **Webhook integration:** Event-driven updates
- **Embed integration:** Widget in partner platform
- **OAuth integration:** User authentication via partner
- **Marketplace listing:** Published in partner's app store

**Prioritization criteria:**
- Customer demand (number of requests)
- Revenue impact (deals blocked without integration)
- Effort required (engineering hours)
- Strategic value (ecosystem positioning)

#### 4.5.3 co-marketing-coordinator
**Purpose:** Coordinate co-marketing campaigns with partners (webinars, content, events).

**Input:**
- Partner name, audience size, focus areas
- Co-marketing opportunity (webinar, case study, event)
- Campaign goals (leads, brand awareness, thought leadership)

**Output:**
- Co-marketing campaign plan
- Content collaboration workflow
- Lead attribution tracking
- Performance metrics

**Co-marketing types:**
- **Webinars:** Joint presentation to combined audiences
- **Case studies:** Customer using both products
- **Content collaboration:** Co-authored blog posts, guides
- **Events:** Joint booth, speaking slots
- **Cross-promotion:** Newsletter swaps, social media mentions

**Success metrics:**
- Leads generated (attributed to partner)
- Pipeline influenced
- Brand reach (impressions, attendees)
- Content engagement (downloads, views)

#### 4.5.4 channel-partner-manager
**Purpose:** Manage reseller, agency, and consultant relationships for indirect sales.

**Input:**
- Channel partner type (reseller, agency, consultant)
- Partner onboarding status
- Deal registration (opportunities from partner)

**Output:**
- Partner portal access
- Partner training materials
- Deal registration tracking
- Commission calculation
- Partner performance dashboard

**Channel partner types:**
- **Resellers:** Sell product directly (white-label)
- **Agencies:** Recommend product to clients
- **Consultants:** Implement product (system integrators)
- **Affiliates:** Referral commissions

**Partner lifecycle:**
1. **Recruitment:** Identify, qualify, pitch partnership
2. **Onboarding:** Training, portal access, materials
3. **Activation:** First deal registered
4. **Growth:** Regular deal flow, expansion
5. **Optimization:** Performance review, incentive adjustments

#### 4.5.5 ecosystem-relationship-tracker
**Purpose:** Track relationships with ecosystem players (platforms, communities, industry groups).

**Input:**
- Ecosystem player (platforms, banking platforms, industry associations)
- Relationship type (integration, sponsorship, membership)
- Activity log (meetings, events, communications)

**Output:**
- Ecosystem map (visual representation)
- Relationship health score
- Engagement recommendations
- Strategic positioning insights

**Ecosystem players tracked:**
- **Platforms:** E-commerce, banking, industry-specific
- **Communities:** Reddit, Discord, Slack communities in target market
- **Industry groups:** Trade associations, professional forums
- **Events:** Conferences, trade shows, meetups
- **Media:** Industry publications, podcasts, blogs

**Relationship health indicators:**
- Last interaction date
- Frequency of engagement
- Reciprocity (do they promote us?)
- Strategic value (influence, reach)

---

### Customer Success Layer (5 sub-skills) - ⚠️ After 10 customers

**Orchestrator:** `customer-success-layer`

**Purpose:** Manage post-sales customer lifecycle (onboarding, support, retention, expansion) to maximize LTV and minimize churn.

**Separation from sales:** Sales = pre-close (demos, pilots, contracts), Customer Success = post-close (adoption, value realization, renewal)

**Input:**
- New customer data (from sales threads - Stage 6)
- Product usage data (from engineering systems)
- Support tickets (from support system)

**Output:**
- `threads/customer-success/{customer-name}/` - Customer health threads
- `artifacts/customer-success/playbooks/` - Onboarding, expansion playbooks
- Escalation flags in `ops/today.md` (churn risk, expansion opportunity)

**Core capabilities:**
- Onboarding automation
- Usage monitoring and health scoring
- Churn prediction and intervention
- Expansion opportunity detection
- Support ticket triage

**Sub-skills:**

#### 4.6.1 onboarding-automator
**Purpose:** Automate customer onboarding through email sequences, in-app guidance, and milestone tracking.

**Input:**
- New customer data (from sales thread)
- Customer segment (from ICP)
- Product tier (from pricing plan)

**Output:**
- Onboarding email sequence (triggered automatically)
- In-app onboarding checklist
- Milestone completion tracking
- Escalation flags (if milestones missed)

**Onboarding milestones:**
- **Day 0:** Welcome email, credentials sent
- **Day 1:** First login, profile setup
- **Day 3:** First core action (e.g., first product recommendation)
- **Day 7:** Integration setup (e.g., platform connection)
- **Day 14:** Value realization (e.g., first conversion attributed to product)
- **Day 30:** Onboarding complete, adoption confirmed

**Email sequence:**
1. Welcome email (Day 0)
2. Getting started guide (Day 1)
3. Feature highlights (Day 3, 5, 7)
4. Integration tutorial (Day 7)
5. Success story (Day 14)
6. Check-in call offer (Day 21)
7. Onboarding complete (Day 30)

**Escalation triggers:**
- No login within 3 days
- No core action within 7 days
- Integration incomplete at Day 14
- No value realization by Day 30

#### 4.6.2 health-score-calculator
**Purpose:** Calculate customer health score based on usage, engagement, and satisfaction to predict churn risk.

**Input:**
- Product usage data (logins, features used, frequency)
- Support ticket history (count, severity, resolution time)
- NPS/satisfaction surveys (if available)
- Payment history (on-time, late, failed)

**Output:**
- Customer health score (0-100)
- Health trend (improving, stable, declining)
- Churn risk level (low, medium, high)
- Recommended actions

**Health score components:**
- **Usage (40%):** Login frequency, feature adoption, active users
- **Engagement (30%):** Support responsiveness, feedback participation, community activity
- **Satisfaction (20%):** NPS score, survey responses, qualitative feedback
- **Financial (10%):** Payment timeliness, plan tier, expansion history

**Health score ranges:**
- **90-100 (Green):** Healthy, expansion candidate
- **70-89 (Yellow):** Stable, monitor closely
- **50-69 (Orange):** At-risk, intervention needed
- **0-49 (Red):** High churn risk, urgent action

**Churn risk indicators:**
- Usage declined >30% in last 30 days
- No logins in last 14 days
- Multiple unresolved support tickets
- NPS score <5
- Payment failure

#### 4.6.3 churn-predictor
**Purpose:** Predict churn risk using health score, usage patterns, and early warning signals.

**Input:**
- Health score (from `health-score-calculator`)
- Usage trend (from product analytics)
- Support ticket sentiment (from ticket analysis)
- Contract renewal date

**Output:**
- Churn probability (0-100%)
- Early warning signals detected
- Intervention recommendations
- Customer outreach scripts

**Early warning signals:**
- **Usage decline:** >30% drop in last 30 days
- **Feature abandonment:** Key features unused for 14+ days
- **Support frustration:** Multiple tickets, negative sentiment
- **Executive disengagement:** Decision-maker not logging in
- **Contract non-renewal:** Renewal date approaching, no engagement

**Intervention playbook:**
- **Low churn risk (<30%):** Automated email check-in
- **Medium churn risk (30-60%):** CSM outreach call, product review
- **High churn risk (>60%):** Executive escalation, retention offer

#### 4.6.4 expansion-opportunity-detector
**Purpose:** Identify expansion opportunities (upsell, cross-sell, additional seats) based on usage and account signals.

**Input:**
- Product usage data (feature adoption, user count)
- Customer health score (from `health-score-calculator`)
- Product tier (current plan)
- Customer segment (from ICP)

**Output:**
- Expansion opportunity list
- Opportunity type (upsell, cross-sell, seats)
- Revenue potential
- Recommended sales motion

**Expansion signals:**
- **Upsell:** Usage approaching plan limits (90%+ of quota)
- **Cross-sell:** Feature requests for adjacent products
- **Seats:** Multiple users sharing single account
- **Premium features:** Repeated use of trial features
- **Higher tier:** Power user behavior exceeding current plan

**Expansion types:**
- **Tier upgrade:** Starter → Pro → Enterprise
- **Seat expansion:** Add more users to account
- **Feature add-ons:** Premium features (API access, white-label)
- **Usage overages:** Exceed plan limits, offer upgrade
- **Cross-sell:** Additional products in portfolio

**Sales motion:**
- **Low-touch (self-serve):** In-app upgrade prompts, email nudges
- **Medium-touch (CSM-led):** CSM proposes upgrade during check-in
- **High-touch (sales-led):** Hand off to sales for enterprise deal

#### 4.6.5 support-triager
**Purpose:** Triage support tickets, route to appropriate team, and escalate urgent issues.

**Input:**
- Support ticket (email, in-app, chat)
- Ticket content (description, attachments, customer info)
- Customer health score (from `health-score-calculator`)

**Output:**
- Ticket priority (P0, P1, P2, P3)
- Routing recommendation (support, engineering, CSM, sales)
- Suggested response (for common issues)
- Escalation flag (if urgent)

**Ticket prioritization:**
- **P0 (Critical):** System down, data loss, security breach
- **P1 (High):** Core feature broken, churn-risk customer
- **P2 (Medium):** Non-core feature issue, moderate impact
- **P3 (Low):** Feature request, general question, minor bug

**Routing logic:**
- **Support team:** How-to questions, known issues, account changes
- **Engineering team:** Bugs, performance issues, technical errors
- **CSM team:** High-value customers, expansion discussions, churn risk
- **Sales team:** Pricing questions, contract changes, expansion deals

**Auto-response triggers:**
- Common questions (FAQ match)
- Known issues (with workaround)
- Service status (planned maintenance)

---

## Summary

| Phase | Focus | New Skills | Status |
|-------|-------|------------|--------|
| 1 | Core verification pipeline | 7 skills | Complete |
| 2 | Inverse transformations & effects | 3 sub-skills | Planned |
| 3 | Behavioral equivalence & optimization | 2 sub-skills | Planned |
| 4 | Business operations layers | 6 layers, 29 sub-skills | Planned |

**Total engineering sub-skills:** 5 (Phases 2-3)
**Total business sub-skills:** 29 (Phase 4)
**Total build steps:** 22 (14 current + 8 new)

---

## Contributing

Phase 2-4 skills follow the same patterns as Phase 1:
- Each skill has `SKILL.md` with clear input/output
- Mathematical foundations documented (engineering)
- Business logic documented (operations)
- Verification scripts in build pipeline (engineering)
- Integration with appropriate orchestrators

See [CONTRIBUTING.md](CONTRIBUTING.md) for contribution guidelines.
