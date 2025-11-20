# Validation Guide: Launch Readiness Criteria

Before activating sales and marketing operations, validate that your foundation is solid.

## Launch Readiness Checklist

### ✅ Canvas Completeness

**All 15 sections populated with evidence:**

- [ ] 01-context.md (KBOS framework)
- [ ] 02-constraints.md (Budget, time, resources)
- [ ] 03-opportunity.md (TAM/SAM/SOM)
- [ ] 04-segments.md (Customer segments)
- [ ] 05-problem.md (Top 3 problems)
- [ ] 06-competitive.md (Competitive landscape)
- [ ] 07-uvp.md (Unique Value Proposition)
- [ ] 08-advantage.md (Unfair advantages)
- [ ] 09-solution.md (MVP feature set)
- [ ] 10-assumptions.md (Hypotheses tracked)
- [ ] 11-pricing.md (Revenue model)
- [ ] 12-costs.md (Cost structure)
- [ ] 13-metrics.md (Key metrics)
- [ ] 14-growth.md (Growth channels)
- [ ] 15-gtm.md (Go-to-market strategy)

**Quality criteria:**
- No "TBD" or placeholder content
- Every claim backed by evidence (interviews, research, experiments)
- Numbers included (market size, pricing, costs, metrics)

---

### ✅ Assumption Validation

**Critical assumptions validated (confidence ≥75%):**

Identify 5-10 critical assumptions from `strategy/canvas/10-assumptions.md` that must be true for the business to work.

**Example critical assumptions:**
- Customers will pay $X/month
- Problem is severe enough to drive purchasing decision
- Solution addresses root cause (not just symptom)
- Target segment is reachable through Channel Y
- Sales cycle is ≤Z weeks

**Validation methods:**
- Customer interviews (qualitative validation)
- Landing page tests (willingness to pay)
- Prototype testing (solution validation)
- Channel experiments (acquisition validation)

**Required confidence levels:**
- High-risk assumptions (market size, pricing): ≥75%
- Medium-risk assumptions (channels, messaging): ≥60%
- Low-risk assumptions (features, operations): ≥50%

---

### ✅ ICP Definition

**At least 1 segment has complete ICP:**

- [ ] ICP file exists: `research/customer/icp/{segment}-icp.yaml`
- [ ] Observable filters defined (firmographics, technographics, behavioral)
- [ ] Qualification criteria documented
- [ ] Sample companies identified (5-10 examples)

**ICP quality criteria:**
- Filters are observable (can be verified without talking to customer)
- Segment is reachable (you know where to find them)
- Segment is actionable (you can target them specifically)
- Sample companies match filters 100%

---

### ✅ Sales Narratives

**Sales messaging exists for 1+ segment:**

- [ ] Narrative files exist: `threads/sales/narrative/{segment}/`
  - [ ] problem-narrative.md
  - [ ] solution-narrative.md
  - [ ] specifics-narrative.md

**Narrative quality criteria:**
- Problem resonates with ICP (validated through interviews)
- Solution addresses root cause (not just symptoms)
- Specifics include proof points (metrics, case studies, demos)

---

### ✅ Sales Materials

**Deliverables exist for 1+ segment:**

- [ ] Materials exist: `artifacts/sales/{segment}/materials/`
  - [ ] pitch-deck.md
  - [ ] one-pager.md
  - [ ] call-scripts.md
  - [ ] email-templates.md

**Materials quality criteria:**
- Aligned with Canvas positioning
- Tailored to segment (not generic)
- Include specific metrics and proof points
- Reviewed by founder (technical accuracy verified)

---

### ✅ Marketing Narratives

**Content strategy defined:**

- [ ] Narrative files exist: `artifacts/marketing/narrative/`
  - [ ] content-pillars.md (3-5 strategic themes)
  - [ ] seo-strategy.md (keywords by funnel stage)
  - [ ] brand-voice.md (tone guidelines)
  - [ ] channel-guidelines.md (format specs)

**Narrative quality criteria:**
- Content pillars align with Canvas UVP
- SEO keywords validated (search volume, competition)
- Brand voice matches target audience
- Channel specs are actionable

---

### ✅ Engineering Validation (OPTIONAL - only if building systems)

**⚠️ CONDITIONAL:** Only validate this section if you're building technical products with backend systems. Skip entirely for non-technical products.

**System correctness validated:**

- [ ] Services pass 100% type safety validation
- [ ] Standardization layer applied to all services:
  - [ ] Auth (JWT, RBAC)
  - [ ] Validation (input schemas, error responses)
  - [ ] Response formats (standardized status codes)
  - [ ] Logging (structured, distributed tracing)
  - [ ] Rate limiting (quotas, throttling)
- [ ] OpenAPI specs generated for all services
- [ ] Integration tests passing in staging environment
- [ ] Code generation success rate >95%
- [ ] Correctness validation complete (composition laws verified)

**Engineering artifacts exist:**

- [ ] Service code: `engineering/services/{service}/`
- [ ] Service blueprints: `engineering/services/{service}/blueprint.yaml`
- [ ] Standards documentation: `engineering/standards/`
- [ ] Domain models: `engineering/domain/`
- [ ] Engineering threads: `threads/engineering/services/{service}/`

**Engineering quality criteria:**
- All services mathematically correct (category theory validation passed)
- Type safety: 100% coverage (all functions typed)
- Composition laws verified: Identity and associativity hold
- Standards uniformly applied: No service bypasses standardization layer
- Canvas synchronized: `09-solution.md` reflects implemented features

**Integration validation:**
- Sales demo environment includes engineering features
- Marketing content accurately describes product capabilities
- Canvas `09-solution.md` matches actual implementation

---

### ✅ Operational Readiness

**Skills installed and tested:**

- [ ] foundation-builder installed
- [ ] icp-generator tested (1+ segment)
- [ ] sales-narrative tested (1+ segment)
- [ ] sales-execution subskills installed
- [ ] marketing-narrative tested
- [ ] marketing-execution subskills installed
- [ ] causal-flow installed
- [ ] ops-dashboard installed (optional pre-launch)
- [ ] **category-theoretic-system-design installed** (if building systems)
- [ ] **standardization-layer installed** (if building systems)

**Infrastructure ready:**

- [ ] Git repository initialized
- [ ] Directory structure created (strategy/, threads/, artifacts/, ops/)
- [ ] Canvas files in version control
- [ ] Markdown editing environment ready

---

## Pre-Launch Validation Workflow

### Step 1: Canvas Self-Audit (30 minutes)

Go through each Canvas section and ask:
1. Is this backed by evidence (not just opinion)?
2. Are numbers included where relevant?
3. Can I trace this to a specific source (interview, research, experiment)?

**If answer is "no" to any question:** Incomplete. Gather evidence before proceeding.

---

### Step 2: Assumption Stress Test (1 hour)

For each critical assumption in `10-assumptions.md`:

1. **What evidence supports this?**
   - Customer interviews: How many? What did they say?
   - Experiments: What was tested? What were results?
   - Research: What data backs this up?

2. **What's the confidence level?**
   - 0-50%: Untested or weak evidence → Run validation experiment
   - 50-75%: Some evidence → Acceptable for medium-risk assumptions
   - 75-100%: Strong evidence → Good for high-risk assumptions

3. **What if I'm wrong?**
   - Fatal flaw: Business fails completely → Must validate to ≥75%
   - Major impact: Pivot required → Must validate to ≥60%
   - Minor impact: Adjustments needed → Can proceed with ≥50%

**Action:** Prioritize validation experiments for high-risk assumptions with low confidence.

---

### Step 3: ICP Validation (2-3 hours)

Test your ICP definition with 5-10 target companies:

1. **Apply filters:** Can you find companies matching your observable filters?
2. **Verify reachability:** Can you get contact info for decision-makers?
3. **Test messaging:** Do they respond to outreach (even if just to decline)?

**If you can't find 10 companies matching your ICP:** ICP is too narrow or filters are not observable. Revise.

---

### Step 4: Narrative Testing (3-5 customer conversations)

Share your sales narratives with 3-5 ICP-matching prospects:

1. **Problem narrative:** Do they agree the problem exists and is severe?
2. **Solution narrative:** Does the approach resonate? Any objections?
3. **Specifics narrative:** Are proof points credible? What questions arise?

**Red flags:**
- They don't recognize the problem → Problem narrative needs work
- They don't believe solution works → Solution narrative needs proof
- They have major unaddressed objections → Specifics narrative incomplete

---

### Step 5: Materials Review (1 hour)

Review sales materials with founder lens:

1. **Technical accuracy:** Are metrics, features, capabilities correct?
2. **Positioning consistency:** Does messaging align with Canvas UVP?
3. **Proof points:** Are specific numbers, case studies, demos included?

**If materials don't pass technical accuracy check:** Regenerate with correct information.

---

### Step 6: Go/No-Go Decision

**Green light criteria (all must be true):**
- ✅ Canvas 100% complete (no TBD, all evidence-backed)
- ✅ Critical assumptions validated (≥75% confidence)
- ✅ ICP validated (10+ matching companies found)
- ✅ Narratives tested (3+ positive customer conversations)
- ✅ Materials reviewed (technical accuracy verified)

**Yellow light (proceed with caution):**
- ⚠️ Medium-risk assumptions at 60-75% confidence
- ⚠️ ICP slightly broad or narrow (can adjust post-launch)
- ⚠️ Narratives resonate but need minor refinement

**Red light (do not launch):**
- 🛑 Critical assumptions <60% confidence
- 🛑 ICP not validated (can't find matching companies)
- 🛑 Narratives don't resonate (problem not recognized)
- 🛑 Materials technically inaccurate

---

## Post-Launch Validation

After launch, continuous validation happens through operations:

### Sales Validation (Per Thread)
- **Stage 6 (Learning):** Captures deal outcomes, validates assumptions
- **Canvas updates:** Confidence scores adjusted based on results
- **Pattern detection:** Cross-thread patterns flag strategy shifts

### Marketing Validation (Per Campaign)
- **Stage 6 (Learning):** Measures content performance, validates hypotheses
- **Canvas updates:** Content performance assumptions updated
- **Opportunity detection:** Top performers trigger follow-up content

### Quarterly Canvas Review
- Review assumption confidence scores
- Update market size estimates
- Refine ICP based on closed deals
- Adjust pricing based on sales cycles

---

## Common Validation Failures

### ❌ "I've talked to 20 people but still uncertain"
**Problem:** Asking wrong questions or talking to wrong people.

**Fix:**
- Validate observable filters: Are you talking to ICP-matching prospects?
- Ask specific questions: "Would you pay $X for Y?" not "Is this interesting?"
- Look for commitments: Pilot agreements, LOIs, waitlist signups (not just "sounds cool")

---

### ❌ "Assumptions validated but deals aren't closing"
**Problem:** Validated the wrong assumptions.

**Fix:**
- Test the full buying journey (not just problem recognition)
- Validate willingness to pay (not just interest)
- Check decision-making authority (are you talking to buyers?)

---

### ❌ "ICP too narrow, can't find enough prospects"
**Problem:** Over-constrained filters.

**Fix:**
- Relax one filter at a time (test impact on fit)
- Expand to adjacent segments (test messaging overlap)
- Validate segment size was correctly estimated

---

### ❌ "Narratives tested well but sales aren't converting"
**Problem:** Gap between narrative and reality.

**Fix:**
- Verify product delivers on promises (pilot results confirm claims)
- Check pricing alignment (narrative value matches price)
- Validate proof points are credible (metrics, case studies real)

---

## Validation Metrics to Track

### Pre-Launch
- Customer interviews completed: Target 10-15
- Assumption confidence: Average ≥70%
- ICP matching companies found: Target 50-100
- Narrative positive feedback: Target ≥80%

### Post-Launch (First 90 Days)
- Sales qualified leads: Target varies by segment
- Demo conversion rate: Target ≥40%
- Pilot conversion rate: Target ≥60%
- Close rate (qualified): Target ≥50%

### Post-Launch (Marketing, First 90 Days)
- Content published: Target 2-4 pieces/month
- Organic sessions: Target varies by keyword
- Demo requests from content: Target 1-3% conversion
- Pipeline influenced: Track attribution

---

## Next Steps

- Start Canvas setup: [Canvas Setup](canvas-setup.md)
- Review timeline: [Timeline Guide](timeline.md)
- Learn operations workflow: [How It Works](../overview/how-it-works.md)