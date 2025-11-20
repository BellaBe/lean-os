# Sales-Marketing-Engineering Integration Loop

LeanOS operates three closed-loop systems that feed each other continuously: Sales ’ Engineering, Engineering ’ Marketing, and Marketing ’ Sales.

## The Three-Way Loop

```text
        Sales Learning
             “
    Engineering Features  Canvas (09-solution.md)
             “
    Product Capabilities
             “
    Marketing Content
             “
    Organic Traffic ’ Demo Requests
             “
        Sales Pipeline
             “
    (Loop continues)
```

---

## Loop 1: Sales ’ Engineering

**Trigger:** Sales pilot requires custom features or integrations

### Flow

1. **Sales Thread (Stage 6):** Pilot customer requests white-label SDK
2. **Engineering Thread Created:** `threads/engineering/services/white-label-sdk/`
3. **Engineering Executes (6-stage flow):**
   - Stage 1: Input (pilot requirement, customer use case)
   - Stage 2: Hypothesis (design approach, architectural assumptions)
   - Stage 3: Implication (implementation effort, timeline, impact on pilot)
   - Stage 4: Decision (technical approach, alternatives considered)
   - Stage 5: Actions (code generation, testing, deployment)
   - Stage 6: Learning (validation results, performance metrics)
4. **Sales Demo Updated:** New capability added to pitch deck, demo environment
5. **Pilot Proceeds:** Custom feature delivered, pilot success tracked

### Examples

**Example 1: White-Label SDK Request**
```
Sales: "ElsaAI wants white-label SDK for their app"
’ Engineering: Build SDK with configurable branding
’ Output: `engineering/services/white-label-sdk/`
’ Sales: Demo updated with SDK capabilities
’ Result: Pilot closed, SDK becomes standard offering
```

**Example 2: Integration Requirement**
```
Sales: "Shopify integration needed for 3 pilots"
’ Engineering: Build Shopify connector service
’ Output: `engineering/services/shopify-connector/`
’ Sales: Shopify integration added to materials
’ Result: 3 pilots close, new ICP segment identified (Shopify merchants)
```

### Integration Points

- **Sales materials auto-update:** When engineering thread completes (Stage 6), sales materials regenerate with new capabilities
- **Canvas synchronization:** Engineering updates `09-solution.md` with implemented features
- **Attribution tracking:** Deals won via custom features tracked back to engineering thread

---

## Loop 2: Engineering ’ Marketing

**Trigger:** Product capabilities validated, ready for content creation

### Flow

1. **Engineering Thread (Stage 6):** Feature validated, deployed to production
2. **Canvas Updated:** `09-solution.md` reflects new capability with evidence
3. **Marketing Scan:** content-strategy detects new product capability
4. **Marketing Thread Created:** `threads/marketing/content/{feature-explanation}/`
5. **Marketing Executes:**
   - Draft: Technical content explaining capability
   - Review: Human verifies technical accuracy (already validated by engineering)
   - SEO: Optimize for feature-related keywords
   - Publish: Blog, LinkedIn, documentation
   - Track: Monitor traffic, demos from content
6. **Sales Enablement:** Content shared in follow-up emails, used in nurture campaigns

### Examples

**Example 1: Category-Theoretic Design**
```
Engineering: Implemented category-theoretic composition for fit + color services
’ Canvas: 09-solution.md updated with "Compositional AI Architecture"
’ Marketing: Technical article "How We Built Composable Fashion AI"
’ Distribution: Blog (technical founders), LinkedIn (CTOs), HN (developers)
’ Result: 45 inbound demos from CTOs building similar systems
```

**Example 2: Standardization Layer**
```
Engineering: Applied standardization layer (auth, validation, response, logging, rate-limiting)
’ Canvas: 09-solution.md updated with "Enterprise-Grade Standards"
’ Marketing: Case study "From MVP to Enterprise: Our Standardization Journey"
’ Distribution: Blog (engineering leaders), LinkedIn (VPs Engineering)
’ Result: Enterprise segment identified, 8 qualified leads
```

### Integration Points

- **Accurate technical content:** Engineering validation ensures marketing claims are true
- **Canvas as source:** Marketing reads from `09-solution.md`, never duplicates
- **Feature ’ Keyword mapping:** Engineering capabilities drive SEO strategy
- **Attribution:** Content performance tracked back to engineering thread

---

## Loop 3: Marketing ’ Sales

**Trigger:** Content published, driving organic traffic

### Flow

1. **Marketing Thread (Stage 6):** Content published, performance tracked
2. **SEO Drives Traffic:** Organic sessions from target keywords
3. **Demo Requested:** Visitor requests demo via form
4. **Sales Thread Created:** `threads/sales/{company-name}/`
   - Metadata includes: `source: marketing/content/{topic}/`, `attribution: Blog article`
5. **Sales Executes:**
   - Qualification call (human)
   - Demo presentation (human, AI prep materials)
   - Pilot negotiation (human)
   - Contract close (human)
6. **Sales Thread (Stage 6):** Deal outcome recorded
   - If won: Pipeline influenced by content tracked
   - If lost: Reasons inform content strategy
7. **Marketing Updated:** `performance-tracking` updates content ROI
8. **Next Opportunity Detected:** Content-strategy scans for new topics

### Examples

**Example 1: White-Label Case Study**
```
Marketing: Published "ElsaAI White-Label Success Story"
’ SEO: Ranks for "white-label fashion AI", "custom SDK"
’ Traffic: 650 sessions in 30 days
’ Demos: 8 demo requests from content
’ Sales: 2 pilots started, 1 closed ($500K ARR)
’ Attribution: $500K attributed to blog article
’ Canvas: H1 validated (case studies convert 2x better than guides)
’ Next: Content-strategy flags opportunity for white-label implementation guide
```

**Example 2: Technical Architecture Post**
```
Marketing: Published "Category-Theoretic System Design"
’ SEO: Ranks for "category theory microservices", "compositional systems"
’ Traffic: 1,200 sessions (technical audience)
’ Demos: 12 requests from CTOs, VPs Engineering
’ Sales: 5 pilots (enterprise segment), 2 closed ($1.2M combined ARR)
’ Attribution: $1.2M attributed to technical article
’ Canvas: A5 validated (enterprise segment values mathematical correctness)
’ Next: Content-strategy flags "Enterprise Standardization Patterns" series
```

### Integration Points

- **Attribution metadata:** Every sales thread tracks content source
- **Conversion tracking:** Marketing measures traffic ’ demos ’ revenue
- **ICP validation:** Content performance validates segment assumptions
- **Closed-loop learning:** Sales outcomes inform next content topics

---

## Complete Three-Way Loop Example

### Scenario: Building a White-Label SDK

**Week 1: Sales Discovery**
- Sales pilot (ElsaAI) requests white-label SDK
- Sales thread: `threads/sales/elsaai-white-label/`
- Stage 6: Learning captured - "Luxury brands prefer white-label (N=1)"

**Week 2-3: Engineering Build**
- Engineering thread: `threads/engineering/services/white-label-sdk/`
- AI executes: ADT analysis ’ Domain modeling ’ Code generation ’ Standardization
- Output: `engineering/services/white-label-sdk/` (FastAPI service, OpenAPI spec)
- Stage 6: Validation complete - SDK deployed to staging
- Canvas updated: `09-solution.md` now includes "White-Label SDK"

**Week 4: Sales Enablement**
- Sales materials regenerate with SDK capability
- ElsaAI pilot proceeds with SDK
- 4 more luxury brands close using SDK
- Stage 6: "Luxury brands prefer white-label (N=5, 100%)"

**Week 5: Marketing Content**
- Content-strategy detects pattern (5/5 luxury brands chose white-label)
- Marketing thread: `threads/marketing/content/elsaai-white-label-case-study/`
- Content published: "How ElsaAI Scaled to 1M Users with Our White-Label SDK"
- SEO: Targets "white-label fashion AI", "custom SDK", "brand customization"

**Week 6-8: Marketing ’ Sales Loop**
- Organic traffic: 650 sessions/month
- Demo requests: 8 from content
- Sales threads created: 8 new opportunities
- Attribution: All 8 have `source: marketing/content/elsaai-white-label/`
- Conversions: 2 pilots started, 1 closed ($500K ARR)
- Stage 6: Performance tracking updates content ROI

**Week 9: Next Iteration**
- Content-strategy scans sales threads
- Detects: White-label implementation questions (common objection)
- Flags: New opportunity "White-Label SDK Implementation Guide" (priority 0.78)
- Human approves
- Marketing creates implementation guide
- Loop continues...

### Metrics Tracked

**Sales ’ Engineering:**
- Custom feature requests: 3/month
- Engineering delivery time: 2 weeks avg
- Pilot close rate (with custom features): 80%

**Engineering ’ Marketing:**
- Features documented: 5/quarter
- Technical content published: 3/quarter
- Inbound demos from technical content: 12/month

**Marketing ’ Sales:**
- Organic traffic: 2,500 sessions/month
- Demo conversion rate: 1.2%
- Demos from content: 30/month
- Pipeline influenced: $2.5M
- Content-attributed revenue: $1.8M (last 12 months)

---

## Canvas Integration

All three loops update Canvas continuously:

### Sales ’ Canvas
- **04-segments.md:** New segments identified from deal patterns
- **10-assumptions.md:** Hypotheses validated/invalidated from sales learning
- **11-pricing.md:** Pricing validated from closed deals
- **13-metrics.md:** Sales cycle, win rate, ASP updated

### Engineering ’ Canvas
- **09-solution.md:** Features implemented, architecture validated
- **10-assumptions.md:** Technical assumptions validated (performance, scalability)
- **13-metrics.md:** Engineering velocity, system correctness tracked

### Marketing ’ Canvas
- **10-assumptions.md:** Content hypotheses validated (what converts)
- **13-metrics.md:** Traffic, conversion rates, content ROI tracked
- **14-growth.md:** Channels validated (SEO effectiveness)

**Single source of truth:** All three functions read from and write to Canvas. No duplication.

---

## When Loops Break

### Problem: Sales requests features but engineering doesn't deliver
**Symptom:** Pilot stalls, custom feature not built
**Diagnosis:** Engineering thread stuck (validation failed, complexity underestimated)
**Fix:** ops/today.md flags engineering bottleneck, human intervention, adjust scope or timeline

### Problem: Engineering builds features but marketing doesn't create content
**Symptom:** Product capabilities not documented
**Diagnosis:** Canvas not updated (09-solution.md out of sync), content-strategy not scanning
**Fix:** Manually update Canvas, trigger content-strategy scan, verify daily scan active

### Problem: Marketing creates content but sales doesn't get leads
**Symptom:** Traffic high, demo conversion low
**Diagnosis:** ICP mismatch (wrong audience), content too technical/not technical enough
**Fix:** Review content performance (underperformers), adjust SEO strategy, revalidate ICP

### Problem: Sales attributes no revenue to marketing content
**Symptom:** Content published but zero attribution
**Diagnosis:** Attribution metadata missing, sales threads not tracking source
**Fix:** Verify thread metadata includes `source:` field, backfill recent threads

---

## Success Indicators

### Healthy Three-Way Loop

 **Sales ’ Engineering:** 2-4 custom features/quarter, 80%+ pilot close rate
 **Engineering ’ Marketing:** 100% feature parity (content matches implementation)
 **Marketing ’ Sales:** >50% demos from content, >$1M attributed revenue/year
 **Canvas Integrity:** Zero duplication, 100% traceability, >95% auto-update accuracy
 **Cycle Time:** <2 weeks sales ’ engineering ’ marketing ’ sales

### Broken Loop Indicators

  **Sales ’ Engineering:** Features requested but not built (engineering bottleneck)
  **Engineering ’ Marketing:** Features exist but not documented (content gap)
  **Marketing ’ Sales:** Content published but zero demos (ICP mismatch)
  **Canvas Drift:** 09-solution.md doesn't match implementation
  **Attribution Failure:** Revenue not tracked back to content

---

## Next Steps

- **Activate sales:** [Sales Workflow](../operations/sales-workflow.md)
- **Activate marketing:** [Marketing Workflow](../operations/marketing-workflow.md)
- **Activate engineering:** [All Skills](../skills/all-skills.md#engineering-skills-system-building---optional)
- **Monitor loops:** [Daily Routine](../operations/daily-routine.md)
- **Track metrics:** [Success Metrics](success-metrics.md)

---

**Last Updated:** 2025-11-20
**Version:** 1.2 (Three-way integration: Sales ” Engineering ” Marketing)
