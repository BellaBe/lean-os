# Frequently Asked Questions

## General

**Q: What is LeanOS?**

A: AI-native operating system that automates 95%+ of startup operations. Built for GlamYouUp, designed for any B2B SaaS. Human provides strategy, AI handles execution.

**Q: How is this different from using ChatGPT/Claude directly?**

A: LeanOS uses specialized skills (agents) for specific tasks, maintains single source of truth (Canvas), stores complete decision narratives (threads), and auto-updates strategy from learning. Not a chatbot - an operating system.

**Q: What do I need to use LeanOS?**

A: Claude AI access (Sonnet 4.5), Git, markdown editing, willingness to populate Lean Canvas, commitment to evidence-based decisions.

---

## Business Model Modes

**Q: What's the difference between VENTURE and BOOTSTRAP modes?**

A: VENTURE prioritizes scale (MAU, ARR growth, market share) and tolerates burn for growth. BOOTSTRAP prioritizes profit (MRR, cash flow, margin) and requires profitability from the start. Mode determines research approach, decision criteria, and metrics tracked.

**Q: Which mode should I choose?**

A: VENTURE if funded/raising or targeting billion-dollar markets requiring scale. BOOTSTRAP if self-funded or building profitable niche business. HYBRID if proving PMF first, then raising funding to scale.

**Q: Can I switch modes later?**

A: Yes. Update `strategy/canvas/00-business-model-mode.md`. Common: BOOTSTRAP → VENTURE after proving profitability and deciding to raise funding.

**Q: How does mode affect operations?**

A: Mode determines:
- Which market research skill to use (venture-analysis vs bootstrap-analysis)
- How impact scores are calculated (strategic value vs revenue impact)
- Which metrics are tracked (MAU/ARR vs MRR/profit)
- Decision prioritization (market size vs time to cash)

**Q: What if I'm not sure which mode I'm in?**

A: Ask: Are you funded or raising? (VENTURE). Need profitability within 3 months? (BOOTSTRAP). Start BOOTSTRAP, switch to VENTURE if you raise funding.

---

## Canvas & Foundation

**Q: Why start with Canvas? Can I skip it?**

A: No. Canvas is single source of truth. Every skill reads from Canvas. Without it, you have no foundation for ICP, narratives, materials, or content strategy.

**Q: How long does Canvas setup take?**

A: Human input: <10 hours total across all phases. Real-world validation: 3-12 weeks (customer interviews, experiments). Bottleneck is validation, not AI.

**Q: What if my assumptions are wrong?**

A: That's expected. Canvas tracks confidence scores. Stage 6 (Learning) validates/invalidates assumptions automatically. Pivot based on evidence, not opinions.

**Q: Can I update Canvas manually?**

A: Yes, but Stage 6 auto-updates are preferred. Manual updates should be for strategic shifts not captured in threads.

---

## Sales Operations

**Q: How does ICP generation work?**

A: Uses Canvas 04-segments.md to create observable filters (firmographics, technographics, behavioral). Output is YAML file with qualification criteria and sample companies.

**Q: What if I can't find prospects matching my ICP?**

A: ICP too narrow. Relax one filter at a time, test impact on fit. Or expand to adjacent segments.

**Q: Do I need to approve every sales email?**

A: No. AI handles outreach sequences autonomously. You only review materials once per segment (pitch deck, scripts, templates).

**Q: What if a deal doesn't close?**

A: Stage 6 captures why (lost, stalled). Learning informs Canvas updates. Pattern of losses may indicate ICP mismatch or messaging issues.

---

## Marketing Operations

**Q: How does marketing content get created?**

A: Content is triggered by business learning (sales threads, strategic decisions), not arbitrary calendars. When threads complete Stage 6, content-strategy scans for insights worth sharing. High-priority opportunities (≥0.7) flagged for approval.

**Q: Can I manually request content?**

A: Yes. Specify topic, keyword, content type, source thread. AI skips content-strategy and goes directly to content-generation → SEO → distribution → tracking.

**Q: How is content quality maintained?**

A: (1) Brand voice guidelines enforce tone, (2) Human reviews drafts for technical accuracy, (3) Content patterns ensure structure, (4) Performance tracking identifies underperformers.

**Q: What if content underperforms?**

A: performance-tracking flags underperformers (<50% expected traffic). AI recommends: (1) SEO optimization if ranking issue, (2) Topic reassessment if no audience, (3) Pillar retirement if systematic underperformance.

**Q: How does marketing influence sales?**

A: Published content drives organic traffic → Demo requests → Sales threads with attribution metadata → Stage 6 tracks pipeline influenced → Performance-tracking updates content ROI → Canvas updates assumptions.

**Q: How many content pieces per month?**

A: Variable, based on business learning. Target: 2-4 high-quality pieces/month (1 per major learning). Quality over quantity.

---

## Engineering & Systems (Optional)

**Q: When should I use the engineering layer?**

A: Only when building technical products (microservices, backend systems). If your product is SaaS with a backend, activate engineering skills. If you're selling services or non-technical products, skip this layer entirely.

**Q: What's category-theoretic system design?**

A: Mathematical approach to building software using category theory. Transforms natural language requirements into mathematically correct, composable services with type safety guarantees. Ensures system correctness through algebraic data types, morphisms, and composition laws.

**Q: How does the engineering pipeline work?**

A: 8-skill pipeline: Requirements → ADT analysis → Domain modeling → Type validation → Transformation mapping (functors) → Service composition → Code generation (FastAPI/Python) → Blueprint creation (OpenAPI specs) → Correctness validation.

**Q: What does the standardization layer do?**

A: Applies 5 cross-cutting concerns uniformly to all services: (1) JWT auth + RBAC, (2) Input validation + error responses, (3) Standard response formats, (4) Structured logging + tracing, (5) Rate limiting + quotas. Ensures consistency across microservices.

**Q: Do I need to know category theory?**

A: No. Skills handle the mathematical formalism. You provide requirements in natural language, AI generates mathematically correct code. Understanding helps but isn't required.

**Q: How does engineering integrate with sales/marketing?**

A: **Sales → Engineering:** Pilot requires custom features → Engineering thread created → Feature implemented → Sales demo updated. **Engineering → Marketing:** Product capabilities validated → Technical content created → Features accurately described.

**Q: Can engineering run independently from sales/marketing?**

A: Yes. Engineering layer is optional and operates independently. Activate only when building systems. Business operations (sales, marketing) work without engineering.

**Q: What if system design fails validation?**

A: Correctness validator identifies violations (type safety, composition laws). Thread returns to earlier stage (design or type validation), fixes applied, re-validated. 100% correctness required before deployment.

**Q: How long does it take to build a service?**

A: Depends on complexity. Simple CRUD service: hours. Complex domain with multiple compositions: days. Measure: Engineering Thread Velocity (requirement → deployed service).

---

## Daily Operations

**Q: What does "5-minute review" actually mean?**

A: Read ops/today.md (auto-generated). Approve high-priority content (30 sec). Review drafts for accuracy (2 min). Review call prep (30 sec). Total: 3-5 min, not including scheduled calls.

**Q: What if I miss a day?**

A: AI continues autonomous operations. ops/today.md accumulates flagged items. Review when back. Nothing breaks.

**Q: How do I know AI made correct decisions?**

A: ops/today.md shows "Decisions made by AI (last 24h)". Review for accuracy. ops/patterns.md flags anomalies. If AI consistently makes errors, investigate skill or Canvas quality.

**Q: What's the difference between business metrics and operational metrics?**

A: **Business metrics** (artifacts/business/metrics.md via `business-metrics-tracker`) track actual business outcomes: revenue (MRR/ARR), profitability, CAC, LTV, growth rates. These answer: "Is the business growing and profitable?" **Operational metrics** (ops/ dashboards via `ops-dashboard`) track LeanOS system efficiency: thread velocity, AI autonomy rate, decision latency. These answer: "Is LeanOS running efficiently?" Both are important but serve different purposes.

---

## Thread Management

**Q: What's the difference between engineering, business, sales, and marketing threads?**

A: Engineering = system design/implementation (optional, only if building systems). Business = strategic decisions. Sales = deal progression or campaigns. Marketing = content execution. All use 6-stage flow.

**Q: Do I create threads manually?**

A: AI creates threads automatically when needed (new deal, content opportunity). You can manually create business threads for strategic decisions.

**Q: What if a thread gets stuck?**

A: ops/velocity.md flags bottlenecks. Common causes: missing information (go back to earlier stage), external dependency (legal, vendor), human approval required (flag in ops/today.md).

---

## Troubleshooting

**Q: Content opportunities not detected**

A: Check thread completion (Stage 6 exists), manually trigger content-strategy scan, verify priority threshold (≥0.7).

**Q: Content draft quality low**

A: Check source thread has sufficient learning, verify brand-voice.md exists, ensure content patterns loaded.

**Q: Sales materials don't match brand**

A: Regenerate with updated Canvas, verify Canvas UVP/positioning is current.

**Q: Too many high-priority flags**

A: Lower priority threshold (>0.7 → >0.8), or adjust implication analysis in Stage 3.

---

## Integration

**Q: How does closed-loop attribution work?**

A: Sales thread → Stage 6 learning → Canvas updated → Marketing detects opportunity → Content published → SEO drives traffic → Demo requested → Sales thread with attribution → Stage 6 tracks influenced pipeline → Marketing performance updated → Loop continues.

**Q: What if sales and marketing aren't aligned?**

A: Both read from same Canvas. Misalignment indicates Canvas quality issue or narratives need updating.

---

## Technical

**Q: What tech stack does LeanOS use?**

A: Claude Sonnet 4.5, Claude Skills, Python (optional for tooling), Bash, Markdown, Git. No external services for MVP.

**Q: Can I self-host?**

A: LeanOS is operated by Claude AI via Claude Skills. "Self-hosting" means running locally with Claude API access.

**Q: What about data privacy?**

A: All data local (Canvas, threads, artifacts). No external services except Claude API. Control what gets shared in threads.

**Q: Can I use this with other LLMs?**

A: Skills are designed for Claude. Porting to other LLMs would require rewriting skills and testing extensively.

---

## Scaling

**Q: What happens when I add more segments?**

A: Run icp-generator + sales-narrative + sales-execution for each new segment. Marketing narratives update to cover all segments. Linear scaling per segment.

**Q: What if I need more than 1 human?**

A: Multiple humans can review ops/today.md. Assign approval responsibilities (e.g., sales lead approves materials, marketing lead approves content).

**Q: When do I outgrow LeanOS?**

A: When >5 people needed for operations, or when processes become too complex for AI autonomy. Typically Series A+ stage.

---

For more details, see:
- [What is LeanOS?](../overview/what-is-leanos.md)
- [How It Works](../overview/how-it-works.md)
- [Troubleshooting](common-issues.md)