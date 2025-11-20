# Timeline Guide: Pre-Launch to Operations

The bottleneck is NOT AI execution - it's human decisions and real-world validation.

Each phase shows three timelines:
- **Human time:** Context provision and decision-making
- **AI time:** Research, analysis, Canvas population
- **Real-world time:** Validation through customer feedback and experiments

---

## Phase 0a: Discovery (Market Intelligence)

**Goal:** Market research, customer segment identification, problem validation

### Human Time: 1-2 hours
- Provide initial business idea and constraints (15 min)
- Review Canvas sections 01-06 for accuracy (30 min)
- Approve market intelligence findings (15 min)
- Identify customer segments to interview (15 min)

### AI Time: 2-3 hours
- Market research (TAM/SAM/SOM, competitive analysis)
- Customer segment identification
- Problem hypothesis generation
- Populate Canvas 01-06

### Real-World Validation: 1-2 weeks ⚠️ BOTTLENECK
- Customer problem interviews (5-10 interviews)
- Competitive product analysis
- Market trend validation

**Total elapsed:** 1-2 weeks (limited by real-world validation, not AI)

---

## Phase 0b: Definition (Value Prop & Business Model)

**Goal:** Define UVP, positioning, pricing, and MVP scope

### Human Time: 1-2 hours
- Provide product vision and constraints (15 min)
- Review UVP and positioning (30 min)
- Validate pricing assumptions (20 min)
- Approve Canvas sections 07-13 (20 min)

### AI Time: 2-3 hours
- Value proposition articulation
- Competitive positioning analysis
- Pricing strategy design
- Unit economics modeling
- Populate Canvas 07-13

### Real-World Validation: 3-5 days ⚠️ BOTTLENECK
- Pricing validation (customer surveys, competitor analysis)
- Value prop testing (landing page, customer conversations)

**Total elapsed:** 3-5 days (mostly validation, minimal human time)

---

## Phase 1a: Validation (Assumption Testing)

**Goal:** Test critical assumptions before building MVP

### Human Time: 2-3 hours
- Identify critical assumptions to test (30 min)
- Review experiment designs (30 min)
- Approve experiment execution (15 min)
- Analyze experiment results with AI (60 min)

### AI Time: 1-2 hours
- Design validation experiments
- Create test materials (landing pages, interview scripts)
- Analyze experiment results
- Update 10-assumptions.md

### Real-World Validation: 2-4 weeks ⚠️ MAJOR BOTTLENECK
- Run landing page tests (1 week minimum for traffic)
- Conduct customer interviews (5-10 interviews, 1-2 weeks)
- Prototype testing with early customers
- **Waiting for statistically significant results**

**Total elapsed:** 2-4 weeks (validation is the constraint)

---

## Phase 1b: Execution (MVP Build & Launch Prep)

**Goal:** Build MVP, create GTM strategy, prepare for launch

### Human Time: 1-2 hours
- Define MVP scope and priorities (30 min)
- Review GTM strategy (30 min)
- Approve sales/marketing narratives (30 min)

### AI Time: 2-4 hours
- GTM strategy design
- Channel selection and planning
- Sales narrative generation (per segment)
- Marketing narrative generation
- Populate Canvas 14-15

### Real-World Validation: 4-8 weeks ⚠️ MAJOR BOTTLENECK
- MVP development (depends on complexity)
- Beta testing with early customers
- **Building and testing the actual product**

**Total elapsed:** 4-8 weeks (MVP build is the constraint)

---

## Phase 1c: Engineering (System Building - OPTIONAL)

**Goal:** Build production-ready backend systems using category-theoretic design

**⚠️ CONDITIONAL:** Only activate this phase if building technical products (microservices, backend systems). Skip entirely for non-technical products or service businesses.

### Human Time: 2-4 hours
- Provide system requirements and architecture vision (30 min)
- Review domain models and type definitions (45 min)
- Approve service blueprints and OpenAPI specs (30 min)
- Review generated code for business logic accuracy (60 min)

### AI Time: 4-8 hours (per service)
- ADT analysis: Parse requirements → algebraic data types (30 min)
- Domain modeling: Extract entities, relationships, contexts (60 min)
- Type validation: Ensure type safety, composition correctness (30 min)
- Functor mapping: Define data transformations (morphisms) (45 min)
- Service composition: Compose services via category theory (60 min)
- Code generation: Generate FastAPI/Python microservices (60 min)
- Blueprint creation: Create OpenAPI specs, architecture docs (30 min)
- Correctness validation: Verify mathematical correctness (45 min)
- Standardization: Apply cross-cutting concerns (auth, validation, response, logging, rate-limiting) (60 min)

### Real-World Validation: 1-4 weeks ⚠️ POTENTIAL BOTTLENECK
- Deploy generated services to staging environment
- Integration testing with other system components
- Load testing and performance validation
- Security review of authentication and validation
- **Testing production-readiness of generated code**

### Output Artifacts
- `engineering/services/{service}/` - Generated microservice code (FastAPI/Python)
- `engineering/services/{service}/blueprint.yaml` - OpenAPI specifications
- `engineering/standards/` - Standardization patterns (auth, validation, response, logging, rate-limiting)
- `engineering/domain/` - Domain models, ADTs, entity relationships
- `threads/engineering/services/{service}/` - Engineering decision threads (6-stage flow)

### When to Activate
- Building B2B SaaS with backend API
- Microservices architecture required
- Complex domain logic with composition requirements
- Need type safety and mathematical correctness guarantees
- Custom features for sales pilots (white-label SDKs, integrations)

### When to Skip
- Selling services (consulting, agency)
- No-code/low-code MVP sufficient
- Using off-the-shelf platforms (Shopify, WordPress)
- Non-technical product (content, community)

**Total elapsed:** 1-4 weeks (system building + testing, conditional on technical complexity)

**Integration points:**
- **Phase 1b → Phase 1c:** MVP requirements drive system design
- **Phase 1c → Phase 2:** Engineering threads feed sales demos and marketing content
- **Sales pilots:** Custom features trigger new engineering threads during operations

---

## Phase 2: Launch (Activate Operations)

**Goal:** Sales and marketing operations live, continuous Canvas updates

### Human Time: <30 min/day ongoing
- Review ops/today.md (5 min)
- Approve content opportunities (2 min)
- Review draft content (10 min, 2-3x/week)
- Strategic decisions only (as needed)

### AI Time: Continuous autonomous operation
- Sales execution (prospecting, qualification, materials)
- Marketing execution (content creation, SEO, distribution)
- Thread management (6-stage flow for all decisions)
- Canvas updates from validated learning

### Real-World Validation: Continuous
- Sales cycle time (varies by segment)
- Content performance (7-30 day feedback loops)
- **Customer decision-making and sales cycles**

**Total time:** Ongoing operations (AI handles 95%+ of decisions)

---

## Summary: Total Pre-Launch Time

### Absolute Minimum (Aggressive): 3-4 weeks

**Breakdown:**
- Discovery: 1 week (5 customer interviews)
- Definition: 3 days (pricing validation)
- Validation: 1 week (landing page + 5 interviews)
- Execution: 1 week (simple MVP or no-code prototype)

**Human input:** <10 hours total  
**AI execution:** <15 hours total  
**Real-world validation:** 3-4 weeks ⚠️ This is the constraint

---

### Typical Timeline (Recommended): 6-8 weeks

**Breakdown:**
- Discovery: 2 weeks (10 customer interviews)
- Definition: 1 week (thorough pricing validation)
- Validation: 2-3 weeks (statistically significant tests)
- Execution: 2-3 weeks (functional MVP)

**Human input:** <10 hours total  
**AI execution:** <15 hours total  
**Real-world validation:** 6-8 weeks ⚠️ This is the constraint

---

### Conservative (Complex Product): 12+ weeks

**Breakdown:**
- Discovery: 3 weeks (extensive market research)
- Definition: 2 weeks (multiple pricing models tested)
- Validation: 4 weeks (multiple experiment iterations)
- Execution: 4+ weeks (complex MVP build)

**Human input:** <15 hours total  
**AI execution:** <20 hours total  
**Real-world validation:** 12+ weeks ⚠️ This is the constraint

---

## Marketing Activation Timeline

**Marketing doesn't wait for sales learning—it starts with Canvas/research, then improves with validation.**

### Week 1: Sales Activation
- Sales infrastructure operational (DTC segment ready)
- ICP defined, narratives generated, materials created

### Week 2 (PARALLEL): Initial Marketing
- **Sales:** DTC outreach begins (10 prospects contacted)
- **Marketing:** Initial content created (foundational, Canvas-based)
  - 2-3 articles from Canvas + research
  - Educational content (problem-focused)
  - Published BEFORE or DURING sales outreach

### Week 3-4: Refinement
- **Sales:** Threads complete Stage 6 (learning captured)
- **Marketing:** Content refined based on sales learning
  - Performance tracked
  - New opportunities detected

### Continuous: Closed Loop
- Sales learning → Content opportunities → Published → Drives demos → More learning

**Key principle:** Marketing content is live BEFORE or DURING sales outreach, not after.

---

## Phase Dependencies

```text
Phase 0a (Discovery)
    ↓ Canvas 01-06 complete
Phase 0b (Definition)
    ↓ Canvas 07-13 complete
Phase 1a (Validation)
    ↓ Critical assumptions validated
Phase 1b (Execution)
    ↓ Canvas 14-15 complete, MVP ready
Phase 1c (Engineering) [OPTIONAL - only if building systems]
    ↓ Services built, tested, deployed
Phase 2 (Launch)
    ↓ Operations live
```

**You can't skip required phases.** Each phase builds on the previous phase's outputs.

**Phase 1c (Engineering) is optional** - only activate when building technical products with backend systems.

---

## Validation Gates

Each phase has validation gates before proceeding:

### After Phase 0a (Discovery)
- ✅ 5+ customer problem interviews completed
- ✅ Market size estimated (TAM/SAM/SOM)
- ✅ Customer segments defined with observable filters
- ✅ Top 3 problems identified and ranked

### After Phase 0b (Definition)
- ✅ UVP articulated (single sentence)
- ✅ Pricing validated with customers
- ✅ MVP scope defined
- ✅ Unit economics modeled

### After Phase 1a (Validation)
- ✅ Critical assumptions tested
- ✅ Confidence ≥75% on key hypotheses
- ✅ Invalidated assumptions addressed (pivot or proceed)

### After Phase 1b (Execution)
- ✅ MVP built and tested
- ✅ GTM strategy defined
- ✅ Sales narratives generated (1+ segment)
- ✅ Marketing narratives created

### After Phase 1c (Engineering - OPTIONAL)
- ✅ Services pass 100% type safety validation
- ✅ Standardization layer applied to all services
- ✅ OpenAPI specs generated for all services
- ✅ Integration tests passing in staging environment
- ✅ Code generation success rate >95%
- ✅ Correctness validation complete (composition laws verified)

### Launch Readiness
- ✅ All 15 Canvas sections populated with evidence
- ✅ Critical assumptions validated (confidence ≥75%)
- ✅ ICP defined for at least 1 segment
- ✅ Sales materials generated
- ✅ Marketing content strategy defined

---

## Common Timeline Mistakes

### ❌ Waiting for "complete" Canvas before starting
Canvas is living documentation. Start with Phase 0a, iterate continuously.

### ❌ Skipping customer validation
No amount of AI analysis replaces talking to real customers. This is the bottleneck by design.

### ❌ Building MVP before validating assumptions
Phase 1a (Validation) happens BEFORE Phase 1b (Execution). Don't build what customers don't want.

### ❌ Waiting for sales learning to start marketing
Marketing starts with Canvas + research (Week 2). Sales learning improves it (Week 3+).

### ❌ Trying to compress real-world validation
You can't force customers to respond faster or experiments to yield results sooner. Accept the timeline.

---

## Acceleration Strategies

### To compress Discovery (Phase 0a):
- Focus on 1-2 segments initially (add more later)
- Use existing research (reports, competitor analysis)
- Leverage warm intros for customer interviews

### To compress Definition (Phase 0b):
- Test pricing with landing page (A/B test)
- Use competitor pricing as baseline
- Start with simple revenue model (add complexity later)

### To compress Validation (Phase 1a):
- Test fewer assumptions (focus on critical ones)
- Use smoke tests (landing page, waitlist)
- Accept lower confidence (60-70% vs 75%+)

### To compress Execution (Phase 1b):
- Build no-code MVP (Webflow, Bubble, Airtable)
- Use off-the-shelf components
- Limit MVP scope aggressively (1-2 features)

**You cannot compress real-world validation time.** Customer interviews, experiment results, and MVP testing take as long as they take.

---

## Next Steps

- Understand validation criteria: [Validation Guide](validation.md)
- Start Canvas setup: [Canvas Setup](canvas-setup.md)
- Learn operations workflow: [How It Works](../overview/how-it-works.md)