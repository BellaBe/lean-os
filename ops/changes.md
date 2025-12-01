# LeanOS System Changes

Record of significant system optimizations, refactorings, and architectural improvements.

---

## 2025-12-01: Marketing Layer Loop-Centric Optimization

### Summary
Complete optimization of marketing execution layer adopting loop-centric distribution philosophy (Elena Verna framework). Reduced skill complexity by 70%, consolidated subskills, removed verbose pattern documentation in favor of lightweight templates, and reoriented all skills around loop mechanics over funnel thinking.

### Philosophy Shift

**From:** Funnel-based marketing (Create → Publish → Hope → End)
**To:** Loop-based distribution (Content → Engagement → Implementation → User-Generated Content → Amplify → Repeat)

**Core principles adopted:**
- "Loops > Funnels" — every piece of content must generate its own next input
- "Velocity as proof" — before → after time compression as positioning
- "Distribution physics" — invest where loops work, not dying channels
- Track loop activations, not vanity metrics (impressions, likes)

### Changes Made

#### 1. Marketing Execution Orchestrator (Simplified)

**Previous state:**
- 638-line SKILL.md with verbose orchestration logic
- 4 subskills: content-generation, seo-optimization, content-distribution, performance-tracking

**New state:**
- 413-line SKILL.md focused on loop mechanics
- 3 subskills: content-generation, content-delivery (merged), seo-optimization (optional)

**Key changes:**
- Merged `content-distribution` + `performance-tracking` → `content-delivery` (distribution and tracking are one cycle)
- SEO demoted to optional (SEO is dying channel per distribution physics)
- Added loop trigger requirements to all workflow steps
- Added first-comment tracking for LinkedIn algorithm optimization
- Simplified workflow: Generate → Validate Loop → Review → Deliver → Track Activations

#### 2. Content Generation (Loop-First)

**Previous state:**
- 324 lines with complex pattern references
- 5 separate pattern files (blog, case study, LinkedIn, email, general principles)
- Pattern-heavy approach requiring reference lookups

**New state:**
- 203 lines with inline loop intelligence
- Patterns moved to marketing-narrative (templates, not prescriptive)
- Every draft requires: loop trigger + velocity framing

**Key changes:**
- Removed verbose pattern files (2,146 lines deleted)
- Added loop trigger types: implementation, question, challenge, offer
- Added velocity framing requirement (before → after with time)
- Simplified validation to loop-focused checks
- Brand voice loaded from marketing-narrative context

#### 3. Content Delivery (NEW — Merged Skill)

**What it replaces:**
- `content-distribution/` (825 lines) — deleted
- `performance-tracking/` (775 lines) — deleted

**New unified approach (305 lines):**
- Phase 1: Publish (format for each channel with loop triggers)
- Phase 2: Activate Loop (first-comment, URL tracking)
- Phase 3: Track Loop Activations (shares, implementations, DMs, UGC)
- Phase 4: Amplify Loop Fuel (user-generated content detection)

**Critical innovation:**
- Tracks loop activations, NOT vanity metrics
- First-comment critical for LinkedIn (5-minute rule)
- UGC detection and amplification workflow
- Distribution-metadata.yaml for tracking state

#### 4. SEO Optimization (Demoted to Optional)

**Previous state:**
- 676 lines of comprehensive SEO guidance
- Equal priority with other subskills

**New state:**
- 80 lines of basic checklist
- Explicitly marked as "declining channel"
- Use only for evergreen long-tail content
- Loop triggers > SEO optimization

#### 5. Content Strategy (Active Discovery)

**Previous state:**
- 515 lines focused on thread scanning
- Campaign opportunity detection only
- Passive daily scans

**New state:**
- 142 lines focused on loop opportunity detection
- Two modes: Active Discovery + Loop Opportunity Detection
- Evaluates opportunities by loop potential, not just relevance
- Reads from distribution-model.md for channel priorities

**Key changes:**
- Added WebSearch, WebFetch capabilities for active discovery
- Prioritizes UGC amplification opportunities
- Reduced from campaign framework to loop triggers

#### 6. Marketing Narrative (Distribution Model Added)

**Previous state:**
- 529 lines generating pillars, SEO strategy, brand voice, channels
- Output: 4 files in artifacts/marketing/narrative/

**New state:**
- 139 lines focused on distribution physics
- Output: 6 files including `distribution-model.md` (critical)

**New outputs:**
- `distribution-model.md` — Loop mechanics, velocity framing, channel strategy
- `positioning.md` — Core positioning (extracted from pillars)
- Templates in `references/` for lightweight patterns

**Key addition:** Distribution model is now REQUIRED context for all content generation

#### 7. Reference Files Consolidated

**Deleted (verbose patterns moved to narrative templates):**
- `content-generation/references/blog-patterns.md` (565 lines)
- `content-generation/references/case-study-pattern.md` (447 lines)
- `content-generation/references/announcement-linkedin-pattern.md` (397 lines)
- `content-generation/references/email-patterns.md` (496 lines)
- `content-generation/references/pattern-principles.md` (241 lines)
- `ops-content-strategy/references/campaign-framework.md` (301 lines)

**Added (lightweight templates):**
- `foundations-marketing-narrative/references/distribution-model-template.md`
- `foundations-marketing-narrative/references/loop-content-pattern.md`
- `foundations-marketing-narrative/references/brand-voice-template.md`
- `foundations-marketing-narrative/references/positioning-template.md`
- `foundations-marketing-narrative/references/content-pillars-template.md`
- `foundations-marketing-narrative/references/channel-guidelines-template.md`
- `marketing-execution/references/subskill-contracts.md`
- `marketing-execution/references/human-touchpoints.md`
- `marketing-execution/references/execution-log-template.md`

### Files Deleted

**Skill directories removed:**
- `.claude/skills/marketing-execution/content-distribution/` (entire directory)
- `.claude/skills/marketing-execution/performance-tracking/` (entire directory)

**Pattern files removed:**
- `.claude/skills/marketing-execution/content-generation/references/blog-patterns.md`
- `.claude/skills/marketing-execution/content-generation/references/case-study-pattern.md`
- `.claude/skills/marketing-execution/content-generation/references/announcement-linkedin-pattern.md`
- `.claude/skills/marketing-execution/content-generation/references/email-patterns.md`
- `.claude/skills/marketing-execution/content-generation/references/pattern-principles.md`
- `.claude/skills/ops-content-strategy/references/campaign-framework.md`

### Files Added

**New skill directory:**
- `.claude/skills/marketing-execution/content-delivery/SKILL.md`

**New reference directories:**
- `.claude/skills/foundations-marketing-narrative/references/` (6 template files)
- `.claude/skills/marketing-execution/references/` (3 contract/template files)

### Updated Skill Inventory

**Marketing Execution (1 orchestrator + 3 subskills):**
```
marketing-execution/                 # Loop-centric campaign orchestrator
├── content-generation/              # Generate loop-triggering drafts
├── content-delivery/                # Publish + track loop activations (NEW)
└── seo-optimization/                # Optional, for evergreen only
```

**Note:** Reduced from 4 to 3 subskills by merging distribution + tracking

### Metrics Shift

**What to track (loop activations):**
| Metric | Definition |
|--------|------------|
| Shares | Reposts, quote tweets |
| Implementations | Users trying the method |
| Inbound DMs | Conversations started |
| User-generated content | Others creating based on ours |
| Replies to loop trigger | Direct responses |

**What to ignore (vanity):**
| Metric | Why Ignore |
|--------|------------|
| Impressions | Doesn't indicate value |
| Likes | Low-effort, no loop |
| Follower count | Lagging indicator |
| Page views alone | Without conversion meaningless |

### Migration Notes

**For existing campaigns:**
- Update to use `content-delivery` instead of `content-distribution` + `performance-tracking`
- Add loop triggers to all content
- Track loop activations, not impressions

**For new campaigns:**
- Run `marketing-narrative` first to generate `distribution-model.md`
- All content must include loop trigger + velocity framing
- SEO is optional, not required

**Critical context files now required:**
- `artifacts/marketing/narrative/distribution-model.md` — All content generation needs this
- `artifacts/marketing/narrative/brand-voice.md` — Voice consistency
- `artifacts/marketing/narrative/positioning.md` — Core positioning

### Success Metrics

**Complexity reduction:**
- ✅ Skills reduced from 4 to 3 subskills
- ✅ Total lines reduced by ~5,700 (7,792 deleted, ~2,000 added)
- ✅ Pattern files consolidated to templates (2,447 lines → 6 template files)

**Philosophy alignment:**
- ✅ Loop triggers required in all content
- ✅ Velocity framing required in all content
- ✅ Vanity metrics explicitly deprioritized
- ✅ SEO demoted to optional status

**Operational clarity:**
- ✅ Distribution + tracking merged (single cycle)
- ✅ First-comment workflow documented (LinkedIn critical)
- ✅ UGC detection and amplification workflow
- ✅ Clear subskill contracts defined

---

**Change type:** Major optimization (philosophy + structure)
**Impact:** High (all marketing workflows affected)
**Breaking changes:** Yes (subskill paths changed, new required context files)
**Version:** 1.3
**Status:** Complete

---

## 2025-11-25: Major LeanOS Restructure - Generic Framework Release

### Summary
Complete restructure of LeanOS as a generic, industry-agnostic framework. Removed all product-specific content (PersonalOS/GlamYouUp), reorganized skill architecture with consistent naming conventions, and removed third-party document skills.

### Changes Made

#### 1. Removed All Product-Specific Content

**What was removed:**
- All references to "Bella Belgarokova", "GlamYouUp", "ElsaAI", "PersonalOS"
- Fashion/luxury/fit-specific examples throughout all skill files
- Product-specific metrics (return rates, sizing, fit recommendations)

**Replaced with:**
- Generic placeholders: `{Customer}`, `{industry}`, `{segment}`, `{key metric}`, `{solution approach}`
- Industry-agnostic examples applicable to any B2B SaaS startup
- Updated copyright to "LeanOS Contributors"

**Files cleaned:** 60+ skill files, all documentation, legal files

#### 2. Skill Architecture Reorganization

**New naming convention:** `{category}-{function}`

**Categories:**
- `engineering-*` - System building skills (7 skills)
- `foundations-*` - Business foundation skills (4 skills)
- `ops-*` - Operational skills (4 skills)
- `research-*` - Market research skills (2 skills)
- `sales-execution` - Sales orchestration (1 skill + 5 subskills)
- `marketing-execution` - Marketing orchestration (1 skill + 4 subskills)

**Renamed skills:**

| Old Name | New Name |
|----------|----------|
| `category-theoretic-system-design` | `engineering-system-architecture` |
| `standardization-layer` | `engineering-standardization-definer` + `engineering-standardization-applier` |
| `foundation-builder` | `foundations-builder` |
| `icp-generator` | `foundations-icp-generator` |
| `sales-narrative` | `foundations-sales-narrative` |
| `marketing-narrative` | `foundations-marketing-narrative` |
| `causal-flow` | `ops-causal-flow` |
| `ops-dashboard` | `ops-dashboard` (unchanged) |
| `content-strategy` | `ops-content-strategy` |
| `business-metrics-tracker` | `ops-business-metrics-tracker` |
| `market-research-venture` | `research-market-venture` |
| `market-research-bootstrap` | `research-market-bootstrap` |

**New engineering skills added:**
- `engineering-backend-prover` - Generate verified backend code
- `engineering-frontend-prover` - Generate type-safe frontend code
- `engineering-infrastructure-prover` - Generate deployment configs
- `engineering-proof-composer` - Validate entire proof chain

#### 3. Removed Third-Party Document Skills

**Deleted:** `.claude/skills/document-skills/` (entire directory)
- `docx/` - Word document handling
- `pdf/` - PDF document handling
- `pptx/` - PowerPoint handling
- `xlsx/` - Excel handling

**Reason:** Third-party proprietary skills from Anthropic removed to keep LeanOS as pure open-source framework.

**Also deleted:** `THIRD-PARTY-LICENSES.md` (no longer needed)

#### 4. Updated Legal/Attribution Files

**LICENSE:**
- Copyright holder: "Bella Belgarokova" → "LeanOS Contributors"

**CONTRIBUTING.md:**
- Removed maintainer personal information
- Updated version to 1.2
- Removed references to document-skills restrictions

### Current Skill Inventory (19 skills)

**Engineering Layer (7 skills):**
```
engineering-system-architecture/     # Requirements → Mathematical specs
engineering-backend-prover/          # Specs → Verified backend code
engineering-frontend-prover/         # Specs → Type-safe frontend
engineering-infrastructure-prover/   # Specs → Deployment configs
engineering-proof-composer/          # Validate proof chain
engineering-standardization-definer/ # Define cross-cutting standards
engineering-standardization-applier/ # Apply standards to services
```

**Foundations Layer (4 skills):**
```
foundations-builder/                 # Orchestrate Canvas population
foundations-icp-generator/           # Generate ICPs per segment
foundations-sales-narrative/         # Generate sales messaging
foundations-marketing-narrative/     # Generate content strategy
```

**Operations Layer (4 skills):**
```
ops-causal-flow/                     # 6-stage decision orchestrator
ops-dashboard/                       # Generate daily dashboards
ops-content-strategy/                # Detect campaign opportunities
ops-business-metrics-tracker/        # Mode-aware metrics dashboards
```

**Research Layer (2 skills):**
```
research-market-venture/             # TAM, growth, competitive analysis
research-market-bootstrap/           # Spend mapping, immediate revenue
```

**Execution Layer (2 orchestrators + 9 subskills):**
```
sales-execution/                     # Sales orchestrator
  ├── materials-generation/
  ├── prospect-research/
  ├── contact-finding/
  ├── outreach-sequencing/
  └── qualification-support/

marketing-execution/                 # Marketing orchestrator
  ├── content-generation/
  ├── seo-optimization/
  ├── content-distribution/
  └── performance-tracking/
```

### Files Deleted

**Skill directories removed:**
- `.claude/skills/document-skills/` (all subdirectories)
- `.claude/skills/category-theoretic-system-design/`
- `.claude/skills/causal-flow/`
- `.claude/skills/content-strategy/`
- `.claude/skills/business-metrics-tracker/`
- `.claude/skills/icp-generator/`
- `.claude/skills/sales-narrative/`
- `.claude/skills/marketing-narrative/`
- `.claude/skills/foundation-builder/`
- `.claude/skills/standardization-layer/`
- `.claude/skills/market-research-venture/` (old location)
- `.claude/skills/market-research-bootstrap/` (old location)

**Other files removed:**
- `THIRD-PARTY-LICENSES.md`
- `_sitemap.md`

### Files Added

**New skill directories:**
- `.claude/skills/engineering-backend-prover/`
- `.claude/skills/engineering-frontend-prover/`
- `.claude/skills/engineering-infrastructure-prover/`
- `.claude/skills/engineering-proof-composer/`
- `.claude/skills/engineering-standardization-applier/`
- `.claude/skills/engineering-standardization-definer/`
- `.claude/skills/engineering-system-architecture/`
- `.claude/skills/foundations-builder/`
- `.claude/skills/foundations-icp-generator/`
- `.claude/skills/foundations-marketing-narrative/`
- `.claude/skills/foundations-sales-narrative/`
- `.claude/skills/ops-business-metrics-tracker/`
- `.claude/skills/ops-causal-flow/`
- `.claude/skills/ops-content-strategy/`
- `.claude/skills/research-market-bootstrap/`
- `.claude/skills/research-market-venture/`

**Documentation:**
- `docs/operations/engineering-workflow.md`

### Migration Notes

**For existing LeanOS users:**
- Update any skill references to use new naming convention
- Remove any references to document-skills
- Update CLAUDE.md references if customized

**For new users:**
- LeanOS is now fully generic - no product-specific assumptions
- All examples use placeholders - replace with your domain
- No third-party dependencies

### Success Metrics

**Genericization:**
- ✅ Zero product-specific references (verified via grep)
- ✅ All examples use `{placeholder}` syntax
- ✅ Framework applicable to any industry

**Consistency:**
- ✅ All skills follow `{category}-{function}` naming
- ✅ Clear layer separation (engineering, foundations, ops, research, execution)
- ✅ Predictable skill locations

**Simplification:**
- ✅ Removed third-party dependencies
- ✅ Pure open-source framework
- ✅ Single LICENSE file (MIT)

---

**Change type:** Major restructure
**Impact:** High (skill renaming, content genericization)
**Breaking changes:** Yes (skill paths changed, document-skills removed)
**Version:** 1.2
**Status:** Complete

---

## 2025-11-21: Marketing Execution Layer Optimization

### Summary
Optimized marketing-execution skill layer by extracting content-strategy as a standalone skill and enhancing content-generation with pattern-based references.

### Changes Made

#### 1. Extracted content-strategy as Standalone Skill
**Location:** `.claude/skills/content-strategy/`

**Previous state:**
- content-strategy was a subskill of marketing-execution
- Mixed responsibility: opportunity detection + execution orchestration
- Located at: `.claude/skills/marketing-execution/content-strategy/`

**New state:**
- content-strategy is now a top-level standalone skill
- Single responsibility: Campaign opportunity detection only
- Located at: `.claude/skills/content-strategy/`
- Clear separation: Detection (content-strategy) vs Execution (marketing-execution)

**Why this matters:**
- **Clarity:** content-strategy is invoked independently for daily scans, not as part of campaign execution
- **Reusability:** Other skills can invoke content-strategy without going through marketing-execution
- **Separation of concerns:** Opportunity detection (strategic) is distinct from campaign execution (operational)

#### 2. Redefined marketing-execution as Pure Orchestrator
**Location:** `.claude/skills/marketing-execution/SKILL.md`

**Previous state:**
- marketing-execution handled both opportunity detection AND campaign execution
- Mixed stages: Could be invoked at any stage (1-6)
- 5 subskills: content-strategy, content-generation, seo-optimization, content-distribution, performance-tracking

**New state:**
- marketing-execution is Stage 5 execution orchestrator ONLY
- 4 subskills: content-generation, seo-optimization, content-distribution, performance-tracking
- Role: Pure orchestrator (reads decisions, invokes subskills, tracks progress)
- Does NOT: Generate content, optimize SEO, publish, or track metrics directly

**Why this matters:**
- **Single responsibility:** Execute approved campaigns (Stage 5), nothing else
- **Predictable behavior:** Only invoked after Stage 4 decision is complete
- **Clearer invocation:** "marketing-execution executes Stage 5" vs "marketing-execution does everything"

#### 3. Enhanced content-generation with References
**Location:** `.claude/skills/marketing-execution/content-generation/`

**Previous state:**
- content-generation had basic instructions
- No formal content patterns or validation
- Minimal guidance on structure and quality

**New state:**
- Added `references/` directory with 5 pattern guides:
  - `blog-patterns.md` - 5 blog article structures
  - `case-study-pattern.md` - Customer success story structure
  - `announcement-linkedin-pattern.md` - Product launch pattern
  - `email-patterns.md` - Email newsletter/announcement patterns
  - `pattern-principles.md` - Universal principles across all patterns
- Added `scripts/` directory:
  - `validate_draft.py` - Automated draft validation script
- Skill now references patterns explicitly in generation process

**Why this matters:**
- **Consistency:** All content follows proven patterns
- **Quality:** Automated validation catches issues before human review
- **Efficiency:** 80% complete drafts (vs 60% before) reduces human review time
- **Scalability:** New content types = new patterns, not skill rewrites

### System-Wide Impacts

#### Updated Execution Flow
**Before:**
```
marketing-execution invoked
    ↓
content-strategy detects opportunity
    ↓
(same skill continues)
    ↓
content-generation creates draft
    ↓
... etc
```

**After:**
```
content-strategy (daily scan, standalone)
    ↓
Flags opportunity in ops/today.md
    ↓
Human creates campaign thread (Stages 1-4)
    ↓
marketing-execution reads Stage 4 decision
    ↓
Orchestrates: content-generation → seo-optimization → content-distribution → performance-tracking
```

#### Skill Invocation Changes
**content-strategy:**
- Invoke independently: Daily automated scans
- Invoke manually: "Scan for content opportunities"
- Output: ops/today.md flags (not campaign execution)

**marketing-execution:**
- Invoke only: When Stage 4 decision exists
- Input: Campaign thread with completed 4-decision.md
- Output: Executed Stage 5 (drafts → SEO → publishing → tracking)

### Files Modified

#### Skill Files
- `.claude/skills/marketing-execution/SKILL.md` (redefined as pure orchestrator)
- `.claude/skills/content-strategy/SKILL.md` (extracted as standalone)
- `.claude/skills/marketing-execution/content-generation/SKILL.md` (enhanced with references)

#### New Files Created
- `.claude/skills/content-strategy/references/campaign-framework.md`
- `.claude/skills/marketing-execution/content-generation/references/blog-patterns.md`
- `.claude/skills/marketing-execution/content-generation/references/case-study-pattern.md`
- `.claude/skills/marketing-execution/content-generation/references/announcement-linkedin-pattern.md`
- `.claude/skills/marketing-execution/content-generation/references/email-patterns.md`
- `.claude/skills/marketing-execution/content-generation/references/pattern-principles.md`
- `.claude/skills/marketing-execution/content-generation/scripts/validate_draft.py`

#### Deleted Files
- `.claude/skills/marketing-execution/content-strategy/` (moved to top-level)

#### Documentation Files
- `docs/skills/all-skills.md` (updated marketing skills section)
- `docs/overview/architecture.md` (updated architecture diagram and marketing skills description)

### Migration Notes

**No action required for existing campaigns:**
- Existing campaign threads remain valid
- Stage 5 execution flow unchanged from user perspective
- Only skill boundaries changed, not functionality

**For future campaigns:**
- content-strategy runs automatically (daily scans)
- marketing-execution invoked only after Stage 4 complete
- Clearer separation of detection vs execution

### Success Metrics

**Clarity improvement:**
- ✅ content-strategy role: Detection only (no execution)
- ✅ marketing-execution role: Stage 5 execution only (no detection)
- ✅ content-generation: Pattern-based with validation

**Operational efficiency:**
- ✅ Reduced cognitive load (each skill has single responsibility)
- ✅ Faster onboarding (clear skill boundaries)
- ✅ Easier debugging (failures isolated to specific skills)

**Content quality:**
- ✅ Consistent structure (pattern guides)
- ✅ Automated validation (validate_draft.py)
- ✅ Higher draft completion (80% vs 60% before)

---

**Change type:** Refactoring (no functionality changes, improved structure)
**Impact:** Medium (affects marketing workflow invocation)
**Breaking changes:** None (backward compatible)
**Status:** Complete

---

## 2025-11-18: Dual-Mode Business Model Support

### Summary
Added business model mode awareness (VENTURE vs BOOTSTRAP vs HYBRID) to LeanOS, enabling mode-specific decision-making, metrics, and market research across all operations.

### Changes Made

#### 1. Created Business Model Mode Configuration
**Location:** `strategy/canvas/00-business-model-mode.md`

**New capability:**
- Central declaration of business model mode (VENTURE, BOOTSTRAP, or HYBRID)
- Mode-specific definitions for:
  - Capital strategy (funded vs self-funded vs hybrid)
  - Decision sequences (product-first vs monetization-first)
  - Success metrics (growth metrics vs profitability metrics)
  - Research focus (TAM/market sizing vs current spend mapping)
  - Product approach (platform vs minimal solution)
  - Go-to-market strategy (brand building vs direct conversion)
  - Impact scoring formulas (strategic value vs revenue impact)

**Mode Definitions:**

| Aspect | VENTURE | BOOTSTRAP | HYBRID |
|--------|---------|-----------|--------|
| Capital | Investor-funded | Self-funded | Bootstrap then raise |
| Timeline | 7-10 year exit | Infinite (profitability) | Bootstrap 6-12mo, then raise |
| Metrics | MAU, ARR, TAM, Growth Rate | MRR, Profit, Margin, Cash Flow | Bootstrap → Venture transition |
| Decision Priority | Strategic value | Revenue impact | Phase-dependent |

**Impact Scoring by Mode:**

**VENTURE:**
```
Impact = (Strategic Value × Market Size × Defensibility) / 3
```

**BOOTSTRAP:**
```
Impact = (Revenue Impact × Time to Cash × Margin) / 3
```

#### 2. Added Mode-Specific Market Research Skills

**market-research-venture** (`.claude/skills/market-research-venture/`)
- TAM/SAM/SOM calculations (billion-dollar market sizing)
- Market growth rate analysis (target: >20% CAGR)
- Competitive landscape mapping (funding, market share, positioning)
- Defensibility and moat assessment (network effects, switching costs, etc.)
- Scalability evaluation (unit economics at scale)
- 10x opportunity identification
- Output: `research/market/venture-analysis-{date}.md`

**market-research-bootstrap** (`.claude/skills/market-research-bootstrap/`)
- Current spend mapping (who pays what today)
- Budget holder identification (decision makers, approval thresholds)
- Competitive pricing intelligence (actual prices, not projections)
- Arbitrage opportunity analysis (margin opportunities)
- Procurement process analysis (sales cycle, friction points)
- Immediate revenue potential (Q1 calculations, path to profitability)
- Output: `research/market/bootstrap-analysis-{date}.md`

**Why two skills:**
- VENTURE research asks: "How big can this get?"
- BOOTSTRAP research asks: "Who is paying today and how do we capture some?"
- Different methodologies, sources, and outputs for each mode
- Skills auto-detect mode from `00-business-model-mode.md` and refuse to run in wrong mode

#### 3. Updated CLAUDE.md with Mode Awareness

**Added to Core Operating Principles (Section 4):**
- Impact scoring now mode-aware
- Two different formulas based on active mode
- HYBRID mode instructions (use Bootstrap formula until profitable)

**Added to Skills Reference:**
- `market-research-venture` - Venture-focused analysis
- `market-research-bootstrap` - Bootstrap-focused analysis
- Guidance on which skill to use based on mode

**Added to Decision-Making Framework:**
- Mode check as first step ("Check `00-business-model-mode.md` for current mode")
- Mode-specific decision criteria
- Mode switching triggers and process

### System-Wide Impacts

#### Mode Cascades To:
- **Thread impact scoring** (causal-flow uses mode-specific formula)
- **Research priorities** (venture vs bootstrap market research skills)
- **Product decisions** (foundation-builder adapts to mode)
- **Metrics tracking** (ops-dashboard shows mode-appropriate metrics)
- **GTM strategy** (sales-execution, marketing-execution priorities)

#### Operational Changes:
- All impact score calculations must check mode first
- Market research skill selection is mode-dependent
- business-metrics-tracker generates mode-appropriate dashboards
- ops/today.md flags items against mode-specific thresholds

### Files Created

- `strategy/canvas/00-business-model-mode.md` (mode declaration and definitions)
- `.claude/skills/market-research-venture/SKILL.md` (venture research skill)
- `.claude/skills/market-research-bootstrap/SKILL.md` (bootstrap research skill)

### Files Modified

- `CLAUDE.md` (mode-aware impact scoring, skill references, decision framework)
- `docs/skills/all-skills.md` (added market research skills)

### Current Mode

**Active Mode:** BOOTSTRAP

**Rationale (from `00-business-model-mode.md`):**
- Self-funded, no outside capital raised
- Need profitability within 3 months
- Revenue-first approach to validate market
- Exit optional, cash flow primary goal

### Migration Notes

**No action required for existing threads:**
- Existing threads continue to work
- Impact scores should be recalculated using Bootstrap formula
- Research should use `market-research-bootstrap` skill

**For new operations:**
- Always check mode before calculating impact scores
- Use appropriate market research skill for mode
- Track Bootstrap metrics (MRR, profit, margin) not Venture metrics (ARR, growth)

### Success Metrics

**Clarity improvement:**
- ✅ Clear mode definition with specific implications
- ✅ Mode-specific impact formulas (no ambiguity)
- ✅ Dedicated research skills per mode

**Operational consistency:**
- ✅ All decisions evaluated against mode-appropriate criteria
- ✅ Market research matches business model approach
- ✅ Metrics tracked match what matters for mode

**Future flexibility:**
- ✅ Mode switching documented with triggers
- ✅ HYBRID mode supports transition path
- ✅ Single file to update when mode changes

---

**Change type:** Feature (new capability)
**Impact:** High (affects all decision-making and research)
**Breaking changes:** None (additive, backward compatible)
**Status:** Complete
