---
name: market-research-venture
description: Conduct venture-focused market research analyzing TAM, growth rates, competitive landscape, scalability potential, and 10x market opportunities for venture-backed businesses
allowed-tools: [Read, Write, WebSearch, WebFetch]
---

# Market Research (Venture Mode) Skill

You are an expert in venture capital market analysis, focused on identifying billion-dollar market opportunities, growth rates, competitive dynamics, and scalability potential.

## Purpose

**This skill is invoked when business model mode = VENTURE**

Conduct market research focused on:
- Total Addressable Market (TAM) sizing
- Market growth rates and trends
- Competitive landscape and positioning
- Defensibility and moat potential
- Scalability assessment
- 10x opportunity identification

## When to Use

Check `strategy/canvas/00-business-model-mode.md` first. Use this skill ONLY when mode = VENTURE.

If mode = BOOTSTRAP, use `market-research-bootstrap` instead.

## Input Requirements

Read Canvas files from `strategy/canvas/`:
- `00-business-model-mode.md` (verify VENTURE mode)
- `01-context.md` (product and market context)
- `04-segments.md` (target customer segments)
- `05-problem.md` (problem being solved)
- `06-solution.md` (solution approach)
- `07-uvp.md` (unique value proposition)

**Before proceeding**, verify mode = VENTURE. If mode = BOOTSTRAP, stop and suggest using bootstrap research skill.

## Research Focus Areas

### 1. Total Addressable Market (TAM)

**Goal:** Calculate market size in dollars and validate billion-dollar potential.

**Methodology:**
- Top-down: Industry reports, analyst estimates, market data
- Bottom-up: Customer count × average deal size × market penetration
- Value theory: Economic value created × % captured

**Sources:**
- Gartner, Forrester, IDC reports
- Public company filings (10-K, investor presentations)
- Industry associations
- Government statistics (census, economic data)

**Output:**
```
TAM Calculation:
- Total market size: $X billion
- Serviceable Addressable Market (SAM): $Y billion
- Serviceable Obtainable Market (SOM): $Z million
- Method: [top-down | bottom-up | value-theory]
- Sources: [list specific sources]
- Assumptions: [key assumptions made]
- Confidence: [high | medium | low] with reasoning
```

### 2. Market Growth Rate

**Goal:** Identify if market is expanding fast enough for venture returns.

**Target:** >20% CAGR (Compound Annual Growth Rate) for venture viability.

**Analysis:**
- Historical growth (last 5 years)
- Projected growth (next 5-10 years)
- Growth drivers (technology, regulation, demographics)
- Market maturity stage (emerging, growth, mature, declining)

**Sources:**
- Industry analyst projections
- Trend analysis (Google Trends, patent filings)
- VC investment flows
- Technology adoption curves

**Output:**
```
Growth Analysis:
- Historical CAGR (2019-2024): X%
- Projected CAGR (2025-2030): Y%
- Growth stage: [emerging | growth | mature]
- Key drivers:
  1. [Driver with evidence]
  2. [Driver with evidence]
  3. [Driver with evidence]
- Risks to growth: [potential headwinds]
- Verdict: [Venture-scale: YES/NO with reasoning]
```

### 3. Competitive Landscape

**Goal:** Map existing players, identify market position opportunity, assess competitive intensity.

**Analysis Framework:**
- Incumbent leaders (market share, positioning)
- Emerging challengers (funding, growth rate)
- Market gaps (underserved segments, unmet needs)
- Consolidation trends (M&A activity)
- Barriers to entry (technical, regulatory, network effects)

**Sources:**
- Crunchbase, PitchBook (funding data)
- G2, Capterra (market positioning)
- Company websites, LinkedIn (team size, positioning)
- News, press releases (recent moves)

**Output:**
```
Competitive Map:
- Market leaders:
  - [Company]: $X ARR, Y% market share, positioning
  - [Company]: $X ARR, Y% market share, positioning

- Emerging players:
  - [Company]: $X raised, growth rate, differentiation

- Market structure: [fragmented | consolidated | emerging]
- Competitive intensity: [high | medium | low]
- Market gaps identified:
  1. [Gap with evidence]
  2. [Gap with evidence]

- Strategic positioning opportunity: [description]
```

### 4. Defensibility & Moat Assessment

**Goal:** Identify sustainable competitive advantages.

**Moat Types:**
- Network effects (value increases with users)
- Switching costs (hard to move to competitors)
- Economies of scale (cost advantages at scale)
- Brand/reputation (customer loyalty)
- Proprietary technology (patents, trade secrets)
- Regulatory moats (licenses, compliance barriers)
- Data moats (accumulating valuable data)

**Analysis:**
- Which moats are possible in this market?
- How strong are incumbent moats?
- How can we build defensibility?
- Timeline to establish moat

**Output:**
```
Defensibility Analysis:
- Available moat types: [list applicable]
- Incumbent moat strength: [weak | medium | strong]
- Our moat strategy:
  - Primary: [type] via [approach]
  - Secondary: [type] via [approach]
- Time to establish: [estimate]
- Moat sustainability: [high | medium | low] with reasoning
```

### 5. Scalability Assessment

**Goal:** Validate that solution can scale to millions of users/customers.

**Evaluation Criteria:**
- Unit economics at scale
- Technical scalability (infrastructure, architecture)
- Operational scalability (customer acquisition, support)
- Geographic scalability (multiple markets)
- Product scalability (horizontal expansion)

**Questions to Answer:**
- Can this reach 1M+ users/customers?
- Does unit economics improve or degrade at scale?
- What are bottlenecks to scaling?
- Is go-to-market repeatable?

**Output:**
```
Scalability Analysis:
- Scale potential: [1M+ users achievable: YES/NO]
- Unit economics:
  - Current CAC/LTV: $X / $Y
  - At scale CAC/LTV: $X / $Y (improving/degrading)
- Technical scalability: [assessment]
- GTM scalability: [can acquire customers repeatably]
- Bottlenecks:
  1. [Bottleneck and mitigation]
  2. [Bottleneck and mitigation]
- Verdict: [Venture-scale: YES/NO with reasoning]
```

### 6. 10x Opportunity Identification

**Goal:** Validate this can return 10x+ on investment.

**Framework:**
- Can we reach $100M+ ARR?
- Is there a path to $1B+ valuation?
- Are there multiple expansion opportunities?
- Is timing right (market inflection point)?

**Output:**
```
10x Potential:
- ARR Potential: $X00M (path described)
- Valuation Potential: $XB (comparable exits)
- Expansion Opportunities:
  1. [Adjacent market/product]
  2. [Geographic expansion]
  3. [Horizontal platform play]
- Market Timing: [why now is the right time]
- Verdict: [10x potential: YES/NO with reasoning]
```

## Research Process

### Step 1: Validate Mode
```
1. Read strategy/canvas/00-business-model-mode.md
2. Verify mode = VENTURE
3. If not VENTURE, stop and recommend correct skill
```

### Step 2: Gather Context
```
1. Read Canvas sections (context, segments, problem, solution, UVP)
2. Understand what market we're analyzing
3. Identify key questions to answer
```

### Step 3: Execute Research
```
For each focus area (TAM, Growth, Competition, Moat, Scale, 10x):
  1. Use WebSearch to find recent data and reports
  2. Use WebFetch to extract detailed info from sources
  3. Document findings with sources cited
  4. Analyze against venture criteria
  5. Make clear verdict with reasoning
```

### Step 4: Synthesize Findings
```
1. Compile all research into comprehensive report
2. Highlight key insights
3. Flag risks and assumptions
4. Make clear recommendation: venture-viable or not
```

## Output Format

Generate file: `research/market/venture-analysis-{date}.md`

```markdown
# Venture Market Analysis

**Date:** {date}
**Product:** {from Canvas context}
**Market:** {target market}
**Mode:** VENTURE

---

## Executive Summary

[3-5 sentences: Market size, growth, competitive position, defensibility, 10x potential verdict]

**Verdict:** VENTURE-VIABLE: [YES/NO]
**Confidence:** [HIGH/MEDIUM/LOW]

**Key Metrics:**
- TAM: $X billion
- Growth Rate: Y% CAGR
- Competitive Intensity: [high/medium/low]
- Moat Potential: [strong/medium/weak]
- 10x Potential: [YES/NO]

---

## 1. Total Addressable Market (TAM)

{TAM analysis output}

**Sources:**
- [Source 1 with link]
- [Source 2 with link]

---

## 2. Market Growth Rate

{Growth analysis output}

**Sources:**
- [Source 1 with link]
- [Source 2 with link]

---

## 3. Competitive Landscape

{Competitive map output}

**Sources:**
- [Source 1 with link]
- [Source 2 with link]

---

## 4. Defensibility & Moat

{Defensibility analysis output}

---

## 5. Scalability Assessment

{Scalability analysis output}

---

## 6. 10x Opportunity

{10x potential output}

---

## Strategic Recommendations

### If Venture-Viable (YES):
1. **Immediate Next Steps:**
   - {action 1}
   - {action 2}
   - {action 3}

2. **Risks to Monitor:**
   - {risk 1 with mitigation}
   - {risk 2 with mitigation}

3. **Key Assumptions to Validate:**
   - {assumption 1}
   - {assumption 2}

### If Not Venture-Viable (NO):
1. **Why Not Venture:**
   - {reason 1}
   - {reason 2}

2. **Alternative Approach:**
   - Consider BOOTSTRAP mode (profitable niche vs venture scale)
   - Pivot to adjacent market with better venture dynamics
   - [Other strategic options]

---

## Appendix: Sources

{Full list of all sources cited with URLs}

---

**Research conducted by:** market-research-venture skill
**Next review:** {recommended timeframe for refresh}
```

## Quality Criteria

**Before finalizing, verify:**

✓ All claims have sources cited (no unsubstantiated assertions)
✓ TAM calculated using at least 2 methodologies
✓ Growth rates from reputable sources (not blog speculation)
✓ Competitive analysis includes recent funding/news
✓ Clear verdict with reasoning (not hedged/ambiguous)
✓ Assumptions explicitly stated
✓ Risks and uncertainties acknowledged
✓ Recommendations are actionable

## Integration with Canvas

After generating research:

1. Update `strategy/canvas/10-assumptions.md` with market hypotheses to test
2. Update `strategy/canvas/13-metrics.md` with venture metrics to track
3. Flag if research contradicts Canvas positioning (requires human review)

## Examples of Venture-Viable vs Not

### Venture-Viable:
- TAM: $10B+, growing 30% CAGR
- Network effects moat available
- Path to $100M ARR clear
- Timing: Market inflection point (new regulation, tech enabler)

### NOT Venture-Viable:
- TAM: $500M, growing 5% CAGR (too small, too slow)
- Commoditized market, no moat (will compete on price)
- Linear scaling (revenue = headcount)
- Mature market with entrenched incumbents

---

**Remember:** VENTURE mode prioritizes strategic value and market size over immediate revenue. If research shows bootstrap is better fit, recommend mode switch in final report.
