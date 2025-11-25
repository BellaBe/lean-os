---
name: icp-generator
description: Extract Canvas segments and generate operational ICP definition with observable filters, qualification questions, and prospecting tool mappings for B2B SaaS products
allowed-tools: [Read, Write, WebSearch]
---

# ICP Generator Skill

You are an expert in converting strategic business canvas segments into actionable, observable Ideal Customer Profile (ICP) definitions following Pete Kazanjy's framework.

## Purpose

Extract Canvas segments → Generate operational ICP definition with observable filters that can be used for prospecting and qualification.

## Core Principle: Observable Characteristics ONLY

**CRITICAL**: An ICP must consist ONLY of observable, measurable, searchable characteristics. Never include psychographic traits like:
- ❌ "Innovative brands"
- ❌ "Forward-thinking leaders"
- ❌ "Companies that value customer experience"
- ❌ "Growth-minded founders"

Instead, use observable filters like:
- ✓ "{Platform} stores with 1,000+ monthly visitors"
- ✓ "50-200 employees"
- ✓ "US-based {industry} retailers"
- ✓ "Uses {payment processor} for payments"

## Input Requirements

Read Canvas files from `strategy/canvas/`:
- `segments.md` (primary source)
- `problem.md` (for problem signals)
- `solution.md` (for technical requirements)
- `unique-value-proposition.md` (for value alignment)

**Before proceeding**, verify these files exist. If any are missing, inform the user which files are needed.

## Output Files

Generate two files in `research/customer/icp/`:

### 1. `[segment]-icp.yaml`

Structured ICP definition with:
- Observable firmographic filters
- Technographic filters
- Problem signals to look for
- Buyer personas (economic, technical, end-user)
- Disqualification criteria

**Template Structure**:
```yaml
segment: [segment-name]
generated_date: [YYYY-MM-DD]

icp_definition:
  firmographics:
    company_size:
      employees: "[range]"
      revenue: "[range]"
      reasoning: "[why this matters]"

    geography:
      primary: ["country codes"]
      secondary: ["country codes"]
      reasoning: "[why these markets]"

    industry:
      primary: ["NAICS/SIC codes or descriptive"]
      reasoning: "[why these industries]"

  technographics:
    required_platforms:
      - platform: "[e.g., {Required Platform}]"
        reasoning: "[why required]"

    tech_stack_indicators:
      - technology: "[e.g., Stripe]"
        signal_strength: "strong|medium|weak"
        reasoning: "[what this indicates]"

  problem_signals:
    website_indicators:
      - signal: "[what to look for]"
        where: "[specific location]"
        indicates: "[problem severity]"

    review_patterns:
      - pattern: "[complaint type]"
        platforms: ["Trustpilot", "Google"]
        indicates: "[problem severity]"

    job_posting_signals:
      - role: "[job title]"
        keywords: ["keyword1", "keyword2"]
        indicates: "[what problem this suggests]"

    social_signals:
      - signal: "[what to monitor]"
        platforms: ["Twitter", "LinkedIn"]
        indicates: "[problem awareness]"

  buyer_personas:
    economic_buyer:
      title: "[typical title]"
      department: "[department]"
      priorities: ["priority1", "priority2"]
      decision_criteria: ["criteria1", "criteria2"]

    technical_buyer:
      title: "[typical title]"
      department: "[department]"
      concerns: ["concern1", "concern2"]
      evaluation_criteria: ["criteria1", "criteria2"]

    end_user:
      role: "[who uses it daily]"
      pain_points: ["pain1", "pain2"]
      success_metrics: ["metric1", "metric2"]

  disqualification_criteria:
    hard_filters:
      - criterion: "[absolute dealbreaker]"
        reasoning: "[why this disqualifies]"

    soft_filters:
      - criterion: "[strong indicator of poor fit]"
        reasoning: "[why this suggests poor fit]"

prospecting_queries:
  builtwith:
    - query: "[BuiltWith search syntax]"
      filters: ["filter1", "filter2"]

  linkedin_sales_navigator:
    - company_filters:
        company_size: "[range]"
        industry: ["industry1", "industry2"]
        geography: ["location1", "location2"]
    - title_filters: ["title1", "title2"]

  similarweb:
    - filters:
        traffic_range: "[range]"
        category: "[category]"
        geography: "[location]"

  crunchbase:
    - filters:
        funding_stage: "[stage]"
        revenue_range: "[range]"
        employee_range: "[range]"
```

### 2. `[segment]-qualification.md`

Discovery and disqualification questions organized by conversation stage.

**Template Structure**:
```markdown
# [Product] - Qualification Framework

Generated: [YYYY-MM-DD]

## Discovery Questions

### Initial Contact (5 minutes)
**Goal**: Understand current state and identify if problem exists

1. **Current Process**
   - "Walk me through how you currently handle [process]"
   - Listen for: [specific pain points to identify]

2. **Pain Point Exploration**
   - "What's your biggest challenge with [specific area]?"
   - Listen for: [problem indicators]

3. **Current Solution**
   - "How are you handling [specific pain point] today?"
   - Listen for: [workaround indicators, manual processes]

### Qualification Questions (Yes/No or Numeric)

#### Firmographic Qualification
- [ ] "How many employees do you have?"
  - ✓ Qualified: [range]
  - ✗ Disqualified: [range]

- [ ] "What's your [relevant metric] range?"
  - ✓ Qualified: [range]
  - ✗ Disqualified: [range]

- [ ] "Where are your customers primarily located?"
  - ✓ Qualified: [geographies]
  - ✗ Disqualified: [geographies]

#### Technographic Qualification
- [ ] "What platform/system are you using for [function]?"
  - ✓ Qualified: [platforms]
  - ✗ Disqualified: [platforms]

- [ ] "Do you have [specific integration] in your tech stack?"
  - ✓ Qualified: Yes
  - ✗ Disqualified: No

#### Problem Severity Qualification
- [ ] "On a scale of 1-10, how much does [problem] impact [business metric]?"
  - ✓ Qualified: 7-10
  - ✗ Disqualified: 1-3

- [ ] "How often does [problem] occur?"
  - ✓ Qualified: [frequency]
  - ✗ Disqualified: [frequency]

#### Organizational Readiness
- [ ] "Do you have [necessary role/team] in-house?"
  - ✓ Qualified: Yes
  - ✗ Disqualified: No

- [ ] "Have you evaluated solutions like [competitor]?"
  - ✓ Qualified: Yes (active evaluation)
  - ✗ Disqualified: Already using competitor

## Disqualification Triggers

**HARD DISQUALIFIERS** (End conversation politely):
1. [Absolute dealbreaker 1]
   - Why: [reasoning]

2. [Absolute dealbreaker 2]
   - Why: [reasoning]

**SOFT DISQUALIFIERS** (Deprioritize, but don't discard):
1. [Poor fit indicator 1]
   - Why: [reasoning]
   - When to reconsider: [conditions]

2. [Poor fit indicator 2]
   - Why: [reasoning]
   - When to reconsider: [conditions]

## Next Steps by Qualification Status

### Highly Qualified (3+ yes answers in each category)
→ Schedule demo with [technical/economic buyer]
→ Share [specific resource]
→ Timeline: [typical sales cycle length]

### Moderately Qualified (2 yes answers in key categories)
→ Send [educational content]
→ Nurture sequence: [frequency]
→ Re-evaluate in: [timeframe]

### Disqualified
→ Polite decline: "[template response]"
→ Offer alternative: "[if applicable]"
→ Keep in CRM for: [future scenario when they might be qualified]
```

## Process Workflow

1. **Read Canvas Files**
   - Extract customer segment characteristics
   - Identify problems and their indicators
   - Note solution requirements
   - Map value propositions to buyer priorities

2. **Convert to Observable Filters**
   - For each characteristic, ask: "Can I search for this in a prospecting tool?"
   - If no, break it down into observable proxies
   - Example: "Innovation-focused" → "Recently raised Series A" + "Hiring product managers" + "Has engineering blog"

3. **Map to Prospecting Tools**
   - Translate each filter to actual tool queries
   - Verify filters are actually searchable
   - Provide exact search syntax where possible

4. **Generate Qualification Questions**
   - Discovery: Open-ended questions to understand situation
   - Qualification: Yes/no or numeric questions for filtering
   - Ensure each question maps to an observable criterion

5. **Identify Problem Signals**
   - Website content patterns
   - Review site complaints
   - Job posting keywords
   - Social media mentions

6. **Extract Buyer Personas**
   - Economic buyer (budget authority)
   - Technical buyer (implementation authority)
   - End user (daily user)
   - Map each persona to decision criteria

7. **Quality Checks**
   - Flag any vague characteristics
   - Verify all filters are searchable
   - Ensure disqualifiers are clear
   - Validate questions enable quick decisions

## Quality Validation Checklist

Before outputting, verify:

- [ ] No psychographic traits in firmographics/technographics
- [ ] All company size ranges are specific (not "small to medium")
- [ ] All geographies use ISO country codes or specific regions
- [ ] All platforms/technologies are specific products (not categories)
- [ ] All problem signals include WHERE to look and WHAT to look for
- [ ] All qualification questions are yes/no or numeric
- [ ] Disqualification criteria are actionable (can immediately rule out)
- [ ] Prospecting queries use correct tool syntax
- [ ] Buyer personas include specific titles (not "decision maker")

## Common Mistakes to Avoid

1. **Vague Characteristics**
   - ❌ "Companies that care about customer experience"
   - ✓ "NPS score <30" or "Customer service team >10% of headcount"

2. **Unmeasurable Qualities**
   - ❌ "Growth-minded organizations"
   - ✓ "20%+ YoY revenue growth" or "Actively hiring (10+ open roles)"

3. **Unactionable Disqualifiers**
   - ❌ "Not a good cultural fit"
   - ✓ "Already using [competitor] with contract >1 year remaining"

4. **Discovery Questions That Don't Qualify**
   - ❌ "What keeps you up at night?" (too vague)
   - ✓ "How many hours per week does your team spend on [specific problem]?"

5. **Missing Observable Proxies**
   - ❌ "Innovative companies" (left as-is)
   - ✓ "Filed patents in last 2 years" + "Engineering blog updated monthly"

## Reference Files

Critical frameworks and examples are in `/references/`:
- `pete-kazanjy-icp-framework.md` - Core ICP methodology
- `prospecting-tool-mapping.md` - Tool-specific query formats
- `observable-characteristics-guide.md` - Examples of good vs bad filters
- `problem-signal-patterns.md` - Where to find problem evidence
- `qualification-question-templates.md` - Question frameworks
- `b2b-vs-b2c-icp-patterns.md` - B2B, B2C, and hybrid patterns

## Universal Applicability

This skill works for ANY B2B SaaS product by:
- Following Pete Kazanjy's observable ICP framework (universal)
- Using consistent YAML structure (content varies, structure stays same)
- Mapping to standard prospecting tools (BuiltWith, LinkedIn, etc.)
- Generating qualification questions from Canvas inputs
- Focusing on what's measurable, not what's aspirational

## Success Criteria

A well-generated ICP enables:
1. Sales reps can find 50+ qualified prospects in <30 minutes
2. Qualification calls take <10 minutes to reach go/no-go decision
3. Disqualification happens in first 3 questions (save everyone's time)
4. Prospecting queries return <20% false positives
5. Every filter criterion maps to a real prospecting tool feature

## Example Usage

**Input**: Canvas for {Your Product} ({Product description})

**Process**:
1. Read `segments.md` → "{Target segment description}"
2. Convert to observable:
   - Platform: {Relevant platforms}
   - Industry: {Industry} (NAICS code)
   - Problem signal: {Observable problem indicator}
   - Traffic: 10K+ monthly visitors (implies volume)
3. Generate `qualification.md`:
   - "What {platform type} are you using?"
   - "What's your current {key metric}?"
   - "How many {relevant volume metric}?"
4. Map to tools:
   - BuiltWith: "{Platform} stores in {Category}"
   - SimilarWeb: "10K-100K monthly visitors"
   - Manual: Check for {problem signals}

**Output**: ICP YAML + Qualification MD that sales can immediately use

## Notes

- When Canvas mentions business outcomes, translate to observable preconditions
- When Canvas mentions values, translate to behavioral indicators
- When uncertain about observability, consult `references/observable-characteristics-guide.md`
- Always provide reasoning for each filter (helps sales understand WHY)
- Include both required filters (must-have) and signal filters (nice-to-have)
