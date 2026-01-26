# Descriptive Schema Reference

Neutral summary without recommendations.

## When to Use

- Need objective summary of situation
- Providing information for others to decide
- Documenting current state
- Explaining or comparing without advocacy
- Default schema when no other fits

## Purpose

**Inform without influencing.** Present facts, structure information, acknowledge uncertainty. Let the reader draw conclusions.

## Distinction from Other Schemas

| Schema | Stance | Purpose |
|--------|--------|---------|
| **Descriptive** | **Neutral** | **Inform** |
| Prescriptive | Advocacy | Recommend action |
| Evaluative | Judgment | Assess quality |
| Diagnostic | Explanatory | Explain why |

## Structure

### Scope Definition

```yaml
scope:
  topic: "Q1 marketing campaign performance"
  boundaries:
    includes:
      - "Paid acquisition metrics"
      - "Organic growth metrics"
      - "Campaign costs"
    excludes:
      - "Product changes during period"
      - "Competitor activity"
  time_period: "January 1 - March 31, 2024"
  audience: "Executive team"
```

### Summary

Brief, neutral overview.

```yaml
summary: "Q1 marketing spent $150K across three channels, generating 2,400 leads at $62.50 CPL. Email performed best by volume; paid social had lowest CPL."
```

### Structured Details

Organized by logical sections.

```yaml
details:
  - section: "Channel Performance"
    content:
      - "Email: 1,200 leads, $45K spend, $37.50 CPL"
      - "Paid Social: 800 leads, $50K spend, $62.50 CPL"
      - "Content/SEO: 400 leads, $55K spend, $137.50 CPL"
      
  - section: "Conversion Funnel"
    content:
      - "Lead to MQL: 35% (840 MQLs)"
      - "MQL to SQL: 25% (210 SQLs)"
      - "SQL to Opportunity: 40% (84 Opps)"
      
  - section: "Budget Utilization"
    content:
      - "Total budget: $180K"
      - "Spent: $150K (83%)"
      - "Remaining: $30K"
```

### Evidence and Sources

Cite sources for claims.

```yaml
evidence:
  - claim: "Email generated 1,200 leads"
    source: "HubSpot dashboard, exported March 31"
    confidence: high
    
  - claim: "Paid social CPL was $62.50"
    source: "Meta Ads Manager + Google Ads, combined"
    confidence: high
    
  - claim: "Content/SEO attribution"
    source: "First-touch attribution model"
    confidence: medium
    caveat: "Multi-touch would show different numbers"
```

### Open Questions

What remains unknown or uncertain.

```yaml
open_questions:
  - "How much pipeline did Q1 leads generate?"
  - "What's the quality difference between channels?"
  - "How does this compare to industry benchmarks?"
  - "What drove the email over-performance?"
```

## Writing Guidelines

### Neutral Language

| Avoid (Evaluative) | Use (Descriptive) |
|-------------------|-------------------|
| "Email performed excellently" | "Email had the lowest CPL" |
| "Content marketing failed" | "Content marketing had the highest CPL" |
| "We should increase email budget" | "Email used 30% of budget, generated 50% of leads" |
| "The results were disappointing" | "Results were below Q4 levels" |

### Structure Over Prose

- Use sections with clear headers
- Present data in consistent formats
- Avoid narrative arc (no buildup/conclusion)
- Let structure carry the message

### Acknowledge Uncertainty

```yaml
uncertainty_levels:
  high_confidence:
    - "Total spend was $150K" (direct measurement)
  medium_confidence:
    - "Content contributed 400 leads" (attribution model dependent)
  low_confidence:
    - "Industry CPL benchmark is $50" (single source, dated)
```

## Quality Gates

| Gate | Requirement |
|------|-------------|
| Scope explicit | Reader knows boundaries |
| Claims sourced | Evidence for each assertion |
| Neutral language | No evaluative adjectives |
| No recommendations | Facts only, reader decides |
| Uncertainty flagged | Confidence levels stated |
| Questions acknowledged | Unknown items listed |

## Anti-Patterns

| Avoid | Do Instead |
|-------|------------|
| Hidden recommendations | State facts, let reader conclude |
| Selective presentation | Include all relevant data |
| Evaluative language | Neutral descriptions |
| Ignoring uncertainty | Flag confidence levels |
| Burying unfavorable data | Present prominently if relevant |

## Transitions to Other Schemas

Descriptive is often the **first step** before:

| Next Schema | Trigger |
|-------------|---------|
| Evaluative | "Is this good or bad?" |
| Prescriptive | "What should we do?" |
| Diagnostic | "Why did this happen?" |
| Decision | "Which option should we choose?" |

## Output Schema

```yaml
descriptive:
  scope:
    topic: string
    boundaries:
      includes: [string]
      excludes: [string]
    time_period: optional<string>
    audience: optional<string>
    
  summary: string
  
  details:
    - section: string
      content: [string]
      
  evidence:
    - claim: string
      source: string
      confidence: high | medium | low
      caveat: optional<string>
      
  open_questions: [string]
```

## Example: Market Landscape

```yaml
descriptive:
  scope:
    topic: "AI coding assistant market Q4 2024"
    boundaries:
      includes: ["Commercial products", "Major open source"]
      excludes: ["General LLMs", "Research prototypes"]
      
  summary: "Market has 5 major commercial players and 3 significant open source projects. Total funding exceeds $500M. GitHub Copilot leads by install base; newer entrants compete on features and price."
  
  details:
    - section: "Major Players"
      content:
        - "GitHub Copilot: $10/mo individual, $19/mo business, ~1M+ users"
        - "Cursor: $20/mo, ~100K users, VS Code fork approach"
        - "Codeium: Free tier available, enterprise focus"
        - "Amazon CodeWhisperer: Free for individuals, AWS integration"
        - "Tabnine: $12/mo, on-premise options"
        
    - section: "Recent Funding"
      content:
        - "Cursor: $60M Series A (2024)"
        - "Codeium: $65M Series B (2024)"
        - "Magic: $117M Series A (2024)"
        
    - section: "Feature Landscape"
      content:
        - "All offer autocomplete"
        - "Chat interfaces now standard"
        - "Codebase awareness emerging differentiator"
        - "Agentic capabilities in early stages"
        
  evidence:
    - claim: "GitHub Copilot has 1M+ users"
      source: "GitHub blog, October 2024"
      confidence: medium
      caveat: "May include inactive users"
      
  open_questions:
    - "Enterprise adoption rates by sector?"
    - "Retention rates across products?"
    - "Developer productivity impact data?"
```
