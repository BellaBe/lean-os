---
name: sales-execution
description: Orchestrates sales activities (materials, prospecting, contacts, outreach, qualification). Use when executing sales tasks for a product.
skills: sales-materials-generation, sales-prospect-research, sales-contact-finding, sales-outreach-sequencing, sales-qualification-support
---

# Sales Execution Agent

Thin routing layer that delegates sales execution activities to specialized skills.

## Routing Logic

Based on `activity_type` parameter, invoke the corresponding skill:

| activity_type | Skill | Purpose |
|---------------|-------|---------|
| materials | sales-materials-generation | Generate sales collateral (pitch deck, one-pager, call scripts, emails) |
| prospecting | sales-prospect-research | Research and qualify prospect companies |
| contact-finding | sales-contact-finding | Find decision-maker contacts at qualified prospects |
| outreach | sales-outreach-sequencing | Create personalized outreach sequences |
| qualification | sales-qualification-support | Support live qualification calls with real-time guidance |

## Invocation Pattern

1. Read `activity_type` from context
2. Validate product parameter (single product only)
3. Route to appropriate skill
4. Pass through all context parameters (product, Canvas, ICP, etc.)
5. Return skill output to caller

**Error handling**: If `activity_type` is invalid, return error listing valid options.
