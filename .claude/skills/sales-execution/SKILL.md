---
name: sales-execution
description: Orchestrator that routes sales activity requests to specialized subskills based on activity type (materials, prospecting, contact-finding, outreach, qualification)
allowed-tools: [Read]
---

# Sales Execution Orchestrator

## Purpose

Thin routing layer that delegates sales execution activities to specialized subskills. Does not perform activities itself—only routes to the appropriate subskill based on `activity_type` parameter.

**Called by**: causal-flow with activity type and product context
**Operates on**: ONE product per invocation (no multi-product parallelization)

## Routing Logic

Based on `activity_type` parameter, invoke the corresponding subskill:

### Activity Type: "materials"
**Route to**: `materials-generation/SKILL.md`
**Purpose**: Generate sales collateral (pitch deck, one-pager, call scripts, emails)
**Inputs**: product, Canvas location, ICP location, narrative location
**Outputs**: Sales materials in `artifacts/sales/`

### Activity Type: "prospecting"
**Route to**: `prospect-research/SKILL.md`
**Purpose**: Research and qualify prospect companies
**Inputs**: product, ICP definition, target list (optional)
**Outputs**: Qualified prospect list with scoring

### Activity Type: "contact-finding"
**Route to**: `contact-finding/SKILL.md`
**Purpose**: Find decision-maker contacts at qualified prospects
**Inputs**: product, qualified prospect list, buyer personas from ICP
**Outputs**: Contact list with names, titles, LinkedIn URLs

### Activity Type: "outreach"
**Route to**: `outreach-sequencing/SKILL.md`
**Purpose**: Create personalized outreach sequences
**Inputs**: product, contacts, email templates, ICP
**Outputs**: Personalized email sequences per contact

### Activity Type**: "qualification"
**Route to**: `qualification-support/SKILL.md`
**Purpose**: Support live qualification calls with real-time guidance
**Inputs**: product, prospect context, qualification questions from ICP
**Outputs**: Call preparation, question routing, objection responses

## Invocation Pattern

1. Read `activity_type` from context
2. Validate product parameter (single product only)
3. Route to appropriate subskill SKILL.md path
4. Pass through all context parameters (product, Canvas, ICP, etc.)
5. Return subskill output to caller

**Error handling**: If `activity_type` is invalid, return error listing valid options.
