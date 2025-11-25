---
name: sales-narrative
description: Generate persona-specific sales narratives using Peter Kazanjy's founding sales methodology. Creates problem-solution-specifics narratives for economic buyers, technical buyers, and end users based on discovery data.
allowed-tools: "Read,Write,Bash"
version: 2.0.0
---

# Sales Narrative Generator (Kazanjy Methodology)

You generate persona-specific sales narratives from discovery interviews using Peter Kazanjy's founding sales approach.

## Methodology

Read: `{baseDir}/references/kazanjy_methodology.md` for full framework

Key principles:
- **Hypothesis-driven**: Every deal tests ICP/pain/value assumptions
- **Discovery-based**: Generate from actual prospect data, not templates
- **Persona-specific**: Economic ≠ Technical ≠ End User narratives
- **Objection pre-emption**: Address blockers before they arise

## Process

### Step 1: Validate Discovery Completeness

Run validation script:
```bash
python {baseDir}/scripts/validate_discovery.py S001
```

If `valid: false`, stop and inform user which discovery files are missing.

### Step 2: Check Staleness (if narrative exists)
```bash
python {baseDir}/scripts/detect_staleness.py S001 economic-buyer
```

If `is_stale: false`, inform user narrative is current.

### Step 3: Extract Discovery Data
```bash
python {baseDir}/scripts/extract_discovery.py S001
```

This gives you structured JSON with:
- Problem interview insights
- Solution interview insights  
- Stakeholder/persona mapping

### Step 4: Read Canvas Positioning

Read these files to understand current strategic positioning:
- `strategy/canvas/problem.md` - Validated pain hypothesis
- `strategy/canvas/solution.md` - How we solve it
- `strategy/canvas/unique-value.md` - Differentiation
- `strategy/canvas/metrics.md` - Proof points

### Step 5: Read Persona Patterns

Read: `{baseDir}/references/persona_patterns.md`

This shows you example narratives for each persona type:
- Economic buyer (CFO, VP): ROI focus
- Technical buyer (CTO, Eng): Implementation focus
- End user (Designer): Daily workflow focus

### Step 6: Generate Narrative

**You generate the narrative** using:
- Discovery data (Step 3)
- Canvas positioning (Step 4)
- Persona patterns (Step 5)
- PSS structure (Problem-Solution-Specifics)

Follow this structure:
```markdown
# [Persona] Narrative: [Thread ID]
*Generated: [timestamp]*
*For: [Persona Name] - [Role]*

## Problem

[Write problem section using:]
- Specific pain points from their problem interview
- Quantified impact where they provided numbers
- Competitive/opportunity cost context
- Use their language and examples

## Solution

[Write solution section using:]
- How your product addresses their specific pain
- Canvas unique value proposition
- Why now / why us
- Risk mitigation relevant to this persona

## Specifics

[Write specifics section using:]
- Canvas metrics/proof points
- Case studies relevant to their industry
- ROI model (economic buyer) OR integration timeline (technical) OR workflow improvement (end user)
- Implementation details they care about

## Pre-Empted Objections

[Include objections from solution interview + common ones for persona:]
- **[Objection]**: [How we address it]

## Next Steps

[Recommend next action based on persona and stage]
```

### Step 7: Write Output

Write to: `artifacts/sales/{segment}/narratives/{segment}-{persona}.md`

**File naming convention**:
- Economic buyer: `{segment}-economic-buyer.md`
- Technical buyer: `{segment}-technical-buyer.md`
- Objection library: `{segment}-objection-lib.md`

**No metadata file needed** - narratives are regenerated when Canvas/discovery changes

### Step 8: Present to User

Show:
- Path to generated narrative
- Key insights you incorporated from discovery
- Which objections you pre-empted
- Recommended next action

## Persona-Specific Guidance

Read detailed patterns in `{baseDir}/references/persona_patterns.md`

### Economic Buyer
**They care about**: Business impact, ROI, risk, budget
**Problem section**: Quantified cost of status quo, opportunity cost
**Solution section**: Financial model, payback period, risk mitigation
**Specifics section**: ROI calculation, case study outcomes, TCO comparison

### Technical Buyer
**They care about**: Implementation, integration, maintenance, security
**Problem section**: Technical debt, complexity, vendor concerns
**Solution section**: Architecture fit, API simplicity, support quality
**Specifics section**: Integration timeline, security/compliance, SLA

### End User
**They care about**: Daily workflow, ease of use, productivity
**Problem section**: Manual frustration, inconsistent results
**Solution section**: Speed, accuracy, simplicity
**Specifics section**: Time saved per task, quality improvement, training time

## Error Handling

**Missing discovery files**:
```
Cannot generate narrative for S001:
- Missing: discovery/problem-interview.md

User must complete problem interview first.
```

**Persona not in stakeholders**:
```
Persona 'economic-buyer' not found in stakeholders.md
Available personas: technical-buyer, end-user

User should update stakeholder mapping or specify correct persona.
```

## Examples

Read complete example narratives in `{baseDir}/references/persona_patterns.md`