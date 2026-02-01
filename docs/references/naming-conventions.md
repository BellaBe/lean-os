# LeanOS Naming Conventions

Standard naming rules for agents and skills under `.claude/`.

---

## Official Rules (Anthropic)

| Rule | Constraint |
|------|------------|
| Max length | 64 characters |
| Allowed chars | lowercase letters, numbers, hyphens (and dots for sub-prefixes) |
| Reserved words | Cannot contain "anthropic", "claude" |
| Dir = Name | Directory name must match `name:` field in YAML |

---

## Agent Conventions

### Structure

```
{prefix}-{role}
```

| Component | Role | Example |
|-----------|------|---------|
| Prefix | Vertical namespace | `mkt-` |
| Role | What the agent does (noun) | `strategist`, `manager`, `engineer` |

### Naming Rules

| Rule | Detail |
|------|--------|
| Pattern | `{prefix}-{role-noun}` |
| Role types | `strategist`, `manager`, `engineer`, `builder`, `creator`, `allocator`, `calibrator`, `evaluator` |
| Compound roles | Hyphenated: `outbound-manager`, `growth-engineer`, `problem-solver` |
| Engineering sub-layers | Dot notation: `eng.be-`, `eng.fe-`, `eng.t-` |
| File location | `.claude/agents/{name}.md` |

### Agent Role Patterns

| Role Suffix | Responsibility | Examples |
|-------------|---------------|----------|
| `-strategist` | Plans and designs processes | sls-strategist, mkt-strategist |
| `-manager` | Orchestrates execution workflows | sls-outbound-manager, cst-success-manager |
| `-engineer` | Builds technical artifacts | prd-engineer, eng.be-python-engineer |
| `-builder` | End-to-end construction | fnd-builder, knw-builder |
| `-creator` | Generates content/artifacts | mkt-narrative-creator, sys-vertical-creator |
| `-planner` | Plans specific phases | fnd-launch-planner |
| `-researcher` | Investigates and analyzes | fnd-researcher, rsh-researcher |
| `-assessor` | Evaluates against criteria | fnd-compliance-assessor |
| `-allocator` | Distributes resources | rop-allocator |
| `-calibrator` | Tunes models and scores | rop-calibrator |
| `-evaluator` | Measures performance | rop-evaluator |
| `-router` | Routes signals/work | rop-signal-router |
| `-solver` | Resolves problems | rsn-problem-solver |
| `-orchestrator` | Coordinates multi-agent work | rsn-orchestrator |

### Agents by Vertical

| Vertical | Prefix | Agents |
|----------|--------|--------|
| Engineering | `eng.be-`, `eng.fe-`, `eng.t-` | intent-engineer, spec-engineer, plan-engineer, codemap-engineer, python-engineer, engineer, shopify-engineer, engineer |
| Foundations | `fnd-` | architect, researcher, modeler, launch-planner, builder, canvas-validator, compliance-assessor, funding-strategist |
| Product | `prd-` | engineer, growth-engineer |
| Sales | `sls-` | strategist, outbound-manager, partner-manager, enablement-manager |
| Marketing | `mkt-` | narrative-creator, strategist, content-manager, campaign-manager, inbound-manager |
| Customer | `cst-` | success-manager, retention-manager, expansion-manager, advocacy-manager |
| RevOps | `rop-` | signal-router, calibrator, allocator, evaluator |
| Reasoning | `rsn-` | problem-solver, orchestrator |
| Research | `rsh-` | researcher |
| Knowledge | `knw-` | builder |
| Operations | `ops-` | manager |
| System | `sys-` | vertical-creator |

**Total: 41 agents**

---

## Skill Conventions

### Structure

```
{prefix}-{gerund}-{object}
```

| Component | Role | Example |
|-----------|------|---------|
| Prefix | Vertical namespace | `sls-` |
| Gerund | Action (verb-ing) | `qualifying` |
| Object | Target/modifier | `prospects` |

### Naming Rules

| Rule | Constraint |
|------|------------|
| Form | `{gerund}-{object}` word order required |
| Gerund | Present participle (-ing form) |
| Object | Plural nouns preferred |
| File location | `.claude/skills/{name}/SKILL.md` |

---

## Vertical Prefixes

| Vertical | Prefix | Used By |
|----------|--------|---------|
| behavioral (choice architecture) | `beh-` | skills only |
| code lint | `lnt-` | skills only |
| critique | `crt-` | skills only |
| customer | `cst-` | agents + skills |
| design system | `dsg-` | skills only |
| engineering | `eng.{layer}-` | agents + skills |
| foundations | `fnd-` / `fnd.{phase}-` | agents + skills |
| intelligence | `int-` | skills only |
| knowledge | `knw-` | agents + skills |
| marketing | `mkt-` | agents + skills |
| operations | `ops-` | agents only |
| product | `prd-` | agents + skills |
| reasoning | `rsn-` | agents + skills |
| research | `rsh-` | agents + skills |
| revops | `rop-` | agents + skills |
| sales | `sls-` | agents + skills |
| system | `sys-` | agents + skills |

---

## Engineering Sub-Prefixes

| Layer | Sub-prefix |
|-------|------------|
| Backend | `eng.be-` |
| Frontend | `eng.fe-` |
| Testing | `eng.t-` |

### Backend (`eng.be-`)

```
eng.be-codebase-architecture
eng.be-codegen-anchor-generator
eng.be-codegen-application-generator
eng.be-codegen-verification
eng.be-codemapir-module-generator
eng.be-codemapir-verification
eng.be-intentir-semantic-extractor
eng.be-intentir-verification
eng.be-planir-usecase-generator
eng.be-planir-verification
eng.be-specir-object-constructor
eng.be-specir-verification
```

### Frontend (`eng.fe-`)

```
eng.fe-architecture
eng.fe-data
eng.fe-forms
eng.fe-shopify-liquid
eng.fe-shopify-polaris
eng.fe-shopify-remix
```

### Testing (`eng.t-`)

```
eng.t-designing-tests
eng.t-diagnosing-bugs
eng.t-executing-tests
```

---

## Foundations Sub-Prefixes

| Phase | Sub-prefix |
|-------|------------|
| Research | `fnd.r-` |
| Model | `fnd.m-` |
| Launch | `fnd.l-` |
| Validators (cross-phase) | `fnd-` |
| Domain intelligence | `fnd-` |

Examples:

```
fnd.r-sizing-markets
fnd.r-scoring-problems
fnd.m-designing-pricing
fnd.l-planning-gtm
fnd-validating-gates
fnd-compliance
fnd-funding-strategy
```

---

## Intelligence Skills

Pattern: `int-applying-{domain}`

```
int-applying-category-theory
int-applying-behavioral-science
int-applying-python-excellence
int-applying-authn
int-applying-owasp
```

---

## Design System Skills

Pattern: `dsg-{layer-or-stage}`

```
dsg-intent
dsg-foundations
dsg-tokens
dsg-policies
dsg-components-base
dsg-components-app
dsg-components-marketing
dsg-components-ai
dsg-figma-visual-spec
```

---

## Behavioral Skills

Pattern: `beh-{gerund}-{object}`

```
beh-auditing-behavior
beh-designing-choices
beh-mapping-journeys
beh-setting-defaults
beh-calibrating-friction
beh-structuring-information
```

---

## Standalone Skills -- Folded

| Original | Folded to |
|----------|-----------|
| `icp-generator` | `cst-generating-icps` |
| `creative-thinking` | `rsn-creating-ideas` |
| `storytelling` | `mkt-telling-stories` |
| `narrative-foundations` | `mkt-crafting-narratives` |

---

## Examples by Vertical

| Vertical | Example Skills |
|----------|----------------|
| `beh-` | `beh-auditing-behavior`, `beh-calibrating-friction` |
| `cst-` | `cst-generating-icps`, `cst-diagnosing-churn` |
| `dsg-` | `dsg-intent`, `dsg-foundations` |
| `eng.be-` | `eng.be-codebase-architecture`, `eng.be-codegen-verification` |
| `eng.fe-` | `eng.fe-architecture`, `eng.fe-shopify-remix` |
| `eng.t-` | `eng.t-designing-tests`, `eng.t-diagnosing-bugs` |
| `fnd.r-` | `fnd.r-sizing-markets`, `fnd.r-scoring-problems` |
| `fnd-` | `fnd-compliance`, `fnd-funding-strategy` |
| `fnd.m-` | `fnd.m-designing-pricing`, `fnd.m-calculating-economics` |
| `int-` | `int-applying-category-theory`, `int-applying-python-excellence` |
| `mkt-` | `mkt-telling-stories`, `mkt-crafting-narratives` |
| `prd-` | `prd-specifying-features`, `prd-designing-interactions` |
| `rsn-` | `rsn-creating-ideas`, `rsn-reasoning-problems` |
| `sls-` | `sls-qualifying-prospects`, `sls-creating-battlecards` |
| `sys-` | `sys-defining-goals`, `sys-executing-threads` |
| `rop-` | `rop-scoring-pql`, `rop-routing-signals` |
| `knw-` | `knw-generating-insights`, `knw-generating-playbooks` |
| `rsh-` | `rsh-market-venture`, `rsh-market-bootstrap` |

---

## Filesystem Layout

```
.claude/
├── agents/
│   ├── cst-success-manager.md
│   ├── eng.be-python-engineer.md
│   ├── fnd-builder.md
│   ├── mkt-strategist.md
│   ├── ops-manager.md
│   ├── rop-allocator.md
│   ├── rsn-problem-solver.md
│   ├── sls-outbound-manager.md
│   ├── sys-vertical-creator.md
│   └── ...
│
└── skills/
    ├── beh-auditing-behavior/
    ├── cst-diagnosing-churn/
    ├── dsg-tokens/
    ├── eng.be-codegen-verification/
    ├── eng.fe-architecture/
    ├── eng.t-designing-tests/
    ├── fnd-compliance/
    ├── fnd.m-designing-pricing/
    ├── fnd.r-sizing-markets/
    ├── int-applying-category-theory/
    ├── mkt-crafting-narratives/
    ├── prd-specifying-features/
    ├── rop-scoring-pql/
    ├── rsn-reasoning-problems/
    ├── sls-qualifying-prospects/
    ├── sys-executing-threads/
    └── ...
```
