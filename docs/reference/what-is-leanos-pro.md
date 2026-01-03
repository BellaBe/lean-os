# What is LeanOS Pro?

LeanOS Pro is the **complete AI-native operating system** for startups and businesses. It includes everything in Core plus domain-specific skills and agents for sales, marketing, product, engineering, and research.

**Paid Product** | 64 skills | 12 agents

---

## Core vs Pro

| Feature | Core (Free) | Pro (Paid) |
|---------|-------------|------------|
| **Skills** | 15 | 64 |
| **Agents** | 2 | 12 |
| **Reasoning** | 6 modes | 6 modes |
| **Actions** | 5 skills | 11 skills |
| **Goals** | Full support | Full support |
| **Foundations** | 2 skills | 10 skills |
| **Sales** | — | 6 skills + agent |
| **Marketing** | — | 5 skills + agent |
| **Product** | — | 5 skills + agent |
| **Engineering** | — | 12 skills + 4 agents |
| **Research** | — | 4 skills + 2 agents |
| **Critique** | — | 1 skill |
| **Programming** | — | 1 skill |
| **Indexer** | — | 1 skill |

---

## What Pro Adds

### Additional Action Skills (6)

| Skill | Question Answered |
|-------|-------------------|
| `action-evaluative` | Is this good enough? |
| `action-procedural` | How do we execute this every time? |
| `action-validation` | How do we know it worked? |
| `action-risk` | What could go wrong? |
| `action-constraint` | What must not change? |
| `action-alignment` | Why are we misaligned? |

### Additional Foundation Skills (8)

| Skill | Purpose |
|-------|---------|
| `foundations-business-model` | Revenue model design |
| `foundations-validation` | Experiment design |
| `foundations-go-to-market` | GTM strategy |
| `foundations-funding` | Fundraising preparation |
| `foundations-regulatory` | Compliance requirements |
| `foundations-retention-optimizer` | Churn analysis |
| `foundations-icp-generator` | Ideal customer profiles |
| `foundations-value-proposition` | UVP articulation |

### Sales Skills (6)

| Skill | Purpose |
|-------|---------|
| `sales-materials-generation` | Pitch decks, scripts, templates |
| `sales-prospect-research` | Find target companies |
| `sales-contact-finding` | Find decision-makers |
| `sales-outreach-sequencing` | Email/phone cadences |
| `sales-qualification-support` | Discovery call prep |
| `sales-narrative` | Sales messaging per segment |

### Marketing Skills (5)

| Skill | Purpose |
|-------|---------|
| `marketing-content-generation` | Create content |
| `marketing-content-delivery` | Publish and track |
| `marketing-channel-optimization` | Optimize channel performance |
| `marketing-content-strategy` | Motion-aware opportunity detection |
| `marketing-narrative` | Brand identity, content patterns |

### Product Skills (5)

| Skill | Purpose |
|-------|---------|
| `product-requirements` | Transform Canvas strategy into user stories |
| `product-design-flows` | Transform requirements into user journeys |
| `product-design-wireframes` | Transform flows into visual specs |
| `product-prioritization` | Prioritize features using DHM and LNO |
| `product-handoff` | Create engineering handoff contract |

### Engineering Skills (12)

**Backend (1)**
| Skill | Purpose |
|-------|---------|
| `engineering-be-foundation-targets` | Configure deployment targets and external resources |

**Frontend - Next.js (4)**
| Skill | Purpose |
|-------|---------|
| `engineering-fe-architecture` | Transform requirements into Next.js structure |
| `engineering-fe-data` | API integration and state management |
| `engineering-fe-forms` | React Hook Form + Zod validation |
| `engineering-fe-untitled-ui` | Untitled UI design system for Next.js |

**Frontend - Shopify (3)**
| Skill | Purpose |
|-------|---------|
| `engineering-fe-shopify-remix` | Shopify Remix app architecture |
| `engineering-fe-shopify-polaris` | Polaris design system |
| `engineering-fe-shopify-liquid` | Liquid templating |

**Testing & Quality (4)**
| Skill | Purpose |
|-------|---------|
| `engineering-code-lint` | Run linters, auto-fix |
| `engineering-test-execution` | Execute tests, parse results |
| `engineering-test-design` | Design test cases, coverage analysis |
| `engineering-test-bug-diagnosis` | Backward chain to root cause |

### Research Skills (4)

**Market Research (2)**
| Skill | Purpose |
|-------|---------|
| `research-market-venture` | TAM, growth, defensibility, 10x potential |
| `research-market-bootstrap` | Spend flows, budget holders, arbitrage, immediate revenue |

**Knowledge Synthesis (2)**
| Skill | Purpose |
|-------|---------|
| `research-source-processing` | Process expert sources into structured insights |
| `research-playbook-generation` | Generate actionable playbooks from insights |

### Critique Skills (1)

| Skill | Purpose |
|-------|---------|
| `critique-ux-ui` | Expert UX/UI analysis applying cognitive psychology |

### Programming Skills (1)

| Skill | Purpose |
|-------|---------|
| `programming-python-excellence` | Enforces production-quality Python standards |

### Indexer Skills (1)

| Skill | Purpose |
|-------|---------|
| `indexer-directory` | Directory indexing for context and navigation |

---

## Pro Agents (12)

| Agent | Purpose | Skills Loaded |
|-------|---------|---------------|
| `reasoning-gateway` | Reasoning mode routing | reasoning-* skills |
| `problem-solving-gateway` | Action skill routing | action-* skills |
| `sales-execution` | Sales pipeline orchestration | sales-* skills |
| `marketing-execution` | Campaign execution | marketing-* skills |
| `foundations-builder` | Canvas population through 5 phases | foundations-* skills |
| `product-manager` | Product design to engineering handoff | product-* skills |
| `engineering-be-setup` | Initialize engineering pipeline | engineering-foundation-targets |
| `engineering-fe` | Next.js frontend development | frontend-architecture, frontend-data, frontend-forms, untitled-ui |
| `engineering-fe-shopify` | Shopify app/theme development | shopify-remix, polaris, liquid |
| `engineering-testing` | Run tests, diagnose failures, fix bugs | test-execution, bug-diagnosis, test-design, code-lint |
| `market-research` | Mode-aware market analysis | research-market-*, reasoning-inductive |
| `knowledge-builder` | Knowledge synthesis pipeline | research-source-processing, research-playbook-generation |

---

## Pro Capabilities

### Autonomous Sales

```
Lead arrives
  └── sales-execution agent
        ├── Generates materials (sales-materials-generation)
        ├── Researches prospects (sales-prospect-research)
        ├── Finds contacts (sales-contact-finding)
        ├── Creates outreach sequences (sales-outreach-sequencing)
        └── Supports qualification (sales-qualification-support)
```

### Autonomous Marketing

```
Content strategy defined
  └── marketing-execution agent
        ├── Plans content (marketing-content-strategy)
        ├── Creates content (marketing-content-generation)
        ├── Delivers content (marketing-content-delivery)
        └── Optimizes channels (marketing-channel-optimization)
```

### Complete Canvas Building

```
Business idea
  └── foundations-builder agent
        ├── Market intelligence (10 skills)
        ├── Problem-solution fit
        ├── Value proposition
        ├── Business model
        ├── Validation experiments
        └── GTM strategy
```

### Engineering Workflows

```
Requirement defined
  └── engineering agents
        ├── Architecture design
        ├── Backend implementation
        ├── Frontend implementation
        ├── Testing
        └── Documentation
```

---

## Installation

Pro is delivered as a complete `.claude/` directory:

```bash
# After purchase, clone the private repo
git clone https://github.com/BellaBe/lean-os-pro.git

# Copy to your project
cp -r lean-os-pro/.claude/ your-project/
```

That's it. All 64 skills and 12 agents are ready to use.

---

## Pricing

| Option | Price | Includes |
|--------|-------|----------|
| **One-time** | $499 | All skills |

---

## Get LeanOS Pro

[Purchase on Gumroad](https://bellabe.gumroad.com/l/leanos-pro)

After purchase:
1. Provide your GitHub username
2. Receive invite to private repo
3. Clone and copy `.claude/` to your project
4. Start using all 64 skills and 12 agents
