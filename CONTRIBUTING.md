# Contributing to LeanOS Core

Thank you for your interest in contributing to LeanOS Core, an AI-native operating system for reasoning and problem-solving.

## About LeanOS Core

LeanOS Core is designed to be **operated by Claude AI**, not run locally by humans. This means:
- Claude reads the documentation and executes operations autonomously
- The system provides structured reasoning and goal management through AI skills
- Contributions focus on **design, architecture, and skill improvement**, not code execution

## How to Contribute

### 1. Skill Development

**Improving Existing Skills**

- Review skill documentation for clarity
- Add examples and edge cases
- Improve execution instructions
- Fix logical errors in workflows
- Add validation steps

**Core Skills (15 total):**
- `reasoning-*` (6): causal, abductive, inductive, analogical, dialectical, counterfactual
- `action-*` (5): descriptive, diagnostic, prescriptive, planning, decision
- `goal-*` (2): setter, tracker
- `foundations-*` (2): market-intelligence, problem-solution-fit

**Adding New Skills**

Skills are the execution layer of LeanOS. To contribute a new skill:

- Create a new directory: `.claude/skills/{skill-name}/`
- Add a `SKILL.md` file documenting:
  - Purpose and use cases
  - When to invoke the skill
  - Input/output specifications
  - Step-by-step execution instructions
  - Examples
- Follow the pattern of existing skills (see `reasoning-causal`, `goal-setter`, `action-planning`)
- Update README.md to document the new skill

### 2. Documentation Improvements

**What to Improve:**
- Clarify ambiguous instructions in CLAUDE.md or README.md
- Add examples of 6-stage causal flow threads
- Improve workflow diagrams
- Add troubleshooting guides
- Fix typos and formatting

**Documentation Standards:**
- Use clear, direct language (no fluff)
- Provide concrete examples
- Include "why" not just "what"
- Link between related concepts
- Use markdown formatting consistently

### 3. Architecture Refinements

**Canvas Structure:**
- Propose improvements to the Canvas structure
- Add validation criteria
- Improve linkage between Canvas and threads

**Thread Architecture:**
- Refine the 6-stage causal flow process
- Improve decision impact scoring
- Add thread type templates

**Directory Structure:**
- Suggest organizational improvements
- Propose naming conventions
- Improve information architecture

### 4. Workflow Optimization

**Reasoning Workflows:**
- Improve reasoning mode selection logic
- Refine hypothesis generation
- Optimize pattern detection

**Goal Management:**
- Improve goal decomposition process
- Refine progress tracking
- Optimize milestone definition

**Problem-Solving:**
- Improve action skill routing
- Refine diagnostic processes
- Optimize decision frameworks

## Contribution Process

### For Documentation Changes

1. Fork the repository
2. Create a feature branch: `git checkout -b improve-{area}`
3. Make your changes
4. Submit a pull request with:
   - Clear description of what changed
   - Why the change improves LeanOS
   - Examples if applicable

### For Skill Contributions

1. Fork the repository
2. Create a skill branch: `git checkout -b skill/{skill-name}`
3. Create the skill directory and SKILL.md
4. Update README.md to document the skill
5. Submit a pull request with:
   - Use cases for the skill
   - How it integrates with existing skills
   - Examples of when Claude should invoke it

### For Architecture Proposals

1. Open an issue first to discuss the proposal
2. Provide:
   - Current limitation or problem
   - Proposed solution
   - Impact on existing workflows
   - Examples of how it would work
3. If approved, create a PR with implementation

## What NOT to Contribute

**Don't contribute:**
- Personal Canvas data (keep business strategy private)
- Customer information or deal details
- API keys or credentials
- Company-specific configurations
- "Future ideas" lists (use active threads or don't document)
- Product-specific examples (use `{placeholder}` syntax instead)

## Philosophy Alignment

Contributions should align with LeanOS principles:

- **AI-first execution:** Skills should be executable by Claude, not just documentation
- **Context-shaping over generalization:** Each skill targets specific decision types
- **Zero redundancy:** Information exists in ONE location only
- **Evidence-based decisions:** All choices trace to Canvas or thread results
- **Production-ready over theoretical:** Working systems over academic exercises

## Review Process

**Pull requests will be reviewed for:**
1. Clarity of documentation
2. Alignment with LeanOS philosophy
3. Integration with existing architecture
4. Quality of examples
5. Impact on AI execution

**Typical timeline:**
- Documentation changes: 1-3 days
- Skill additions: 3-7 days
- Architecture changes: 7-14 days (requires discussion)

## Questions?

- **General questions:** Open an issue with the `question` label
- **Bug reports:** Open an issue with the `bug` label
- **Feature requests:** Open an issue with the `enhancement` label

## Recognition

Contributors will be acknowledged in:
- CHANGELOG.md for significant contributions
- Skill documentation for skill creators
- README.md for major architecture improvements

---

**Remember:** You're contributing to an AI-operated system. Focus on making it easier for Claude to execute operations autonomously, not on making it runnable by humans.

Thank you for helping make LeanOS Core better!

---

**License:** MIT
