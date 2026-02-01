# Mental Models Reference

Conceptual models that sharpen reasoning across all modes. Apply before analysis to frame the problem correctly.

## Foundation Models

### Telescope, Not Brain

**Model:** AI reveals structure in data—doesn't create it.

**Mechanism:**
- Dense, consistent patterns → model magnifies them
- Contradictions in data → model amplifies contradictions
- Gaps in data → model fills them (hallucination)

**Diagnostic questions:**
- What is the model pointing at?
- Is the data dense or sparse in this region?
- Is this magnification or gap-filling?

**Apply when:**
- Diagnosing hallucination ("It's not lying—it's filling gaps")
- Setting stakeholder expectations
- Evaluating model confidence

**Example:**
> Model confidently states incorrect fact about niche topic.
> 
> Diagnosis: Sparse training data in this domain. Model is interpolating across thin geometry—gap-filling, not retrieval. Solution: Add retrieval to densify the context.

---

### Reasoning = Geometry Under Constraints

**Model:** Reasoning emerges when pattern density is high enough. Hallucination emerges when geometry is thin.

**Mechanism:**
- LLMs store geometry (high-dimensional relationships), not facts
- Dense geometry → coherent recombination → reasoning
- Thin geometry → unstable interpolation → hallucination
- Querying the model = traversing this geometry

**Diagnostic questions:**
- Is this domain well-represented?
- Are we in dense or thin geometry?
- What would add density? (retrieval, examples, constraints)

**Apply when:**
- Predicting where model will fail
- Designing retrieval strategies
- Explaining inconsistent outputs

**Example:**
> Model reasons well about Python but poorly about obscure language.
> 
> Diagnosis: Dense geometry for Python (high training frequency), thin for obscure language. Not a capability gap—a density gap. Solution: Provide more examples in context.

---

### Compression = Generalization

**Model:** Models compress data structure into parameters that recreate similar structure. Understanding is compression.

**Mechanism:**
- Model doesn't "know"—it compresses
- Highly compressible domains → better performance
- Compression artifacts → predictable failure modes
- The more compressible your domain, the better results

**Diagnostic questions:**
- How compressible is this domain?
- What compression artifacts might appear?
- Is this a compression success or failure?

**Apply when:**
- Explaining model behavior to stakeholders
- Predicting performance on new domains
- Identifying representation problems

---

### Four-Layer Intelligence Stack

**Model:** Every AI capability maps to one of four layers. Most failures are misattributed to the wrong layer.

| Layer | Function | What It Does | Failure Mode |
|-------|----------|--------------|--------------|
| **Representation** | Encoding | Converts raw input to model-readable format | Wrong tokenization, missing modality, poor embedding |
| **Generalization** | Pattern Learning | Finds structure in data | Overfit, underfit, spurious correlation, shortcut learning |
| **Reasoning** | Recombination | Combines patterns into new outputs | Hallucination, incoherence, reasoning drift |
| **Agency** | Action | Translates predictions to behavior | Wrong tool, goal drift, infinite loops, overconfidence |

**Key insight:** 90% of subtle production bugs trace to Layer 1 (Representation).

**Diagnostic questions:**
- Which layer is failing?
- Am I blaming reasoning when representation is broken?
- Is this actually a data problem masquerading as a model problem?

**Apply when:**
- Diagnosing AI system failures (abductive mode)
- Designing AI systems
- Debugging unexpected behavior

**Example:**
> Agent repeatedly calls wrong API.
> 
> First instinct: Reasoning failure (Layer 3).
> Layer check: Is the API correctly represented in the tool schema? 
> Finding: Schema has wrong parameter types.
> Actual failure: Representation (Layer 1), not reasoning.

---

### 8-Layer System Stack

**Model:** Production AI requires 8 interacting layers. The model is not the product—the system is.

```
Layer 1: Input Sanitation      → Controlled input representation
Layer 2: Retrieval             → Grounding in factual context
Layer 3: Model Invocation      → Right model for right task
Layer 4: Reasoning Orchestration → CoT, tools, verification, planning
Layer 5: Constraint & Safety   → Multiple overlapping guardrails
Layer 6: Memory                → Selective, permissioned, decayed
Layer 7: Feedback & Evaluation → Continuous measurement
Layer 8: Monitoring & Drift    → Distribution shift detection
```

**Key insight:** "LLMs are unreliable alone, but unstoppable in systems."

**Diagnostic questions:**
- Which layer is the failure in?
- Are layers properly decoupled?
- What's missing from the stack?

**Apply when:**
- Designing AI products
- Diagnosing production failures
- Auditing system architecture

---

## Operational Models

### Prediction is Cheap, Behavior is Expensive

**Model:** Generating text is easy. Acting on the world has consequences.

**Implication:**
- Prediction errors are recoverable
- Behavior errors compound
- Autonomy requires responsibility, not just capability

**Apply when:**
- Designing agent constraints
- Setting approval thresholds
- Evaluating autonomy levels

---

### Agent = Contract, Not Model

**Model:** An agent is defined by its constraints, not its capabilities.

**Contract elements:**
- What must the agent never do?
- What must the agent always do?
- What tools can it access?
- What's outside its domain?
- What constraints protect the environment from the agent?
- What constraints protect the agent from the environment?

**Apply when:**
- Designing agent boundaries
- Writing agent specifications
- Debugging agent failures

---

### Labels ≠ Truth

**Model:** Labels are opinions frozen in data—approximations, judgments, artifacts of human perception.

**Implication:**
- Training on messy labels → model becomes "a flawlessly learned representation of flawed human decisions"
- Model "errors" may be label disagreements
- Evaluation reveals human inconsistency, not just model failure

**Apply when:**
- Evaluating training data quality
- Interpreting model "mistakes"
- Designing evaluation pipelines

---

## Agent Failure Modes

When diagnosing agent systems, check for these patterns:

| Mode | Signal | Typical Cause | Fix |
|------|--------|---------------|-----|
| **Hallucinated Actions** | Invents tools/APIs that don't exist | Missing tool schema validation | Strict schema enforcement |
| **Infinite Loops** | Continues without terminating | No exit conditions | Iteration caps, goal completion checks |
| **Goal Drift** | Task changes mid-execution | Weak goal anchoring | Explicit goal state in context |
| **Over-Confidence** | High certainty + wrong action | No confidence thresholds | Require verification for irreversible actions |

---

## Using Models in Reasoning

### Framing (before selecting mode)

> "Before diagnosing, let me apply Four-Layer Stack: Is this actually a reasoning problem, or is representation broken upstream?"

### Challenge (during analysis)

> "Applying Telescope model: The model is filling gaps here, not retrieving. Confidence should be lower."

### Explanation (communicating findings)

> "This isn't a model failure—it's a compression artifact. The domain is too irregular for the model to generalize cleanly."

---

## Quick Reference

| Situation | Model to Apply |
|-----------|----------------|
| Model confidently wrong | Telescope (gap-filling vs retrieval) |
| Inconsistent outputs | Geometry (dense vs thin) |
| Explaining to stakeholders | Compression (model compresses, doesn't understand) |
| Debugging AI failure | Four-Layer Stack (which layer?) |
| Designing AI product | 8-Layer System Stack |
| Agent misbehaving | Agent Failure Modes |
| Evaluating training data | Labels ≠ Truth |
| Setting autonomy level | Prediction vs Behavior |
