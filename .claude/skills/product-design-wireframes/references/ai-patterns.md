# AI UX Patterns Reference

Reference for designing AI-powered features. Load when wireframing AI interactions.

Based on: Shape of AI, Microsoft HAI Guidelines, Google PAIR

## Spatial Patterns

Choose how AI appears in the interface:

| Pattern | When to Use | Example |
|---------|-------------|---------|
| **Alongside** | AI assists without interrupting | Sidebar suggestions |
| **Layered** | AI enhances existing content | Inline completions |
| **Integrated** | AI is core to the feature | Smart compose |
| **Conversational** | Dialog-based interaction | Chat interface |

## Wayfinding Patterns

Help users start using AI features:

### Suggestions
Provide starter prompts for blank states.
```
┌─────────────────────────────────┐
│ What would you like to create?  │
│                                 │
│ [📝 Write a summary]            │
│ [📊 Analyze this data]          │
│ [💡 Generate ideas for...]      │
└─────────────────────────────────┘
```

### Templates
Pre-structured formats for common tasks.
```
┌─────────────────────────────────┐
│ Choose a template:              │
│                                 │
│ ○ Meeting notes                 │
│ ○ Project brief                 │
│ ○ Status update                 │
└─────────────────────────────────┘
```

### Examples
Show sample inputs and outputs.
```
┌─────────────────────────────────┐
│ Try: "Summarize this article    │
│       in 3 bullet points"       │
│                                 │
│ → • Key finding one             │
│   • Key finding two             │
│   • Key finding three           │
└─────────────────────────────────┘
```

## Trust Patterns

Build confidence in AI outputs:

### Disclosure
Always mark AI-generated content.
```
┌─────────────────────────────────┐
│ 🤖 AI-generated                 │
│                                 │
│ [Content here]                  │
└─────────────────────────────────┘
```

### Citations
Link to sources when applicable.
```
┌─────────────────────────────────┐
│ The market grew 15% in Q3.      │
│ [1]                             │
│                                 │
│ Sources:                        │
│ [1] Industry Report 2024        │
└─────────────────────────────────┘
```

### Confidence Indicators
Show certainty levels.
```
┌─────────────────────────────────┐
│ High confidence ████████░░ 80%  │
│                                 │
│ This appears to be a cat.       │
└─────────────────────────────────┘
```

### Caveats
Disclose known limitations.
```
┌─────────────────────────────────┐
│ ⚠️ Note: This analysis is based │
│ on data through March 2024.     │
└─────────────────────────────────┘
```

## Control Patterns

Maintain user agency:

### Action Plan
Show what AI will do before doing it.
```
┌─────────────────────────────────┐
│ AI will:                        │
│ 1. Read the document            │
│ 2. Extract key points           │
│ 3. Generate summary             │
│                                 │
│ [Proceed] [Cancel]              │
└─────────────────────────────────┘
```

### Stop/Pause
Allow interruption during generation.
```
┌─────────────────────────────────┐
│ Generating response...          │
│ ████████░░░░░░░░░░░░            │
│                                 │
│ [⏹ Stop]                        │
└─────────────────────────────────┘
```

### Feedback
Enable quick quality signals.
```
┌─────────────────────────────────┐
│ Was this helpful?               │
│                                 │
│ [👍] [👎] [Report issue]        │
└─────────────────────────────────┘
```

### Undo/Revert
Easy rollback of AI actions.
```
┌─────────────────────────────────┐
│ ✓ Changes applied               │
│                                 │
│ [Undo] [View changes]           │
└─────────────────────────────────┘
```

## Error Handling

Design for when AI fails:

### Graceful Degradation
```
┌─────────────────────────────────┐
│ AI suggestions unavailable      │
│                                 │
│ You can still:                  │
│ • Type manually                 │
│ • Use templates                 │
│ • Try again later               │
└─────────────────────────────────┘
```

### Low Confidence
```
┌─────────────────────────────────┐
│ ⚠️ Low confidence result        │
│                                 │
│ [Content with uncertainty]      │
│                                 │
│ [Accept anyway] [Try different] │
└─────────────────────────────────┘
```

### Wrong Output Recovery
```
┌─────────────────────────────────┐
│ Not what you expected?          │
│                                 │
│ [Regenerate] [Edit manually]    │
│ [Give feedback]                 │
└─────────────────────────────────┘
```

## Component Spec Addition

When specifying AI components, add:

```markdown
### AI-Specific Properties

**Spatial Pattern:** [Alongside / Layered / Integrated / Conversational]

**Trust Patterns:**
- Disclosure: [How AI is identified]
- Confidence: [How certainty shown]
- Citations: [How sources linked]

**Control Patterns:**
- Invoke: [How to trigger AI]
- Dismiss: [How to ignore/hide]
- Correct: [How to fix mistakes]
- Stop: [How to interrupt]

**Error States:**
- AI unavailable: [Fallback behavior]
- Low confidence: [How indicated]
- Wrong output: [Recovery path]
```

## Checklist

Before finalizing AI wireframes:

### Wayfinding
- [ ] Suggestions provided for empty states
- [ ] Templates available for common tasks
- [ ] Examples show expected input/output

### Trust
- [ ] AI content clearly marked
- [ ] Sources linked where applicable
- [ ] Confidence levels visible when uncertain
- [ ] Limitations disclosed

### Control
- [ ] User can preview AI actions
- [ ] Stop/pause available during generation
- [ ] Feedback mechanism present
- [ ] Undo available for AI changes

### Error Handling
- [ ] Graceful degradation when AI unavailable
- [ ] Low confidence results flagged
- [ ] Easy recovery from wrong outputs
- [ ] Manual fallback always available

## Key Principles

> "Human-centric design: Patterns prioritize clarity, control, and trust rather than opaque 'magic.'"

> "Make clear what the system can do. Make clear how well the system can do what it can do." — Microsoft HAI

> "Design for wrong. AI will make mistakes; the question is how users recover."