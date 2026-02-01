# Scanning Mode

Broad, shallow attention across a space.

## When to Use

- Need landscape awareness
- Don't know what's important yet
- Entering unfamiliar domain
- Checking for changes since last look
- Starting research or investigation

## Mental Model

**Radar sweep:** Cover maximum area, detect anything notable. Depth sacrificed for breadth.

## Scanning Patterns

### Sweep
Cover everything once at uniform depth.

**Use when:** Initial survey, periodic landscape check, need comprehensive view.

**Process:**
1. Define boundaries of space
2. Systematically cover each area once
3. Note signals, don't investigate yet
4. Move on after brief attention

### Sample
Cover representative subset.

**Use when:** Space too large for complete sweep, resources constrained.

**Process:**
1. Identify key segments of space
2. Select representative items from each
3. Examine samples
4. Extrapolate to whole

### Edge
Focus on periphery and outliers.

**Use when:** Core is well-understood, looking for emerging signals, anomaly detection.

**Process:**
1. Identify boundaries of known space
2. Examine what's at the edges
3. Look for outliers
4. Note what doesn't fit patterns

### Competitive
Survey key players only.

**Use when:** Landscape has clear key players, regular monitoring of known entities.

**Process:**
1. Identify key players
2. Check each for changes
3. Note significant updates
4. Skip non-players

## Execution

### Configuration

Before scanning, define:

**Scope:** What domain? What boundaries (include/exclude)?

**Targets:** What categories are we looking for? What are we explicitly not looking for?

**Sources:** Primary (company sites, official docs), Secondary (news, analysts), Tertiary (social, forums)

**Time budget:** Total time, allocation per source type

### Process

1. **Prepare** — Set time limit, open source list, prepare notes
2. **Scan** — Work through sources systematically, fixed time per source (e.g., 5 min), note signals don't investigate, use headlines/summaries not full content
3. **Capture** — Record each signal found, tag with relevance level, note source
4. **Triage** — Review signals, classify: focus / monitor / ignore, queue high-relevance for focusing

### Time Discipline

- Set timer per source
- Move on when timer ends
- Note "investigate later" rather than diving in

## Output Format

```markdown
## Scanning: [Domain]

**Scope:** [What was scanned, boundaries]
**Pattern:** [Sweep/Sample/Edge/Competitive]
**Time spent:** [Duration]
**Sources:** [List of sources checked]

### Landscape Summary

[2-3 sentence overview of what was found]

**Key themes:**
- [Theme 1]
- [Theme 2]

**Changes since last scan:** [If applicable]

### Signals Detected

**High relevance:**
- [Signal]: [Source] — Action: Focus
- [Signal]: [Source] — Action: Focus

**Medium relevance:**
- [Signal]: [Source] — Action: Monitor
- [Signal]: [Source] — Action: Monitor

**Low relevance (noted but ignoring):**
- [Signal]: [Source]

### Blind Spots

- [What might have been missed]
- [Sources not checked]
- [Areas under-covered]

### Next Actions

**Focus on:** [Signals warranting deep dive]
**Monitor:** [Signals warranting ongoing watch]
**Ignore:** [Signals to filter out going forward]
```

## Quality Gates

| Gate | Requirement |
|------|-------------|
| Scope bounded | Not infinite attention |
| Time-limited | Set and enforced time budget |
| Sources documented | Know where signals came from |
| Blind spots acknowledged | What might we miss |
| Triage complete | Every signal classified |

## Anti-Patterns

| Avoid | Problem | Do Instead |
|-------|---------|------------|
| Rabbit holes | Lose scanning breadth | Note and move on |
| No time limit | Scanning never ends | Set and enforce time |
| Completeness obsession | Diminishing returns | Accept sampling |
| No structure | Miss areas | Systematic coverage |
| Ignoring blind spots | False confidence | Acknowledge gaps |
