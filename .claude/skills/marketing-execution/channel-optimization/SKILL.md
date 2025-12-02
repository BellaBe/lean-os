---
name: channel-optimization
description: Optimize acquisition channels based on GTM motion. Use when improving app store listing, LinkedIn profile, SEO, or any active channel. Reads 15.go-to-market.md to activate relevant modules. One skill, multiple channel modules.
allowed-tools: "Read,Write,WebSearch,WebFetch,Bash"
---

# Channel Optimization

Optimize the channels that matter for your GTM motion.

## Core Principle

One skill, multiple modules. Activates based on what `15.go-to-market.md` declares.

## Prerequisites

**Required:**

| File | Purpose | If Missing |
|------|---------|------------|
| `strategy/canvas/15.go-to-market.md` | Channels | Cannot proceed |

**Recommended:**

| File | Purpose |
|------|---------|
| `artifacts/marketing/narrative/brand-voice.md` | Voice for copy |
| `artifacts/marketing/narrative/positioning.md` | Messaging |

## Module Activation

```python
gtm = read("strategy/canvas/15.go-to-market.md")

active = []
for channel in gtm.channels:
    if "shopify" in channel: active.append("shopify-app-store")
    elif "chrome" in channel: active.append("chrome-web-store")
    elif channel in ["blog", "seo"]: active.append("web-seo")
    elif "linkedin" in channel: active.append("linkedin")
    elif channel in ["outbound", "sales"]: active.append("sales-channels")
    elif "email" in channel: active.append("email")
```

Only active modules load.

---

## Module: Shopify App Store

**Active when:** Channel includes Shopify

### Listing

| Element | Spec | Best Practice |
|---------|------|---------------|
| Title | 30 chars | Keyword + benefit |
| Tagline | 70 chars | Value prop |
| Description | 2,500 chars | Benefits → Features → Proof |
| Screenshots | 4-6 | Before/after, UI, results |
| Video | 60 sec | Value demo |

### Keywords

| Type | Count | Placement |
|------|-------|-----------|
| Primary | 1-2 | Title, first paragraph |
| Secondary | 3-5 | Tagline, body |
| Long-tail | 5-10 | Throughout |

### Screenshots

| # | Purpose |
|---|---------|
| 1 | Hero — value prop |
| 2 | Before/after |
| 3 | Key feature |
| 4 | Results |
| 5 | Setup ease |

### Reviews

**Triggers:**

| Event | Timing | Type |
|-------|--------|------|
| First value | +48h | Soft |
| 10 values | +24h | Direct |
| Revenue attributed | +24h | Celebration |
| 30 days | Day 30 | Summary |

**Response SLA:** 24 hours

### Ranking Factors

| Factor | Weight |
|--------|--------|
| Install velocity | High |
| Rating | High |
| Review count | Medium |
| Uninstall rate | High |

### Metrics

```yaml
weekly: [installs, uninstalls, rating, reviews, rankings]
monthly: [trends, sentiment, competitors]
```

### Output

```
artifacts/marketing/channels/shopify-app-store/
├── listing.md
├── keywords.md
├── screenshots.md
├── review-prompts.md
├── review-responses.md
└── performance.md
```

---

## Module: Chrome Web Store

**Active when:** Channel includes Chrome

### Listing

| Element | Spec |
|---------|------|
| Name | 45 chars |
| Summary | 132 chars |
| Description | First 2 lines key |

### Images

| Type | Size |
|------|------|
| Screenshots | 1280x800 |
| Small promo | 440x280 |
| Large promo | 920x680 |

### Chrome-Specific

- Category affects discovery
- Privacy disclosure required
- Review: 1-3 days

### Output

```
artifacts/marketing/channels/chrome-web-store/
├── listing.md
├── keywords.md
└── performance.md
```

---

## Module: Web SEO

**Active when:** Channel includes blog/SEO

**Note:** Lower priority per distribution physics. Optimize if easy.

### On-Page

| Element | Spec |
|---------|------|
| Title | Keyword, 50-60 chars |
| Meta | 150-160 chars |
| H1 | One, with keyword |
| H2s | 3-7 with variations |
| First 100 words | Include keyword |
| Internal links | 3-5 |

### Content Brief

```markdown
**Keyword:** {keyword}
**Intent:** {type}
**Word count:** {count}

**Include:**
- Keyword in title, H1, first 100 words
- {X} H2 sections
- {X} internal links
```

### Technical

| Check | Target |
|-------|--------|
| Page speed | >90 |
| Mobile | Pass |
| Crawlability | Check |

### Metrics

```yaml
weekly: [rankings, sessions, CTR]
monthly: [changes, new keywords, backlinks]
```

### Output

```
artifacts/marketing/channels/web-seo/
├── keyword-strategy.md
├── content-briefs/
└── performance.md
```

---

## Module: LinkedIn

**Active when:** Founder LinkedIn is channel

### Profile

| Element | Best Practice |
|---------|---------------|
| Headline | What + for whom + result |
| About | Problem → Solution → Proof → CTA |
| Featured | Top 3 content |
| Experience | Narrative |
| Banner | Positioning |

### Posting

| Factor | Recommendation |
|--------|----------------|
| Frequency | 3-5x/week |
| Timing | Morning/lunch |
| Length | 800-1,200 chars |
| Hook | First 2 lines grab |

### Engagement

| Action | Timing |
|--------|--------|
| First comment | Within 5 min |
| Reply to comments | Within 2 hours |
| Engage others | Before/after posting |

### Content Mix

| Type | % |
|------|---|
| Insights | 40% |
| How-to | 30% |
| Stories | 20% |
| Wins | 10% |

### Metrics

```yaml
weekly: [engagement, comments, DMs, views]
monthly: [growth, reach, quality]
```

### Output

```
artifacts/marketing/channels/linkedin/
├── profile.md
├── content-themes.md
└── performance.md
```

---

## Module: Sales Channels

**Active when:** Motion is SLG

### Portal Structure

```
sales-portal/
├── case-studies/
├── one-pagers/
├── battle-cards/
├── sequences/
├── decks/
└── calculators/
```

### Findability

- Clear naming
- Search/filter
- Recently used
- Stage recommendations

### Metrics

```yaml
weekly: [usage by piece, usage by rep]
monthly: [pipeline influenced, win rate impact]
```

### Output

```
artifacts/marketing/channels/sales/
├── portal-structure.md
├── content-inventory.md
└── performance.md
```

---

## Module: Email

**Active when:** Email is channel

### List Health

| Factor | Action |
|--------|--------|
| Segmentation | By stage, persona |
| Hygiene | Remove bounces, 90d inactive |
| Preferences | Let subscribers choose |

### Performance

| Metric | Target |
|--------|--------|
| Open | >25% |
| Click | >3% |
| Unsubscribe | <0.5% |

### Deliverability

- SPF, DKIM, DMARC
- Warm up domains
- Monitor complaints
- Clean regularly

### Output

```
artifacts/marketing/channels/email/
├── segments.md
├── sequences/
├── templates/
└── performance.md
```

---

## Execution Flow

1. **Read GTM** — Get channels, priorities
2. **Activate modules** — Only declared channels
3. **Assess** — Current state vs best practice
4. **Prioritize** — By investment level
5. **Execute** — Module-specific optimization
6. **Track** — Channel-appropriate metrics

## Output

```
artifacts/marketing/channels/
├── {channel}/
│   └── {files}
└── channel-overview.md
```

## Boundaries

**DO:**
- Read GTM first
- Only optimize declared channels
- Track appropriate metrics
- Prioritize by investment

**DON'T:**
- Optimize undeclared channels
- Same tactics everywhere
- Track vanity metrics
- Over-invest in low priority
