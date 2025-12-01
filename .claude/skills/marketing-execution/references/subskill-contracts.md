# Subskill Contracts

## content-generation

**Input:**
| Parameter | Type | Required |
|-----------|------|----------|
| `campaign_slug` | String | Yes |
| `decision_path` | Path | Yes |
| `piece_name` | String | Yes |
| `loop_trigger_type` | String | Yes |
| `velocity_proof` | String | Yes |

**Output:**
```
drafts/
├── {piece}-article.md
├── {piece}-linkedin.md
├── {piece}-twitter.md
└── {piece}-email.md
```

**Validation:**
- Loop trigger present in each draft
- Velocity proof in content
- Brand voice applied

**Failure:** If loop trigger missing → Reject, do not proceed

---

## content-delivery

**Input:**
| Parameter | Type | Required |
|-----------|------|----------|
| `drafts_path` | Path | Yes |
| `campaign_slug` | String | Yes |
| `channels` | Array | Yes |
| `piece_name` | String | Yes |
| `loop_trigger` | String | Yes |
| `first_comment` | String | Yes (LinkedIn) |

**Output:**
```
artifacts/{slug}/
├── {piece}.md
└── distribution/
    ├── {piece}-linkedin.md
    ├── {piece}-twitter.md
    ├── {piece}-email.md
    └── distribution-metadata.yaml
```

**Post-publish:**
- Loop tracking initiated
- UGC detection active
- Reports in ops/today.md

---

## seo-optimization (Optional)

**Input:**
| Parameter | Type | Required |
|-----------|------|----------|
| `draft_path` | Path | Yes |
| `target_keyword` | String | Yes |
| `secondary_keywords` | Array | No |

**Output:** Overwrites draft with SEO optimizations

**When to invoke:**
- Blog/article content
- Evergreen content
- Explicitly requested

**When to skip:**
- Social-first content
- Time-sensitive content
- Loop mechanics prioritized