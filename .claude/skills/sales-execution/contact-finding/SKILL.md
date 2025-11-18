---
name: contact-finding
description: Identify decision-maker contacts at target companies using web research for LinkedIn queries, email patterns, and phone research methods based on ICP buyer personas
allowed-tools: [Read, Write, WebSearch]
---

# Contact-Finding Subskill

## Purpose

Identify decision-makers at target companies and provide contact research strategy (LinkedIn queries, email patterns, phone research methods) based on ICP buyer personas.

**Operates on**: ONE product per invocation
**Input**: Qualified prospect list + ICP buyer personas
**Output**: Contact research strategy with LinkedIn queries, email patterns, phone methods

## Context

- Reads from: `research/customer/prospects/[segment]-prospects-{date}.csv` (target companies)
- Reads from: `research/customer/icp/[segment]-icp.md` (personas - decision-maker titles)
- Writes to: `research/customer/prospects/[segment]-contacts-{date}.csv`
- Uses WebSearch for LinkedIn discovery, email pattern detection, phone research

## Key Workflows

### 1. Load Target Companies

**Read prospect list**:
- Company names and domains from prospect CSV
- Filter by `rows` parameter (default: 1-20)
- Priority: Research Tier 1 prospects first

**Read ICP personas**:
- Extract buyer personas section from ICP YAML
- Identify decision-maker titles by buyer type:
  - Economic buyer (budget authority)
  - Technical buyer (evaluation authority)
  - End user (implementation user)
- Map persona focus parameter to titles

**Example** (GlamYouUp):
```yaml
buyer_personas:
  economic_buyer:
    - Founder/CEO
    - CFO
    - CMO
  technical_buyer:
    - Ecommerce Director
    - Head of Operations
  end_user:
    - Customer Service Manager
    - Returns Coordinator
```

### 2. Identify Decision-Maker Titles

**Per company, determine target titles**:

**If persona_focus = "economic"**:
- Target only economic buyer titles
- Example: Founder, CFO, CMO

**If persona_focus = "technical"**:
- Target only technical buyer titles
- Example: Ecommerce Director, Head of Operations

**If persona_focus = "end_user"**:
- Target only end user titles
- Example: Customer Service Manager

**If persona_focus = "all"** (default):
- Start with economic buyer (primary)
- Add technical buyer if product requires technical evaluation
- Optionally add end user for product-led growth

**Prioritization**:
1. Economic buyer first (budget authority)
2. Technical buyer second (if product is technical)
3. End user third (for PLG or bottoms-up)

### 3. Research Contacts

**For each company + title combination**:

#### LinkedIn Search Strategy

**Primary pattern**:
```
site:linkedin.com/in "{company name}" "{title}"
```

**Examples**:
```
site:linkedin.com/in "ChicThreads" "Founder"
site:linkedin.com/in "ChicThreads" "CMO"
site:linkedin.com/in "TrendyStyles" "Ecommerce Director"
```

**Verification indicators** (look for in search results):
- Current position at target company
- Recent LinkedIn activity (posted/commented in last 90 days)
- Profile completeness (photo, headline, experience)
- Connection count (500+ = active user)

**Confidence scoring**:
- **High**: Multiple matching profiles, recent activity, complete profiles
- **Medium**: 1-2 matching profiles, some activity
- **Low**: No clear matches, incomplete profiles, inactive accounts

#### Email Pattern Detection

**Pattern discovery methods**:

1. **Company website contact page**:
```
site:{domain} "contact" OR "team" OR "about"
```

2. **Public email signatures**:
```
"{domain}" "email" "@{domain}"
```

3. **Press releases or news**:
```
"{company name}" "contact" "@{domain}"
```

**Common B2B patterns**:
- `firstname.lastname@domain.com` (most common)
- `first.last@domain.com`
- `flast@domain.com`
- `firstnamel@domain.com`
- `firstname@domain.com` (small companies)

**Pattern verification**:
- If you find 2+ emails with same pattern → **High confidence**
- If you find 1 email showing pattern → **Medium confidence**
- If no emails found, infer from company size:
  - <50 employees: firstname@domain.com
  - 50-200 employees: firstname.lastname@domain.com
  - >200 employees: first.last@domain.com or flast@domain.com
  - **Low confidence** for inferred patterns

#### Phone Research Methods

**Phone discovery strategy**:

1. **Company website**:
```
site:{domain} "phone" OR "call" OR "contact us"
```

2. **LinkedIn company page**:
```
site:linkedin.com/company "{company name}"
```
Look for: Company phone number in About section

3. **Industry directories**:
- Chamber of Commerce listings
- Professional association directories
- Regulatory databases (for regulated industries)

**Phone research output**:
- Document WHERE to find phone (company page, LinkedIn, directory)
- Do NOT include actual phone numbers (privacy)
- Note: "Company phone: {source}", "LinkedIn profile: {person name}"

**Confidence scoring**:
- **High**: Company phone on website, LinkedIn profile shows contact info
- **Medium**: Company phone only (no direct line)
- **Low**: No phone found, will need outbound discovery call

### 4. Output Contact Report

**CSV structure**:
```csv
company_name,domain,target_title,buyer_persona,linkedin_search_query,email_pattern,phone_research_method,confidence
```

**Example rows**:
```csv
ChicThreads,chicthreads.com,Founder,economic,"site:linkedin.com/in ""ChicThreads"" ""Founder""",firstname.lastname@chicthreads.com,Company website contact page,high
ChicThreads,chicthreads.com,CMO,economic,"site:linkedin.com/in ""ChicThreads"" ""CMO""",firstname.lastname@chicthreads.com,Company website contact page,medium
TrendyStyles,trendystyles.com,Ecommerce Director,technical,"site:linkedin.com/in ""TrendyStyles"" ""Ecommerce Director""",first.last@trendystyles.com,LinkedIn company page,high
```

**Confidence calculation**:
- **High**: LinkedIn high + Email high + Phone high/medium
- **Medium**: LinkedIn medium or Email medium or Phone low
- **Low**: LinkedIn low or Email low or Phone not found

## Input Parameters

**Required**:
- `product`: Product name (e.g., "GlamYouUp", "Detekta")
- `prospect_list_path`: Path to prospect CSV (default: `research/customer/prospects/{segment}-prospects-{date}.csv`, use most recent)
- `icp_path`: Path to ICP (default: `research/customer/icp/{segment}-icp.md`)

**Optional**:
- `rows`: Which prospects to research (default: "1-20")
  - "1-10": First 10 prospects
  - "1-50": First 50 prospects
  - "all": All prospects (use with caution for large lists)
- `persona_focus`: Which buyer personas to target (default: "all")
  - "economic": Economic buyers only (Founder, CFO, CMO)
  - "technical": Technical buyers only (CTO, VP Eng, Head of Ops)
  - "end_user": End users only (Manager, Coordinator)
  - "all": All personas (prioritize economic, then technical, then end user)

## Output

**File**: `research/customer/prospects/{segment}-contacts-{date}.csv`

**Columns**:
1. **company_name**: Target company name
2. **domain**: Company domain
3. **target_title**: Decision-maker title to search for
4. **buyer_persona**: economic/technical/end_user
5. **linkedin_search_query**: Exact LinkedIn search query to run
6. **email_pattern**: Detected or inferred email format
7. **phone_research_method**: Where to find phone (source description)
8. **confidence**: high/medium/low (overall contact research confidence)

## Web Search Patterns

### LinkedIn Discovery

**Pattern 1: Title-based search**:
```
site:linkedin.com/in "{company name}" "{title}"
```

**Pattern 2: Seniority-based search** (if title yields no results):
```
site:linkedin.com/in "{company name}" "Director"
site:linkedin.com/in "{company name}" "VP"
site:linkedin.com/in "{company name}" "Head of"
```

**Pattern 3: Department-based search**:
```
site:linkedin.com/in "{company name}" "Marketing"
site:linkedin.com/in "{company name}" "Operations"
site:linkedin.com/in "{company name}" "Finance"
```

### Email Pattern Detection

**Pattern 1: Direct contact page**:
```
site:{domain} "contact" OR "team"
```

**Pattern 2: About/Team page**:
```
site:{domain} "about" OR "our team"
```

**Pattern 3: Press/Media page**:
```
site:{domain} "press" OR "media" OR "news"
```

**Pattern 4: Public email signatures**:
```
"{domain}" "@{domain}"
```

### Phone Research

**Pattern 1: Contact page**:
```
site:{domain} "phone" OR "call us"
```

**Pattern 2: LinkedIn company page**:
```
site:linkedin.com/company "{company name}"
```

**Pattern 3: Business directories**:
```
"{company name}" "phone" OR "contact"
```

## Contact Research Strategy

### Priority Order (Pete Kazanjy Method)

1. **LinkedIn first** (most reliable for B2B):
   - Current employment verification
   - Profile activity indicates engagement
   - Direct messaging capability (for Sales Navigator users)
   - Connection requests as outreach channel

2. **Email pattern second** (primary outreach channel):
   - Verify pattern from company website/public sources
   - If unverifiable, use conservative inferred pattern
   - Avoid guessing (use email validation tools if needed)

3. **Phone third** (supplementary, critical per Kazanjy):
   - Company phone as starting point
   - Ask for decision-maker by name/title
   - LinkedIn profile contact info (if available)
   - Direct line research (post-connection)

### Verification Best Practices

**Before outputting contact**:
- ✓ LinkedIn profile shows current position at target company
- ✓ Email pattern verified by 2+ examples OR is conservative inference
- ✓ Phone research method documented (even if "not found")
- ✓ Confidence score reflects weakest link in contact research

**Red flags requiring manual review**:
- No LinkedIn profiles found for any target title
- Email pattern conflicts (multiple patterns detected)
- No company contact information available (phone/email)
- All confidence scores "low"

### Company Size Adjustments

**Small companies (<50 employees)**:
- Focus on Founder/CEO (often wears multiple hats)
- Email: firstname@domain.com (simpler patterns)
- Phone: Company phone likely reaches decision-maker directly
- LinkedIn: Founder very active, high response rate

**Medium companies (50-200 employees)**:
- Multiple decision-makers (CFO, CMO, CTO separate)
- Email: firstname.lastname@domain.com (standard corporate)
- Phone: Receptionist/gatekeeper, ask for specific person
- LinkedIn: Mix of active/inactive profiles

**Large companies (200+ employees)**:
- Complex hierarchy, multiple approvers
- Email: first.last@domain.com or flast@domain.com (IT-managed)
- Phone: Complex phone tree, direct lines hard to find
- LinkedIn: High profile count, many inactive profiles

## Constraints

### Decision-Maker Title Mapping

**Must map to ICP personas**:
- All target titles must appear in ICP buyer personas section
- If title not in ICP, do not research (out of scope)
- If ICP has no personas, return error (ICP incomplete)

**Example validation**:
```yaml
# ICP has these personas:
buyer_personas:
  economic_buyer: [Founder, CFO]
  technical_buyer: [CTO]

# Valid targets: Founder, CFO, CTO
# Invalid targets: COO, CMO (not in ICP)
```

### Email Pattern Verification

**Verified patterns** (high/medium confidence):
- Found 2+ emails with same pattern on company website
- Found 1 email with pattern in press release/news
- Pattern confirmed by email verification tool

**Inferred patterns** (low confidence):
- No emails found, inferred from company size
- Must use conservative pattern (firstname.lastname@domain.com)
- Never guess creative patterns (flast@, f.lastname@, etc.)

### Phone Research (Privacy)

**Allowed**:
- Document WHERE to find phone (source)
- General company phone from website
- LinkedIn profile shows "contact info available"

**Not allowed**:
- Direct phone numbers in CSV (privacy violation)
- Personal mobile numbers
- Unsolicited phone list scraping

**Output format**:
```csv
phone_research_method
"Company website contact page"
"LinkedIn company page"
"Not found - will need discovery call"
```

### LinkedIn Query Specificity

**Must be specific**:
- Include company name AND title in query
- Use exact match quotes: "Company Name" "Title"
- Use site:linkedin.com/in for profile search

**Examples**:
```
✓ site:linkedin.com/in "ChicThreads" "Founder"
✓ site:linkedin.com/in "TrendyStyles" "CMO"
✗ "CMO fashion" (too broad)
✗ site:linkedin.com "Ecommerce Director" (no company)
```

## Error Handling

**No prospects found**:
- Check prospect_list_path exists
- Check rows parameter is valid range
- Return error: "No prospects found in {path} for rows {rows}"

**No personas in ICP**:
- Check icp_path has buyer_personas section
- Return error: "ICP missing buyer_personas section"

**Invalid persona_focus**:
- Check parameter is one of: economic, technical, end_user, all
- Return error: "Invalid persona_focus: {value}. Must be: economic, technical, end_user, or all"

**No contacts found for company**:
- Document in CSV with confidence: "low"
- phone_research_method: "Not found - manual research needed"
- linkedin_search_query: Still provide query to run manually

## Quality Validation

**Before finalizing CSV, verify**:
- [ ] All companies from prospect list (rows range) are included
- [ ] All target titles map to ICP buyer personas
- [ ] LinkedIn queries use correct syntax (site:linkedin.com/in)
- [ ] Email patterns are verified or conservatively inferred
- [ ] Phone research methods documented (even if "not found")
- [ ] Confidence scores calculated correctly
- [ ] No actual phone numbers in CSV (only methods)

**Output review**:
- Total contacts researched: {count}
- High confidence: {count} ({percent}%)
- Medium confidence: {count} ({percent}%)
- Low confidence: {count} ({percent}%)
- Companies with no contacts found: {list}

## References

See `references/` directory for:
- `contact-patterns.md`: Decision-maker titles by industry and product type
- `email-format-detection.md`: Common email patterns and detection methods
- `phone-research-methods.md`: Where to find phone numbers, when to call
