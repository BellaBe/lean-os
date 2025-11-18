# Email Format Detection Methods

## Overview

Systematic methods for detecting and verifying company email patterns for B2B contact research.

## Common Email Patterns

### Pattern 1: firstname.lastname@domain.com (Most Common)

**Usage**: 65% of B2B companies
**Company size**: 50-500 employees
**Examples**:
```
john.smith@acmecorp.com
sarah.johnson@techstartup.com
michael.chen@retailbrand.com
```

**Advantages**:
- Professional standard
- Clear, unambiguous
- Easy to remember
- Scales well

**Detection indicators**:
- Company has >50 employees
- Corporate/professional industry
- IT-managed email (Google Workspace, Microsoft 365)

### Pattern 2: first.last@domain.com (Alternative Dot Pattern)

**Usage**: 15% of B2B companies
**Company size**: 200+ employees
**Examples**:
```
john.smith@enterprise.com
sarah.johnson@bigcorp.com
```

**Advantages**:
- Same as Pattern 1
- Some companies prefer "first" over "firstname" (shorter)

**Detection indicators**:
- Large company (>200 employees)
- Enterprise IT systems
- Formal corporate culture

### Pattern 3: flast@domain.com (First Initial + Last Name)

**Usage**: 10% of B2B companies
**Company size**: 100+ employees
**Examples**:
```
jsmith@company.com
sjohnson@business.com
mchen@startup.com
```

**Advantages**:
- Shorter email addresses
- Reduces collisions (fewer duplicate names)

**Disadvantages**:
- Less professional appearance
- Harder to remember

**Detection indicators**:
- Common last names (Smith, Johnson, etc.)
- Large company (many employees)
- Tech companies (casual culture)

### Pattern 4: firstname@domain.com (First Name Only)

**Usage**: 5% of B2B companies
**Company size**: <50 employees
**Examples**:
```
john@smallco.com
sarah@boutique.com
michael@agency.com
```

**Advantages**:
- Very simple
- Personal/friendly feel
- Works well for small teams

**Disadvantages**:
- Doesn't scale (name collisions)
- Less professional for large companies

**Detection indicators**:
- Small company (<20 employees)
- Creative industry (agency, design, consulting)
- Startup/founder-led

### Pattern 5: firstnamelastinitial@domain.com (First Name + Last Initial)

**Usage**: 3% of B2B companies
**Company size**: Various
**Examples**:
```
johns@company.com
sarahj@business.com
michaelc@startup.com
```

**Advantages**:
- Balances clarity and brevity
- Reduces collisions vs firstname@domain

**Detection indicators**:
- Mid-size company (30-100 employees)
- Casual industry
- Cost-sensitive (shorter = cheaper for some email systems)

### Pattern 6: f.lastname@domain.com (First Initial + Dot + Last Name)

**Usage**: 2% of B2B companies
**Company size**: 100+ employees
**Examples**:
```
j.smith@company.com
s.johnson@business.com
m.chen@startup.com
```

**Advantages**:
- Professional appearance
- Shorter than full first name

**Detection indicators**:
- European companies (common in UK/EU)
- Formal industries (legal, financial)
- Large companies

## Email Pattern Detection Methods

### Method 1: Company Website Contact Page

**Search query**:
```
site:{domain} "contact" OR "about" OR "team"
```

**What to look for**:
- Team page with individual emails
- Contact page with department emails
- Press/media contact emails

**Example findings**:
```
Contact Us page shows:
sales@company.com
john.smith@company.com
sarah.johnson@company.com

Pattern detected: firstname.lastname@domain.com (2 examples)
Confidence: High
```

**Confidence scoring**:
- 2+ individual emails found: **High confidence**
- 1 individual email found: **Medium confidence**
- Only department emails (sales@, info@): **Low confidence** (pattern unclear)

### Method 2: Press Releases and News

**Search query**:
```
"{company name}" "contact" "@{domain}"
```

**What to look for**:
- Press release contact information
- Media inquiry email addresses
- Public relations contact

**Example findings**:
```
Press release shows:
"For media inquiries, contact Sarah Johnson at sarah.johnson@company.com"

Pattern detected: firstname.lastname@domain.com (1 example)
Confidence: Medium
```

**Confidence scoring**:
- Multiple press contacts found: **High confidence**
- Single press contact: **Medium confidence**
- Generic press@ address only: **Low confidence**

### Method 3: Email Signatures in Public Documents

**Search query**:
```
"{domain}" filetype:pdf "@{domain}"
```

**What to look for**:
- Public PDFs with email signatures
- White papers with author emails
- Case studies with client contact info

**Example findings**:
```
White paper shows:
"Written by Michael Chen, michael.chen@company.com"

Pattern detected: firstname.lastname@domain.com
Confidence: Medium
```

**Confidence scoring**:
- Multiple signatures found: **High confidence**
- Single signature: **Medium confidence**
- No signatures found: **N/A**

### Method 4: LinkedIn Email Visibility

**Search query**:
```
site:linkedin.com/in "{company name}" "{title}"
```

**What to look for**:
- LinkedIn profiles with "Contact Info" showing email
- Public profile email addresses
- About section with email

**Example findings**:
```
LinkedIn profile shows:
John Smith - CEO at Company
Contact Info: john.smith@company.com

Pattern detected: firstname.lastname@domain.com
Confidence: High
```

**Confidence scoring**:
- Email visible on LinkedIn profile: **High confidence** (verified person)
- No email visible: **N/A**

**Note**: Most LinkedIn profiles hide email addresses (privacy settings)

### Method 5: Job Postings

**Search query**:
```
site:lever.co OR site:greenhouse.io "{company name}"
```

**What to look for**:
- Application instructions with contact emails
- Recruiter contact information
- Hiring manager emails

**Example findings**:
```
Job posting shows:
"Questions? Contact Sarah Johnson, Recruiting Manager at sarah.johnson@company.com"

Pattern detected: firstname.lastname@domain.com
Confidence: Medium
```

**Confidence scoring**:
- Multiple job postings with emails: **High confidence**
- Single job posting with email: **Medium confidence**
- No contact emails in postings: **N/A**

### Method 6: Social Media Profiles

**Search query**:
```
site:twitter.com "{company name}" OR site:facebook.com "{company name}"
```

**What to look for**:
- Twitter bio with email
- Facebook "About" section with contact info
- Instagram bio with email

**Example findings**:
```
Twitter bio shows:
"Contact: hello@company.com or john.smith@company.com"

Pattern detected: firstname.lastname@domain.com
Confidence: Medium
```

**Confidence scoring**:
- Individual emails in bio: **Medium confidence**
- Generic emails only (info@, hello@): **Low confidence**

## Email Pattern Inference (When No Examples Found)

### Inference Rules Based on Company Size

**Small companies (<50 employees)**:
- **Primary hypothesis**: firstname@domain.com
- **Secondary hypothesis**: firstname.lastname@domain.com
- **Confidence**: Low (unverified)

**Rationale**: Small companies prioritize simplicity, less IT infrastructure

**Medium companies (50-200 employees)**:
- **Primary hypothesis**: firstname.lastname@domain.com
- **Secondary hypothesis**: flast@domain.com
- **Confidence**: Low (unverified)

**Rationale**: Standard corporate pattern, IT-managed email systems

**Large companies (200+ employees)**:
- **Primary hypothesis**: first.last@domain.com
- **Secondary hypothesis**: flast@domain.com
- **Confidence**: Low (unverified)

**Rationale**: Enterprise IT systems, name collision avoidance

### Inference Rules Based on Email System

**Google Workspace indicators**:
- Look for Google Calendar links on website
- Look for Google Meet links in press releases
- Check MX records (dig {domain} MX shows google.com)

**Pattern hypothesis**: firstname.lastname@domain.com (Google Workspace default)
**Confidence**: Low-Medium (system detected, pattern inferred)

**Microsoft 365 indicators**:
- Look for Outlook calendar links
- Look for Teams links in job postings
- Check MX records (shows outlook.com or microsoft.com)

**Pattern hypothesis**: firstname.lastname@domain.com or first.last@domain.com
**Confidence**: Low-Medium (system detected, pattern inferred)

**Custom email server**:
- MX records show custom domain or third-party provider
- No clear indicators of Google/Microsoft

**Pattern hypothesis**: firstname.lastname@domain.com (most common default)
**Confidence**: Low (pure inference)

### Inference Rules Based on Industry

**Tech/SaaS companies**:
- Often use: flast@domain.com or firstname@domain.com (casual culture)
- Sometimes: firstname.lastname@domain.com (if larger)
- **Confidence**: Low (industry pattern, not verified)

**Financial/Legal companies**:
- Almost always: firstname.lastname@domain.com or first.last@domain.com (formal)
- Rarely: flast@domain.com (too casual)
- **Confidence**: Low-Medium (strong industry norm)

**Healthcare companies**:
- Usually: firstname.lastname@domain.com (HIPAA compliance, formal)
- Sometimes: first.last@domain.com
- **Confidence**: Low-Medium (industry norm)

**Retail/E-commerce companies**:
- Varies widely
- Default to: firstname.lastname@domain.com
- **Confidence**: Low (no clear pattern)

## Email Verification Techniques

### Technique 1: SMTP Email Verification (Not Recommended for Privacy)

**Method**: Connect to mail server, check if address exists
**Tools**: Email verification services (Hunter.io, NeverBounce, etc.)

**Pros**: Confirms email exists
**Cons**:
- Privacy invasion
- Often blocked by mail servers
- Can trigger spam filters
- Not recommended without consent

**Use case**: Only after initial outreach attempt (validate bounce reason)

### Technique 2: Pattern Confirmation with Multiple Examples

**Method**: Find 2-3 emails from company, confirm they all use same pattern

**Example**:
```
Found emails:
1. john.smith@company.com (team page)
2. sarah.johnson@company.com (press release)
3. michael.chen@company.com (LinkedIn)

Pattern: firstname.lastname@domain.com
Confidence: High (3 examples, consistent pattern)
```

**Confidence levels**:
- 3+ examples, same pattern: **High confidence**
- 2 examples, same pattern: **High confidence**
- 1 example: **Medium confidence**
- 0 examples: **Low confidence** (inferred)

### Technique 3: Test Email with Opt-Out

**Method**: Send initial outreach email to inferred address with clear opt-out
**Compliance**: CAN-SPAM compliant (business context, opt-out provided)

**Example**:
```
To: john.smith@company.com (inferred pattern)
Subject: Quick question about [company's challenge]

Hi John,

[Personalized message about their company/role]

If this isn't the right email or you'd prefer not to receive this, reply "not interested" and I'll remove you immediately.

Best,
[Your name]
```

**Result handling**:
- Email delivered (no bounce): Pattern likely correct
- Bounce (address not found): Try alternative pattern
- Response received: Pattern confirmed

**Confidence**: Medium (delivered but unconfirmed until response)

## Edge Cases and Special Patterns

### Edge Case 1: Name Collisions (Multiple People, Same Name)

**Pattern variations**:
```
john.smith@company.com → Original
john.smith2@company.com → Second person
johnsmith@company.com → Alternative
j.smith@company.com → Alternative
john.a.smith@company.com → Middle initial
```

**Detection strategy**:
- If multiple profiles with same name on LinkedIn, note in research
- Primary email likely goes to first hired (senior person)
- Alternative patterns hard to predict

**Recommendation**: Start with standard pattern, adjust if bounce

### Edge Case 2: Hyphenated Last Names

**Examples**:
```
Sarah Johnson-Williams:
- sarah.johnson-williams@company.com (keep hyphen)
- sarah.johnsonwilliams@company.com (remove hyphen)
- sarah.johnson@company.com (use first last name only)
```

**Detection strategy**:
- Check if other employees on website have hyphens (pattern consistency)
- Default: Keep hyphen (firstname.lastname@company.com)

**Confidence**: Low-Medium (ambiguous)

### Edge Case 3: Non-English Names

**Examples**:
```
François Dubois:
- francois.dubois@company.com (remove accent)
- françois.dubois@company.com (keep accent, if email supports)
```

**Detection strategy**:
- Most email systems don't support special characters
- Default: Remove accents/special characters
- Keep hyphens (Jean-Luc → jean-luc@company.com)

**Confidence**: Low-Medium (system-dependent)

### Edge Case 4: Nicknames vs Legal Names

**Examples**:
```
LinkedIn shows "Bob Smith" but legal name is "Robert Smith":
- bob.smith@company.com (nickname)
- robert.smith@company.com (legal name)
```

**Detection strategy**:
- Check LinkedIn "About" or headline for full name hints
- Corporate emails usually use legal first name
- Default: Use legal name if known, nickname if not

**Confidence**: Low (ambiguous without verification)

## Output Format for Contact Research

### High Confidence Pattern (Verified)

```csv
email_pattern,pattern_confidence,verification_source
firstname.lastname@domain.com,high,"2 examples found on team page"
```

### Medium Confidence Pattern (Single Example)

```csv
email_pattern,pattern_confidence,verification_source
firstname.lastname@domain.com,medium,"1 example in press release"
```

### Low Confidence Pattern (Inferred)

```csv
email_pattern,pattern_confidence,verification_source
firstname.lastname@domain.com,low,"Inferred from company size (120 employees)"
```

## Email Pattern Quality Checklist

**Before outputting email pattern, verify**:
- [ ] Pattern based on 2+ examples (high confidence) OR
- [ ] Pattern based on 1 example (medium confidence) OR
- [ ] Pattern conservatively inferred from company size (low confidence)
- [ ] Pattern does NOT include creative guesses (no flast@ unless verified)
- [ ] Pattern matches industry norms (financial = formal, tech = varies)
- [ ] Verification source documented (where pattern was detected)
- [ ] Confidence score matches verification strength

**Red flags requiring manual review**:
- Conflicting patterns found (some emails use pattern A, others pattern B)
- No examples found and company size unclear (can't infer)
- Name collisions likely (common name, large company)
- Non-standard characters in name (accents, hyphens)

## Common Mistakes

### Mistake 1: Guessing Creative Patterns

**Wrong**: Assuming flast@domain.com without verification
**Right**: Use firstname.lastname@domain.com as conservative default

**Example**:
- ✗ jsmith@company.com (no evidence)
- ✓ john.smith@company.com (conservative, most common)

### Mistake 2: Assuming Single Pattern for Whole Company

**Wrong**: All employees use same pattern
**Right**: Some companies have multiple patterns (historical changes, acquisitions)

**Example**:
- Old employees: firstname@company.com (legacy)
- New employees: firstname.lastname@company.com (new standard)
- Both patterns may be valid

### Mistake 3: Over-Confidence in Inference

**Wrong**: Marking inferred pattern as "high confidence"
**Right**: Inferred patterns are always "low confidence" (unverified)

**Example**:
- ✗ Inferred firstname.lastname@ from company size → "high confidence"
- ✓ Inferred firstname.lastname@ from company size → "low confidence"

### Mistake 4: Not Checking Recent Examples

**Wrong**: Using 5-year-old press release email pattern
**Right**: Find recent examples (last 1-2 years) - patterns change

**Example**:
- 2019 press release: john@company.com
- 2024 team page: john.smith@company.com
- Use 2024 pattern (company changed email system)
