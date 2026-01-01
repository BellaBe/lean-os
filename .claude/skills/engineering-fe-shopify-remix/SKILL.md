---
name: shopify-remix
description: Shopify Remix application architecture, routing, data loading, forms, and authentication. Covers route conventions, loader/action patterns, Remix Form with Zod validation, App Bridge integration, webhooks, and session management. Triggers on: Shopify app routes, loaders, actions, form handling, authentication, webhooks, GraphQL mutations.
---

# Shopify Remix Architecture

Build embedded Shopify admin apps with Remix.

## When to Use This Skill

- Creating new app routes (pages, API endpoints)
- Implementing data loading (loaders) or mutations (actions)
- Building forms with validation
- Setting up authentication flows
- Handling webhooks
- Integrating with Shopify GraphQL Admin API

## Project Structure Requirements

```
app/
├─ routes/                    # All routes
├─ components/                # React components
├─ graphql/                   # Queries and mutations
├─ lib/                       # Server utilities
│   ├─ shopify.server.ts      # Shopify app config (REQUIRED)
│   └─ db.server.ts           # Database client
└─ types/                     # TypeScript types
```

## Route Naming Conventions

| Pattern | URL | Use Case |
|---------|-----|----------|
| `_index/route.tsx` | `/` | Entry redirect |
| `app._index/route.tsx` | `/app` | App dashboard |
| `app.{resource}/route.tsx` | `/app/{resource}` | Resource list |
| `app.{resource}.$id/route.tsx` | `/app/{resource}/:id` | Resource detail |
| `app.{resource}_.new/route.tsx` | `/app/{resource}/new` | Escape layout nesting |
| `auth.$/route.tsx` | `/auth/*` | OAuth splat route |
| `webhooks.tsx` | `/webhooks` | Webhook endpoint |

**Rule**: Dot notation creates URL segments. Underscore escapes nesting.

## Route Module Structure

Every route can export:

| Export | Purpose | Required |
|--------|---------|----------|
| `loader` | Fetch data on GET requests | For pages with data |
| `action` | Handle form submissions (POST/PUT/DELETE) | For mutations |
| `default` | React component | For pages with UI |
| `ErrorBoundary` | Error UI | Recommended |

## Authentication Rules

**CRITICAL**: Every loader and action in `/app/*` routes MUST call `authenticate.admin(request)` first.

```ts
const { admin, session } = await authenticate.admin(request);
```

- `admin`: GraphQL client for Shopify Admin API
- `session`: Contains `shop` domain, access token info

**Never** access Shopify APIs without authentication. **Never** trust client-provided shop domains.

## Data Loading (Loaders)

### Decision Tree

```
Need data for the page?
│
├─ Yes → Define loader function
│   │
│   ├─ Need Shopify data? → Use admin.graphql()
│   ├─ Need app database? → Use Prisma/DB client
│   └─ Need both? → Fetch in parallel
│
└─ No → Skip loader (static page)
```

### Rules

1. Always authenticate first
2. Return data with `json()` helper
3. Handle GraphQL errors before returning
4. Filter database queries by `session.shop`

See [references/loaders-actions.md](references/loaders-actions.md) for patterns.

## Mutations (Actions)

### Decision Tree

```
Form submission or mutation?
│
├─ HTML Form → Use action function
│   │
│   ├─ Multiple actions? → Use intent field to switch
│   ├─ Need validation? → Zod schema + safeParse
│   └─ Need Shopify mutation? → admin.graphql()
│
└─ Background job → Use separate API route
```

### Intent Pattern

For routes with multiple actions (edit, delete, duplicate):

1. Include hidden `intent` field in form
2. Switch on intent in action
3. Return appropriate response per intent

See [references/loaders-actions.md](references/loaders-actions.md) for patterns.

## Form Handling

### Architecture

```
┌─────────────────────────────────────────┐
│              Remix Form                  │
├─────────────────────────────────────────┤
│  <Form method="post">                   │
│    └─ Submits to route's action         │
├─────────────────────────────────────────┤
│              Action                      │
├─────────────────────────────────────────┤
│  1. Parse formData                      │
│  2. Validate with Zod                   │
│  3. Execute mutation                    │
│  4. Return result/errors                │
├─────────────────────────────────────────┤
│           useActionData                  │
├─────────────────────────────────────────┤
│  Access action response in component    │
│  Display errors, success states         │
└─────────────────────────────────────────┘
```

### Validation Rules

1. Define Zod schema matching form fields
2. Use `z.coerce` for number/date inputs (forms submit strings)
3. Use `safeParse` (never `parse` — it throws)
4. Return flattened errors: `result.error.flatten().fieldErrors`
5. Check GraphQL `userErrors` after mutations

### Form Component Rules

1. Use Remix `<Form>` component (not HTML `<form>`)
2. Use Polaris form components (TextField, Select, etc.)
3. Access errors via `useActionData()`
4. Show loading state via `useNavigation().state`

See [references/forms.md](references/forms.md) for complete patterns.

## GraphQL Integration

### Query Rules

1. Use variables (never string interpolation)
2. Request only needed fields (cost optimization)
3. Handle pagination for large datasets
4. Check response for errors before using data

### Mutation Rules

1. Always check `userErrors` array in response
2. Return user-friendly error messages
3. Use optimistic UI where appropriate

See [references/graphql-patterns.md](references/graphql-patterns.md) for queries and mutations.

## App Bridge Integration

### Available Features

| Feature | Use Case | Access |
|---------|----------|--------|
| Toast | Success/error notifications | `shopify.toast.show()` |
| Modal | Confirmations, forms | `<Modal>` from app-bridge-react |
| Navigation | Admin navigation | `<NavMenu>` |
| Resource Picker | Select products/collections | `shopify.resourcePicker()` |

### Rules

1. Use App Bridge for notifications (not custom UI)
2. Modals must use App Bridge Modal (not Polaris Modal)
3. Navigation uses NavMenu component

## Webhook Handling

### Required Webhooks (GDPR Compliance)

| Webhook | Purpose | Deadline |
|---------|---------|----------|
| `APP_UNINSTALLED` | Clean up shop data | Immediate |
| `CUSTOMERS_DATA_REQUEST` | Return customer data | 30 days |
| `CUSTOMERS_REDACT` | Delete customer data | 30 days |
| `SHOP_REDACT` | Delete all shop data | 48 hours |

### Webhook Rules

1. Single `/webhooks` route handles all topics
2. Use `authenticate.webhook(request)` for validation
3. Return 200 status quickly (process async if needed)
4. Implement all GDPR webhooks for app store approval

See [references/webhooks.md](references/webhooks.md) for implementation.

## Session Management

### Storage

Use `PrismaSessionStorage` with this schema:

```prisma
model Session {
  id          String    @id
  shop        String
  state       String
  isOnline    Boolean   @default(false)
  scope       String?
  expires     DateTime?
  accessToken String
  userId      BigInt?

  @@index([shop])
}
```

### Security Rules

1. Always filter database queries by `session.shop`
2. Never expose access tokens to client
3. Validate shop domain on every request
4. Handle token expiration gracefully

See [references/auth-patterns.md](references/auth-patterns.md) for OAuth and security.

## Error Handling

### Loader Errors

- Throw `Response` for expected errors (404, 403)
- Let unexpected errors bubble to ErrorBoundary

### Action Errors

- Return validation errors as JSON (400 status)
- Return GraphQL userErrors as JSON
- Redirect on success

### ErrorBoundary

Every route should have ErrorBoundary for graceful degradation.

## Billing Integration

### Billing Models

| Model | Use Case |
|-------|----------|
| Recurring | Fixed monthly/annual subscription |
| Usage-based | Pay per use with capped amount |
| Combined | Base subscription + usage charges |
| One-time | Single purchase for features |

### Decision Tree

```
How should merchants pay?
│
├─ Fixed monthly/yearly fee?
│   └─ Recurring subscription
│
├─ Pay per use (API calls, emails, etc.)?
│   └─ Usage-based subscription
│       ├─ Define terms (e.g., "$0.01 per call")
│       ├─ Set capped amount (max per billing cycle)
│       └─ Create usage records for each charge
│
├─ Base fee + variable usage?
│   └─ Combined subscription
│
└─ One-time feature purchase?
    └─ One-time purchase
```

### Key Rules

1. Only ONE active subscription per merchant per app
2. Usage charges count toward `cappedAmount` limit
3. Test mode (`test: true`) for development stores
4. Store `subscriptionLineItemId` for usage record creation
5. Handle `APP_SUBSCRIPTIONS_UPDATE` webhook for status changes

See [references/billing.md](references/billing.md) for complete implementation.

## Reference Files

| File | Contents |
|------|----------|
| [loaders-actions.md](references/loaders-actions.md) | Loader and action patterns with examples |
| [forms.md](references/forms.md) | Remix Form + Zod validation patterns |
| [graphql-patterns.md](references/graphql-patterns.md) | Query, mutation, pagination patterns |
| [auth-patterns.md](references/auth-patterns.md) | OAuth, scopes, session, security |
| [webhooks.md](references/webhooks.md) | Webhook setup and GDPR compliance |
| [billing.md](references/billing.md) | Subscriptions, usage billing, one-time purchases |
| [performance.md](references/performance.md) | Data loading, GraphQL optimization, caching |