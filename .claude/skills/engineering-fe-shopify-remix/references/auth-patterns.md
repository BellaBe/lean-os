# Authentication Patterns

## OAuth Flow Overview

```
┌─────────────────────────────────────────────────────────────┐
│                      OAuth 2.0 Flow                         │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  1. Merchant clicks "Install" in Shopify Admin              │
│                         │                                   │
│                         ▼                                   │
│  2. Redirect to your /auth endpoint                         │
│                         │                                   │
│                         ▼                                   │
│  3. Your app redirects to Shopify OAuth screen              │
│     (shopify.com/admin/oauth/authorize)                     │
│                         │                                   │
│                         ▼                                   │
│  4. Merchant approves scopes                                │
│                         │                                   │
│                         ▼                                   │
│  5. Shopify redirects to /auth/callback with code           │
│                         │                                   │
│                         ▼                                   │
│  6. Your app exchanges code for access token                │
│                         │                                   │
│                         ▼                                   │
│  7. Store session, register webhooks, redirect to /app      │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

## Auth Route Setup

### Entry Point Redirect

```tsx
// app/routes/_index/route.tsx
import type { LoaderFunctionArgs } from "@remix-run/node";
import { redirect } from "@remix-run/node";
import { login } from "~/lib/shopify.server";

export async function loader({ request }: LoaderFunctionArgs) {
  const url = new URL(request.url);
  
  // Check if this is an embedded app request
  if (url.searchParams.get("embedded") === "1") {
    return redirect("/app");
  }

  // Otherwise, start OAuth
  return login(request);
}
```

### OAuth Callback Handler

```tsx
// app/routes/auth.$/route.tsx
import type { LoaderFunctionArgs } from "@remix-run/node";
import { authenticate } from "~/lib/shopify.server";

export async function loader({ request }: LoaderFunctionArgs) {
  // Handles the entire OAuth flow
  await authenticate.admin(request);
  return null;
}
```

## Scopes

### Common Scope Combinations

```bash
# Read-only app
SCOPES=read_products,read_orders,read_customers

# Product management app
SCOPES=read_products,write_products,read_inventory,write_inventory

# Order management app
SCOPES=read_orders,write_orders,read_customers,read_products

# Full-featured app
SCOPES=read_products,write_products,read_orders,write_orders,read_customers,write_customers,read_inventory,write_inventory

# Analytics app
SCOPES=read_analytics,read_orders,read_products,read_customers

# Marketing app
SCOPES=read_marketing_events,write_marketing_events,read_customers
```

### Scope Reference

| Scope | Access |
|-------|--------|
| `read_products` | Product, variant, collection data |
| `write_products` | Create, update, delete products |
| `read_orders` | Order data (excludes sensitive payment info) |
| `write_orders` | Create, update, cancel orders |
| `read_customers` | Customer data |
| `write_customers` | Create, update customers |
| `read_inventory` | Inventory levels and locations |
| `write_inventory` | Adjust inventory |
| `read_fulfillments` | Fulfillment data |
| `write_fulfillments` | Create fulfillments |
| `read_shipping` | Shipping zones and rates |
| `write_shipping` | Manage shipping |
| `read_analytics` | Store analytics |
| `read_reports` | Store reports |

## Session Types

### Offline Sessions (Recommended for Apps)

```ts
// Stored in database, persists across browser sessions
// Best for: background jobs, webhooks, server-side operations

const shopify = shopifyApp({
  // ... config
  sessionStorage: new PrismaSessionStorage(prisma),
  // Offline by default
});
```

### Online Sessions

```ts
// Tied to specific user session
// Best for: user-specific permissions, audit trails

export async function loader({ request }: LoaderFunctionArgs) {
  const { admin, session } = await authenticate.admin(request);
  
  // session.onlineAccessInfo contains user data
  const userId = session.onlineAccessInfo?.associated_user?.id;
}
```

## Access Token Management

### Retrieve Token for Background Jobs

```ts
// app/lib/shopify-client.server.ts
import { unauthenticated } from "~/lib/shopify.server";

export async function getShopifyClientForShop(shop: string) {
  const { admin } = await unauthenticated.admin(shop);
  return admin;
}

// Usage in a job/cron
export async function syncProductsJob(shop: string) {
  const admin = await getShopifyClientForShop(shop);
  
  const response = await admin.graphql(`
    query {
      products(first: 100) {
        edges {
          node { id title }
        }
      }
    }
  `);
  
  // Process products...
}
```

### Token Refresh

Shopify handles token refresh automatically for offline sessions. For online sessions, you may need to re-authenticate.

```ts
export async function loader({ request }: LoaderFunctionArgs) {
  try {
    const { admin, session } = await authenticate.admin(request);
    // Use admin...
  } catch (error) {
    if (error instanceof Response && error.status === 401) {
      // Token expired or invalid, redirect to OAuth
      throw redirect("/auth");
    }
    throw error;
  }
}
```

## Multi-Tenant Security

### Always Filter by Shop

```ts
// CORRECT: Filter by shop domain
const products = await db.product.findMany({
  where: { shopDomain: session.shop },
});

// WRONG: No shop filter - security vulnerability!
const products = await db.product.findMany();
```

### Session Validation Middleware

```ts
// app/lib/middleware.server.ts
export async function requireAuth(request: Request) {
  const { admin, session } = await authenticate.admin(request);
  
  // Verify session belongs to active shop
  const shop = await db.shop.findUnique({
    where: { domain: session.shop },
  });
  
  if (!shop || shop.status !== "active") {
    throw redirect("/auth");
  }
  
  return { admin, session, shop };
}
```

## Embedded vs Non-Embedded

### Embedded App (Default)

```tsx
// app/root.tsx
import { AppProvider } from "@shopify/shopify-app-remix/react";
import polarisStyles from "@shopify/polaris/build/esm/styles.css?url";

export const links = () => [{ rel: "stylesheet", href: polarisStyles }];

export default function App() {
  return (
    <html>
      <head>
        <Meta />
        <Links />
      </head>
      <body>
        <AppProvider isEmbeddedApp apiKey={ENV.SHOPIFY_API_KEY}>
          <Outlet />
        </AppProvider>
        <Scripts />
      </body>
    </html>
  );
}
```

### Detect Embedded Context

```tsx
import { useAppBridge } from "@shopify/app-bridge-react";

export function useIsEmbedded() {
  try {
    const app = useAppBridge();
    return !!app;
  } catch {
    return false;
  }
}
```

## App Proxy Authentication

For requests through Shopify's app proxy:

```ts
// app/routes/proxy.$.tsx
import type { LoaderFunctionArgs } from "@remix-run/node";
import { authenticate } from "~/lib/shopify.server";

export async function loader({ request }: LoaderFunctionArgs) {
  // Validates signature from Shopify proxy
  const { session, storefront } = await authenticate.public.appProxy(request);
  
  // storefront client for Storefront API
  // session for shop context
}
```

## Extension Authentication

For Shopify extensions (checkout, post-purchase):

```ts
// app/routes/extensions.$.tsx
import type { ActionFunctionArgs } from "@remix-run/node";
import { authenticate } from "~/lib/shopify.server";

export async function action({ request }: ActionFunctionArgs) {
  const { sessionToken, cors } = await authenticate.public.checkout(request);
  
  // Verify the session token
  const decodedToken = await verifySessionToken(sessionToken);
  
  return cors(json({ success: true }));
}
```

## Billing and Subscriptions

### App Subscription Check

```ts
// app/lib/billing.server.ts
import { authenticate } from "~/lib/shopify.server";

export async function requireActiveSubscription(request: Request) {
  const { admin, session, billing } = await authenticate.admin(request);
  
  const { hasActivePayment } = await billing.check({
    plans: ["Pro", "Enterprise"],
    isTest: process.env.NODE_ENV !== "production",
  });
  
  if (!hasActivePayment) {
    // Redirect to billing page or show upgrade prompt
    throw redirect("/app/billing");
  }
  
  return { admin, session };
}
```

### Create Subscription

```ts
// app/routes/app.billing/route.tsx
export async function action({ request }: ActionFunctionArgs) {
  const { billing } = await authenticate.admin(request);
  
  await billing.request({
    plan: "Pro",
    isTest: process.env.NODE_ENV !== "production",
    returnUrl: `${process.env.SHOPIFY_APP_URL}/app/billing/callback`,
  });
}
```

## Security Checklist

- [ ] Access tokens encrypted at rest (Prisma handles via session storage)
- [ ] HTTPS enforced for all endpoints
- [ ] HMAC validation for webhooks (handled by `authenticate.webhook`)
- [ ] State parameter validated in OAuth (handled by Shopify library)
- [ ] Shop domain validated before processing
- [ ] All database queries filtered by shop
- [ ] Sensitive data not logged
- [ ] Rate limiting implemented for API calls
- [ ] Session expiry handled gracefully
- [ ] GDPR webhooks implemented and tested