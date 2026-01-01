# Shopify Remix Performance

## Data Loading Optimization

### Parallel Loading

```tsx
// ❌ SLOW: Sequential fetches
export async function loader({ request }: LoaderFunctionArgs) {
  const { admin } = await authenticate.admin(request);
  
  const products = await admin.graphql(`query { products(first: 10) { ... } }`);
  const orders = await admin.graphql(`query { orders(first: 10) { ... } }`);  // Waits
  const customers = await admin.graphql(`query { customers(first: 10) { ... } }`);  // Waits
  
  return json({ products, orders, customers });
}

// ✅ FAST: Parallel fetches
export async function loader({ request }: LoaderFunctionArgs) {
  const { admin } = await authenticate.admin(request);
  
  const [productsRes, ordersRes, customersRes] = await Promise.all([
    admin.graphql(`query { products(first: 10) { ... } }`),
    admin.graphql(`query { orders(first: 10) { ... } }`),
    admin.graphql(`query { customers(first: 10) { ... } }`),
  ]);
  
  const [products, orders, customers] = await Promise.all([
    productsRes.json(),
    ordersRes.json(),
    customersRes.json(),
  ]);
  
  return json({ products: products.data, orders: orders.data, customers: customers.data });
}
```

### Defer Non-Critical Data

```tsx
import { defer } from "@remix-run/node";
import { Await, useLoaderData } from "@remix-run/react";
import { Suspense } from "react";

export async function loader({ request }: LoaderFunctionArgs) {
  const { admin } = await authenticate.admin(request);
  
  // Critical data - await immediately
  const productsRes = await admin.graphql(`query { products(first: 10) { ... } }`);
  const products = await productsRes.json();
  
  // Non-critical - defer for streaming
  const analyticsPromise = admin.graphql(`query { ... }`).then(r => r.json());
  
  return defer({
    products: products.data.products,
    analytics: analyticsPromise,
  });
}

export default function Dashboard() {
  const { products, analytics } = useLoaderData<typeof loader>();
  
  return (
    <Page>
      {/* Renders immediately */}
      <ProductList products={products} />
      
      {/* Streams in when ready */}
      <Suspense fallback={<AnalyticsSkeleton />}>
        <Await resolve={analytics}>
          {(data) => <AnalyticsChart data={data} />}
        </Await>
      </Suspense>
    </Page>
  );
}
```

## GraphQL Optimization

### Request Only Needed Fields

```tsx
// ❌ BAD: Over-fetching
const response = await admin.graphql(`
  query {
    products(first: 50) {
      edges {
        node {
          id
          title
          description
          descriptionHtml
          handle
          status
          totalInventory
          vendor
          productType
          tags
          images(first: 10) { ... }
          variants(first: 100) { ... }
          metafields(first: 50) { ... }
        }
      }
    }
  }
`);

// ✅ GOOD: Only what's needed for the list view
const response = await admin.graphql(`
  query {
    products(first: 50) {
      edges {
        node {
          id
          title
          status
          totalInventory
          featuredImage {
            url(transform: { maxWidth: 100 })
          }
        }
      }
    }
  }
`);
```

### Use Image Transforms

```tsx
// Let Shopify resize images server-side
const response = await admin.graphql(`
  query {
    product(id: $id) {
      featuredImage {
        # Request specific size
        url(transform: { maxWidth: 400, maxHeight: 400, crop: CENTER })
      }
      images(first: 10) {
        edges {
          node {
            # Thumbnail for gallery
            thumbnail: url(transform: { maxWidth: 100 })
            # Full size for modal
            full: url(transform: { maxWidth: 1200 })
          }
        }
      }
    }
  }
`);
```

### Pagination Best Practices

```tsx
// Use cursor-based pagination (more efficient than offset)
const response = await admin.graphql(`
  query GetProducts($first: Int!, $after: String) {
    products(first: $first, after: $after) {
      pageInfo {
        hasNextPage
        endCursor
      }
      edges {
        cursor
        node {
          id
          title
        }
      }
    }
  }
`, {
  variables: { first: 20, after: cursor },
});

// Don't fetch huge pages
// ✅ first: 20-50
// ❌ first: 250 (max, but slow)
```

### Query Cost Management

```tsx
// Shopify limits query cost to 1000 points per request
// Check cost in response:
const response = await admin.graphql(`...`);
const { extensions } = await response.json();
console.log('Query cost:', extensions.cost);

// Expensive operations:
// - Deep nesting (products → variants → metafields)
// - Large first/last values
// - Multiple connections

// Split expensive queries
// ❌ One huge query
query {
  products(first: 100) {
    variants(first: 100) {
      metafields(first: 20) { ... }
    }
  }
}

// ✅ Separate queries or bulk operations
```

## Caching Strategies

### Loader Caching

```tsx
import { json } from "@remix-run/node";

export async function loader({ request }: LoaderFunctionArgs) {
  const { admin } = await authenticate.admin(request);
  
  const data = await fetchData(admin);
  
  return json(data, {
    headers: {
      // Cache for 60 seconds, revalidate in background
      "Cache-Control": "private, max-age=60, stale-while-revalidate=300",
    },
  });
}
```

### App-Level Caching

```tsx
// app/lib/cache.server.ts
const cache = new Map<string, { data: any; expiry: number }>();

export async function cachedFetch<T>(
  key: string,
  fetcher: () => Promise<T>,
  ttlSeconds: number = 60
): Promise<T> {
  const now = Date.now();
  const cached = cache.get(key);
  
  if (cached && cached.expiry > now) {
    return cached.data as T;
  }
  
  const data = await fetcher();
  cache.set(key, { data, expiry: now + ttlSeconds * 1000 });
  
  return data;
}

// Usage
export async function loader({ request }: LoaderFunctionArgs) {
  const { admin, session } = await authenticate.admin(request);
  
  const products = await cachedFetch(
    `products:${session.shop}`,
    () => fetchProducts(admin),
    300  // 5 minutes
  );
  
  return json({ products });
}
```

### Session Storage Optimization

```ts
// Use indexed queries for session lookups
model Session {
  id          String   @id
  shop        String
  // ...
  
  @@index([shop])  // Fast lookups by shop
}
```

## Bundle Optimization

### Dynamic Imports

```tsx
// ❌ BAD: Large component loaded on every page
import { RichTextEditor } from "~/components/RichTextEditor";

// ✅ GOOD: Load only when needed
const RichTextEditor = lazy(() => import("~/components/RichTextEditor"));

export default function ProductEdit() {
  return (
    <Suspense fallback={<EditorSkeleton />}>
      <RichTextEditor />
    </Suspense>
  );
}
```

### Route-Based Splitting

Remix automatically code-splits by route. Keep routes focused:

```
routes/
├─ app._index/        # Dashboard (light)
├─ app.products/      # Product list (medium)
├─ app.products.$id/  # Product detail (heavier - has editor)
└─ app.analytics/     # Analytics (charts - load separately)
```

### Tree Shaking

```tsx
// ❌ BAD: Imports entire library
import { format, parse, add, sub, formatDistance } from "date-fns";

// ✅ GOOD: Import only what's used
import { format } from "date-fns/format";
import { formatDistance } from "date-fns/formatDistance";

// ❌ BAD: Entire Polaris
import * as Polaris from "@shopify/polaris";

// ✅ GOOD: Named imports (tree-shakeable)
import { Page, Card, Button } from "@shopify/polaris";
```

## Asset Optimization

### Polaris CSS

```tsx
// app/root.tsx
import polarisStyles from "@shopify/polaris/build/esm/styles.css?url";

export const links: LinksFunction = () => [
  { rel: "stylesheet", href: polarisStyles },
];
```

### Image Handling

```tsx
// Use Shopify CDN transforms
function ProductImage({ image }: { image: ShopifyImage }) {
  return (
    <img
      src={image.url}
      srcSet={`
        ${image.url}&width=400 400w,
        ${image.url}&width=800 800w,
        ${image.url}&width=1200 1200w
      `}
      sizes="(max-width: 640px) 100vw, 50vw"
      loading="lazy"
      alt={image.altText || "Product image"}
    />
  );
}
```

## Bulk Operations

For large data sets, use bulk operations instead of paginated queries:

```tsx
// Start bulk operation
const bulkOp = await admin.graphql(`
  mutation {
    bulkOperationRunQuery(
      query: """
        {
          products {
            edges {
              node {
                id
                title
                variants {
                  edges {
                    node {
                      id
                      sku
                      inventoryQuantity
                    }
                  }
                }
              }
            }
          }
        }
      """
    ) {
      bulkOperation {
        id
        status
      }
      userErrors { field message }
    }
  }
`);

// Poll for completion
const status = await admin.graphql(`
  query {
    currentBulkOperation {
      id
      status
      url  # JSONL file URL when complete
    }
  }
`);

// Download and process JSONL
if (status.data.currentBulkOperation.status === "COMPLETED") {
  const response = await fetch(status.data.currentBulkOperation.url);
  const lines = (await response.text()).split('\n');
  const products = lines.filter(Boolean).map(JSON.parse);
}
```

## Webhook Processing

### Async Processing

```tsx
// ❌ BAD: Process inline (blocks webhook response)
export async function action({ request }: ActionFunctionArgs) {
  const { payload } = await authenticate.webhook(request);
  
  await heavyProcessing(payload);  // Slow!
  
  return new Response(null, { status: 200 });
}

// ✅ GOOD: Queue for async processing
export async function action({ request }: ActionFunctionArgs) {
  const { topic, shop, payload } = await authenticate.webhook(request);
  
  // Quick enqueue
  await queue.add("process-webhook", { topic, shop, payload });
  
  // Return immediately
  return new Response(null, { status: 200 });
}
```

## Performance Checklist

### Data Loading
- [ ] Parallel fetch with Promise.all
- [ ] Defer non-critical data
- [ ] Paginate large lists (20-50 items)
- [ ] Cache expensive queries

### GraphQL
- [ ] Request only needed fields
- [ ] Use image transforms
- [ ] Monitor query costs
- [ ] Use bulk operations for large exports

### Bundle
- [ ] Dynamic import heavy components
- [ ] Tree-shake imports
- [ ] Analyze bundle size

### Assets
- [ ] Lazy load images below fold
- [ ] Use Shopify CDN transforms
- [ ] Optimize Polaris CSS

### Webhooks
- [ ] Process async (queue)
- [ ] Return 200 immediately
- [ ] Idempotent handlers