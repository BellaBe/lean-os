# Webhook Handling

## Webhook Route

```tsx
// app/routes/webhooks.tsx
import type { ActionFunctionArgs } from "@remix-run/node";
import { authenticate } from "~/lib/shopify.server";
import db from "~/lib/db.server";

export async function action({ request }: ActionFunctionArgs) {
  const { topic, shop, session, payload } = await authenticate.webhook(request);

  console.log(`Received ${topic} webhook for ${shop}`);

  switch (topic) {
    case "APP_UNINSTALLED":
      await handleAppUninstalled(shop, session);
      break;

    case "CUSTOMERS_DATA_REQUEST":
      await handleCustomerDataRequest(shop, payload);
      break;

    case "CUSTOMERS_REDACT":
      await handleCustomerRedact(shop, payload);
      break;

    case "SHOP_REDACT":
      await handleShopRedact(shop);
      break;

    // App-specific webhooks
    case "PRODUCTS_UPDATE":
      await handleProductUpdate(shop, payload);
      break;

    case "ORDERS_CREATE":
      await handleOrderCreate(shop, payload);
      break;

    default:
      console.log(`Unhandled webhook topic: ${topic}`);
  }

  // Always return 200 quickly
  return new Response(null, { status: 200 });
}
```

## GDPR Webhook Handlers

### APP_UNINSTALLED

```ts
async function handleAppUninstalled(shop: string, session: any) {
  // Delete session data
  if (session) {
    await db.session.deleteMany({ where: { shop } });
  }

  // Mark shop as uninstalled (don't delete data yet - wait for SHOP_REDACT)
  await db.shop.update({
    where: { domain: shop },
    data: { 
      uninstalledAt: new Date(),
      isActive: false,
    },
  });

  // Cancel any active subscriptions
  // Stop any background jobs for this shop
}
```

### CUSTOMERS_DATA_REQUEST

Respond within 30 days with customer data.

```ts
async function handleCustomerDataRequest(shop: string, payload: any) {
  const { customer, orders_requested } = payload;
  
  // Find all data associated with this customer
  const customerData = await db.customerData.findMany({
    where: {
      shopDomain: shop,
      customerId: customer.id.toString(),
    },
  });

  // Store request for processing
  await db.gdprRequest.create({
    data: {
      type: "DATA_REQUEST",
      shopDomain: shop,
      customerId: customer.id.toString(),
      customerEmail: customer.email,
      payload: JSON.stringify(payload),
      status: "PENDING",
    },
  });

  // Process async - send data to customer/shop
  // You have 30 days to respond
}
```

### CUSTOMERS_REDACT

Delete customer data within 30 days.

```ts
async function handleCustomerRedact(shop: string, payload: any) {
  const { customer, orders_to_redact } = payload;

  // Delete all customer-related data
  await db.customerData.deleteMany({
    where: {
      shopDomain: shop,
      customerId: customer.id.toString(),
    },
  });

  // Log the redaction
  await db.gdprRequest.create({
    data: {
      type: "CUSTOMER_REDACT",
      shopDomain: shop,
      customerId: customer.id.toString(),
      completedAt: new Date(),
      status: "COMPLETED",
    },
  });
}
```

### SHOP_REDACT

Delete ALL shop data within 48 hours.

```ts
async function handleShopRedact(shop: string) {
  // Delete ALL data for this shop
  await db.$transaction([
    db.customerData.deleteMany({ where: { shopDomain: shop } }),
    db.productSync.deleteMany({ where: { shopDomain: shop } }),
    db.orderSync.deleteMany({ where: { shopDomain: shop } }),
    db.appSettings.deleteMany({ where: { shopDomain: shop } }),
    db.session.deleteMany({ where: { shop } }),
    db.shop.delete({ where: { domain: shop } }),
  ]);

  console.log(`Completed shop redact for ${shop}`);
}
```

## Register Webhooks

### In shopify.server.ts

```ts
// app/lib/shopify.server.ts
import { DeliveryMethod } from "@shopify/shopify-app-remix/server";

const shopify = shopifyApp({
  // ... other config
  webhooks: {
    APP_UNINSTALLED: {
      deliveryMethod: DeliveryMethod.Http,
      callbackUrl: "/webhooks",
    },
    CUSTOMERS_DATA_REQUEST: {
      deliveryMethod: DeliveryMethod.Http,
      callbackUrl: "/webhooks",
    },
    CUSTOMERS_REDACT: {
      deliveryMethod: DeliveryMethod.Http,
      callbackUrl: "/webhooks",
    },
    SHOP_REDACT: {
      deliveryMethod: DeliveryMethod.Http,
      callbackUrl: "/webhooks",
    },
    // App-specific webhooks
    PRODUCTS_UPDATE: {
      deliveryMethod: DeliveryMethod.Http,
      callbackUrl: "/webhooks",
    },
    ORDERS_CREATE: {
      deliveryMethod: DeliveryMethod.Http,
      callbackUrl: "/webhooks",
    },
  },
});
```

### Programmatic Registration

```ts
// After OAuth, register webhooks
export async function registerWebhooksForShop(shop: string) {
  const { admin } = await unauthenticated.admin(shop);

  await admin.graphql(`
    mutation webhookSubscriptionCreate($topic: WebhookSubscriptionTopic!, $url: URL!) {
      webhookSubscriptionCreate(
        topic: $topic
        webhookSubscription: {
          callbackUrl: $url
          format: JSON
        }
      ) {
        webhookSubscription { id }
        userErrors { field message }
      }
    }
  `, {
    variables: {
      topic: "PRODUCTS_UPDATE",
      url: `${process.env.SHOPIFY_APP_URL}/webhooks`,
    },
  });
}
```

## App-Specific Webhook Handlers

### PRODUCTS_UPDATE

```ts
async function handleProductUpdate(shop: string, payload: any) {
  const product = payload;

  await db.productSync.upsert({
    where: {
      shopDomain_shopifyProductId: {
        shopDomain: shop,
        shopifyProductId: product.id.toString(),
      },
    },
    update: {
      title: product.title,
      status: product.status,
      updatedAt: new Date(),
    },
    create: {
      shopDomain: shop,
      shopifyProductId: product.id.toString(),
      title: product.title,
      status: product.status,
    },
  });
}
```

### ORDERS_CREATE

```ts
async function handleOrderCreate(shop: string, payload: any) {
  const order = payload;

  // Check if order meets criteria for your app
  const lineItems = order.line_items || [];
  
  // Process order
  await db.order.create({
    data: {
      shopDomain: shop,
      shopifyOrderId: order.id.toString(),
      orderNumber: order.order_number,
      totalPrice: order.total_price,
      createdAt: new Date(order.created_at),
    },
  });

  // Trigger any app-specific logic
  // e.g., send notification, update inventory sync, etc.
}
```

## Async Processing

For heavy operations, respond immediately and process async:

```ts
import { queue } from "~/lib/queue.server";

async function handleOrderCreate(shop: string, payload: any) {
  // Enqueue for async processing
  await queue.add("process-order", {
    shop,
    orderId: payload.id,
  });
  
  // Return immediately - webhook response sent
}
```

## Webhook Verification

The `authenticate.webhook(request)` handles:

1. HMAC signature verification
2. Shop domain extraction
3. Payload parsing

**Never** process webhooks without calling `authenticate.webhook` first.

## Common Webhook Topics

| Topic | Triggered When |
|-------|----------------|
| `APP_UNINSTALLED` | App is uninstalled |
| `PRODUCTS_CREATE` | New product created |
| `PRODUCTS_UPDATE` | Product modified |
| `PRODUCTS_DELETE` | Product deleted |
| `ORDERS_CREATE` | New order placed |
| `ORDERS_UPDATED` | Order modified |
| `ORDERS_PAID` | Order payment completed |
| `ORDERS_FULFILLED` | Order fulfilled |
| `ORDERS_CANCELLED` | Order cancelled |
| `CUSTOMERS_CREATE` | New customer |
| `CUSTOMERS_UPDATE` | Customer modified |
| `INVENTORY_LEVELS_UPDATE` | Inventory changed |
| `FULFILLMENTS_CREATE` | Fulfillment created |

## Testing Webhooks

Use Shopify CLI to trigger test webhooks:

```bash
shopify app webhook trigger --topic PRODUCTS_UPDATE --address http://localhost:3000/webhooks
```

Or use ngrok for local development:

```bash
ngrok http 3000
# Update SHOPIFY_APP_URL to ngrok URL
```