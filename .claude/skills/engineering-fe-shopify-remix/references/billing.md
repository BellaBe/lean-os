# Shopify Billing API

Charge merchants for app features using subscriptions, usage-based billing, and one-time purchases.

**API Version**: 2025-10

## Billing Models

| Model | Use Case | Mutation |
|-------|----------|----------|
| Recurring | Fixed monthly/annual fee | `appSubscriptionCreate` |
| Usage-based | Pay per use (capped) | `appSubscriptionCreate` + `appUsageRecordCreate` |
| Combined | Base fee + usage charges | `appSubscriptionCreate` with both line items |
| One-time | Single purchase | `appPurchaseOneTimeCreate` |

## Subscription Setup

### Define Plans

```ts
// app/lib/billing/plans.ts
export const PLANS = {
  FREE: {
    name: "Free",
    price: 0,
  },
  STARTER: {
    name: "Starter",
    price: 9.99,
    interval: "EVERY_30_DAYS",
    trialDays: 7,
  },
  PRO: {
    name: "Pro", 
    price: 29.99,
    interval: "EVERY_30_DAYS",
    trialDays: 14,
  },
  ENTERPRISE: {
    name: "Enterprise",
    price: 299.99,
    interval: "ANNUAL",
  },
} as const;

export type PlanName = keyof typeof PLANS;
```

### Create Recurring Subscription

```ts
// app/lib/billing/create-subscription.server.ts
import { authenticate } from "~/lib/shopify.server";

interface CreateSubscriptionParams {
  name: string;
  price: number;
  currencyCode?: string;
  interval?: "EVERY_30_DAYS" | "ANNUAL";
  trialDays?: number;
  returnUrl: string;
  test?: boolean;
}

export async function createRecurringSubscription(
  request: Request,
  params: CreateSubscriptionParams
) {
  const { admin } = await authenticate.admin(request);

  const response = await admin.graphql(`
    mutation AppSubscriptionCreate(
      $name: String!
      $lineItems: [AppSubscriptionLineItemInput!]!
      $returnUrl: URL!
      $trialDays: Int
      $test: Boolean
    ) {
      appSubscriptionCreate(
        name: $name
        returnUrl: $returnUrl
        lineItems: $lineItems
        trialDays: $trialDays
        test: $test
      ) {
        appSubscription {
          id
          status
          createdAt
          currentPeriodEnd
          trialDays
        }
        confirmationUrl
        userErrors {
          field
          message
        }
      }
    }
  `, {
    variables: {
      name: params.name,
      returnUrl: params.returnUrl,
      trialDays: params.trialDays ?? 0,
      test: params.test ?? process.env.NODE_ENV !== "production",
      lineItems: [
        {
          plan: {
            appRecurringPricingDetails: {
              price: {
                amount: params.price,
                currencyCode: params.currencyCode ?? "USD",
              },
              interval: params.interval ?? "EVERY_30_DAYS",
            },
          },
        },
      ],
    },
  });

  const { data } = await response.json();

  if (data.appSubscriptionCreate.userErrors.length > 0) {
    throw new Error(data.appSubscriptionCreate.userErrors[0].message);
  }

  return {
    subscription: data.appSubscriptionCreate.appSubscription,
    confirmationUrl: data.appSubscriptionCreate.confirmationUrl,
  };
}
```

### Create Usage-Based Subscription

```ts
// app/lib/billing/create-usage-subscription.server.ts
export async function createUsageSubscription(
  request: Request,
  params: {
    name: string;
    terms: string;           // e.g., "$0.01 per API call"
    cappedAmount: number;    // Maximum charge per billing period
    returnUrl: string;
  }
) {
  const { admin } = await authenticate.admin(request);

  const response = await admin.graphql(`
    mutation AppSubscriptionCreate(
      $name: String!
      $lineItems: [AppSubscriptionLineItemInput!]!
      $returnUrl: URL!
    ) {
      appSubscriptionCreate(
        name: $name
        returnUrl: $returnUrl
        lineItems: $lineItems
      ) {
        appSubscription {
          id
          lineItems {
            id
            plan {
              pricingDetails {
                __typename
              }
            }
          }
        }
        confirmationUrl
        userErrors {
          field
          message
        }
      }
    }
  `, {
    variables: {
      name: params.name,
      returnUrl: params.returnUrl,
      lineItems: [
        {
          plan: {
            appUsagePricingDetails: {
              terms: params.terms,
              cappedAmount: {
                amount: params.cappedAmount,
                currencyCode: "USD",
              },
            },
          },
        },
      ],
    },
  });

  const { data } = await response.json();

  if (data.appSubscriptionCreate.userErrors.length > 0) {
    throw new Error(data.appSubscriptionCreate.userErrors[0].message);
  }

  // Store the usage line item ID for creating usage records later
  const usageLineItem = data.appSubscriptionCreate.appSubscription.lineItems.find(
    (item: any) => item.plan.pricingDetails.__typename === "AppUsagePricing"
  );

  return {
    subscription: data.appSubscriptionCreate.appSubscription,
    usageLineItemId: usageLineItem?.id,
    confirmationUrl: data.appSubscriptionCreate.confirmationUrl,
  };
}
```

### Create Combined Subscription (Recurring + Usage)

```ts
export async function createCombinedSubscription(
  request: Request,
  params: {
    name: string;
    basePrice: number;
    usageTerms: string;
    usageCappedAmount: number;
    returnUrl: string;
    trialDays?: number;
  }
) {
  const { admin } = await authenticate.admin(request);

  const response = await admin.graphql(`
    mutation AppSubscriptionCreate(
      $name: String!
      $lineItems: [AppSubscriptionLineItemInput!]!
      $returnUrl: URL!
      $trialDays: Int
    ) {
      appSubscriptionCreate(
        name: $name
        returnUrl: $returnUrl
        lineItems: $lineItems
        trialDays: $trialDays
      ) {
        appSubscription {
          id
          lineItems {
            id
            plan {
              pricingDetails {
                __typename
                ... on AppRecurringPricing {
                  price { amount currencyCode }
                  interval
                }
                ... on AppUsagePricing {
                  terms
                  cappedAmount { amount currencyCode }
                  balanceUsed { amount currencyCode }
                }
              }
            }
          }
        }
        confirmationUrl
        userErrors { field message }
      }
    }
  `, {
    variables: {
      name: params.name,
      returnUrl: params.returnUrl,
      trialDays: params.trialDays ?? 0,
      lineItems: [
        {
          plan: {
            appRecurringPricingDetails: {
              price: { amount: params.basePrice, currencyCode: "USD" },
              interval: "EVERY_30_DAYS",
            },
          },
        },
        {
          plan: {
            appUsagePricingDetails: {
              terms: params.usageTerms,
              cappedAmount: { amount: params.usageCappedAmount, currencyCode: "USD" },
            },
          },
        },
      ],
    },
  });

  const { data } = await response.json();
  return data.appSubscriptionCreate;
}
```

## Usage Records

### Create Usage Record

```ts
// app/lib/billing/usage-record.server.ts
export async function createUsageRecord(
  request: Request,
  params: {
    subscriptionLineItemId: string;  // From subscription creation
    amount: number;
    description: string;
    idempotencyKey?: string;         // Prevent duplicate charges
  }
) {
  const { admin } = await authenticate.admin(request);

  const response = await admin.graphql(`
    mutation AppUsageRecordCreate(
      $subscriptionLineItemId: ID!
      $price: MoneyInput!
      $description: String!
      $idempotencyKey: String
    ) {
      appUsageRecordCreate(
        subscriptionLineItemId: $subscriptionLineItemId
        price: $price
        description: $description
        idempotencyKey: $idempotencyKey
      ) {
        appUsageRecord {
          id
          createdAt
          description
          price { amount currencyCode }
          subscriptionLineItem { id }
        }
        userErrors {
          field
          message
        }
      }
    }
  `, {
    variables: {
      subscriptionLineItemId: params.subscriptionLineItemId,
      price: {
        amount: params.amount,
        currencyCode: "USD",
      },
      description: params.description,
      idempotencyKey: params.idempotencyKey,
    },
  });

  const { data } = await response.json();

  if (data.appUsageRecordCreate.userErrors.length > 0) {
    const error = data.appUsageRecordCreate.userErrors[0];
    // Handle capped amount exceeded
    if (error.message.includes("exceeds balance remaining")) {
      throw new Error("USAGE_CAP_EXCEEDED");
    }
    throw new Error(error.message);
  }

  return data.appUsageRecordCreate.appUsageRecord;
}
```

### Usage Tracking Pattern

```ts
// app/lib/billing/usage-tracker.server.ts
import db from "~/lib/db.server";
import { createUsageRecord } from "./usage-record.server";

export async function trackUsage(
  request: Request,
  shopDomain: string,
  event: {
    type: string;       // e.g., "api_call", "email_sent", "image_processed"
    quantity: number;
    unitPrice: number;  // Price per unit
  }
) {
  // Get shop's subscription info
  const shop = await db.shop.findUnique({
    where: { domain: shopDomain },
    select: { usageLineItemId: true },
  });

  if (!shop?.usageLineItemId) {
    throw new Error("No active usage subscription");
  }

  const totalAmount = event.quantity * event.unitPrice;
  const idempotencyKey = `${shopDomain}-${event.type}-${Date.now()}`;

  try {
    const record = await createUsageRecord(request, {
      subscriptionLineItemId: shop.usageLineItemId,
      amount: totalAmount,
      description: `${event.quantity} ${event.type}(s)`,
      idempotencyKey,
    });

    // Log usage for analytics
    await db.usageLog.create({
      data: {
        shopDomain,
        eventType: event.type,
        quantity: event.quantity,
        amount: totalAmount,
        usageRecordId: record.id,
      },
    });

    return record;
  } catch (error) {
    if (error instanceof Error && error.message === "USAGE_CAP_EXCEEDED") {
      // Notify merchant they've hit their cap
      // Could trigger email, in-app notification, etc.
      await notifyCapExceeded(shopDomain);
    }
    throw error;
  }
}
```

## Check Subscription Status

### Get Current Subscription

```ts
// app/lib/billing/get-subscription.server.ts
export async function getCurrentSubscription(request: Request) {
  const { admin, session } = await authenticate.admin(request);

  const response = await admin.graphql(`
    query GetActiveSubscription {
      currentAppInstallation {
        activeSubscriptions {
          id
          name
          status
          createdAt
          currentPeriodEnd
          trialDays
          test
          lineItems {
            id
            plan {
              pricingDetails {
                __typename
                ... on AppRecurringPricing {
                  price { amount currencyCode }
                  interval
                }
                ... on AppUsagePricing {
                  terms
                  cappedAmount { amount currencyCode }
                  balanceUsed { amount currencyCode }
                }
              }
            }
          }
        }
      }
    }
  `);

  const { data } = await response.json();
  const subscriptions = data.currentAppInstallation.activeSubscriptions;

  return subscriptions.length > 0 ? subscriptions[0] : null;
}
```

### Subscription Guard

```ts
// app/lib/billing/require-subscription.server.ts
import { redirect } from "@remix-run/node";
import { getCurrentSubscription } from "./get-subscription.server";

export async function requireActiveSubscription(
  request: Request,
  options?: { 
    allowedPlans?: string[];
    redirectTo?: string;
  }
) {
  const subscription = await getCurrentSubscription(request);

  if (!subscription) {
    throw redirect(options?.redirectTo ?? "/app/billing");
  }

  if (subscription.status !== "ACTIVE") {
    throw redirect(options?.redirectTo ?? "/app/billing");
  }

  if (options?.allowedPlans && !options.allowedPlans.includes(subscription.name)) {
    throw redirect("/app/billing/upgrade");
  }

  return subscription;
}

// Usage in loader
export async function loader({ request }: LoaderFunctionArgs) {
  const subscription = await requireActiveSubscription(request, {
    allowedPlans: ["Pro", "Enterprise"],
  });

  // User has active Pro or Enterprise subscription
  // Continue with loader logic...
}
```

### Check Usage Balance

```ts
export async function getUsageBalance(request: Request) {
  const subscription = await getCurrentSubscription(request);

  if (!subscription) return null;

  const usageLineItem = subscription.lineItems.find(
    (item: any) => item.plan.pricingDetails.__typename === "AppUsagePricing"
  );

  if (!usageLineItem) return null;

  const { cappedAmount, balanceUsed } = usageLineItem.plan.pricingDetails;

  return {
    used: parseFloat(balanceUsed.amount),
    cap: parseFloat(cappedAmount.amount),
    remaining: parseFloat(cappedAmount.amount) - parseFloat(balanceUsed.amount),
    percentUsed: (parseFloat(balanceUsed.amount) / parseFloat(cappedAmount.amount)) * 100,
  };
}
```

## Cancel Subscription

```ts
// app/lib/billing/cancel-subscription.server.ts
export async function cancelSubscription(
  request: Request,
  subscriptionId: string,
  options?: {
    prorate?: boolean;  // Issue prorated refund
  }
) {
  const { admin } = await authenticate.admin(request);

  const response = await admin.graphql(`
    mutation AppSubscriptionCancel($id: ID!, $prorate: Boolean) {
      appSubscriptionCancel(id: $id, prorate: $prorate) {
        appSubscription {
          id
          status
        }
        userErrors {
          field
          message
        }
      }
    }
  `, {
    variables: {
      id: subscriptionId,
      prorate: options?.prorate ?? false,
    },
  });

  const { data } = await response.json();

  if (data.appSubscriptionCancel.userErrors.length > 0) {
    throw new Error(data.appSubscriptionCancel.userErrors[0].message);
  }

  return data.appSubscriptionCancel.appSubscription;
}
```

## Update Usage Cap

```ts
export async function updateUsageCap(
  request: Request,
  lineItemId: string,
  newCappedAmount: number
) {
  const { admin } = await authenticate.admin(request);

  const response = await admin.graphql(`
    mutation AppSubscriptionLineItemUpdate(
      $id: ID!
      $cappedAmount: MoneyInput!
    ) {
      appSubscriptionLineItemUpdate(
        id: $id
        cappedAmount: $cappedAmount
      ) {
        appSubscriptionLineItem {
          id
          plan {
            pricingDetails {
              ... on AppUsagePricing {
                cappedAmount { amount currencyCode }
              }
            }
          }
        }
        userErrors { field message }
      }
    }
  `, {
    variables: {
      id: lineItemId,
      cappedAmount: { amount: newCappedAmount, currencyCode: "USD" },
    },
  });

  const { data } = await response.json();
  return data.appSubscriptionLineItemUpdate;
}
```

## One-Time Purchase

```ts
export async function createOneTimePurchase(
  request: Request,
  params: {
    name: string;
    price: number;
    returnUrl: string;
  }
) {
  const { admin } = await authenticate.admin(request);

  const response = await admin.graphql(`
    mutation AppPurchaseOneTimeCreate(
      $name: String!
      $price: MoneyInput!
      $returnUrl: URL!
    ) {
      appPurchaseOneTimeCreate(
        name: $name
        price: $price
        returnUrl: $returnUrl
        test: ${process.env.NODE_ENV !== "production"}
      ) {
        appPurchaseOneTime {
          id
          status
          createdAt
        }
        confirmationUrl
        userErrors { field message }
      }
    }
  `, {
    variables: {
      name: params.name,
      price: { amount: params.price, currencyCode: "USD" },
      returnUrl: params.returnUrl,
    },
  });

  const { data } = await response.json();
  return data.appPurchaseOneTimeCreate;
}
```

## Billing Webhooks

### Register Webhooks

```ts
// In shopify.server.ts webhooks config
webhooks: {
  APP_SUBSCRIPTIONS_UPDATE: {
    deliveryMethod: DeliveryMethod.Http,
    callbackUrl: "/webhooks",
  },
  APP_SUBSCRIPTIONS_APPROACHING_CAPPED_AMOUNT: {
    deliveryMethod: DeliveryMethod.Http,
    callbackUrl: "/webhooks",
  },
  APP_PURCHASES_ONE_TIME_UPDATE: {
    deliveryMethod: DeliveryMethod.Http,
    callbackUrl: "/webhooks",
  },
}
```

### Handle Billing Webhooks

```ts
// In webhooks.tsx action
case "APP_SUBSCRIPTIONS_UPDATE": {
  const { app_subscription } = payload;
  
  await db.shop.update({
    where: { domain: shop },
    data: {
      subscriptionId: app_subscription.admin_graphql_api_id,
      subscriptionStatus: app_subscription.status,
      currentPeriodEnd: new Date(app_subscription.current_period_end),
    },
  });
  
  // Handle status changes
  if (app_subscription.status === "CANCELLED") {
    await handleSubscriptionCancelled(shop);
  } else if (app_subscription.status === "ACTIVE") {
    await handleSubscriptionActivated(shop);
  }
  break;
}

case "APP_SUBSCRIPTIONS_APPROACHING_CAPPED_AMOUNT": {
  // Merchant is at 90% of usage cap
  await sendUsageWarningEmail(shop, payload);
  break;
}

case "APP_PURCHASES_ONE_TIME_UPDATE": {
  const { app_purchase_one_time } = payload;
  
  if (app_purchase_one_time.status === "ACTIVE") {
    // Purchase approved - grant access
    await grantPurchasedFeature(shop, app_purchase_one_time);
  }
  break;
}
```

## Billing Route Example

```tsx
// app/routes/app.billing/route.tsx
import { json, redirect, type LoaderFunctionArgs, type ActionFunctionArgs } from "@remix-run/node";
import { Form, useLoaderData } from "@remix-run/react";
import { Page, Card, BlockStack, Text, Button, Banner } from "@shopify/polaris";
import { authenticate } from "~/lib/shopify.server";
import { getCurrentSubscription } from "~/lib/billing/get-subscription.server";
import { createRecurringSubscription } from "~/lib/billing/create-subscription.server";
import { PLANS } from "~/lib/billing/plans";

export async function loader({ request }: LoaderFunctionArgs) {
  await authenticate.admin(request);
  const subscription = await getCurrentSubscription(request);

  return json({ subscription, plans: PLANS });
}

export async function action({ request }: ActionFunctionArgs) {
  const { session } = await authenticate.admin(request);
  const formData = await request.formData();
  const planName = formData.get("plan") as string;

  const plan = PLANS[planName as keyof typeof PLANS];
  if (!plan || plan.price === 0) {
    return json({ error: "Invalid plan" }, { status: 400 });
  }

  const { confirmationUrl } = await createRecurringSubscription(request, {
    name: plan.name,
    price: plan.price,
    interval: plan.interval,
    trialDays: plan.trialDays,
    returnUrl: `${process.env.SHOPIFY_APP_URL}/app/billing/callback`,
  });

  return redirect(confirmationUrl);
}

export default function BillingPage() {
  const { subscription, plans } = useLoaderData<typeof loader>();

  return (
    <Page title="Billing">
      {subscription ? (
        <Card>
          <BlockStack gap="200">
            <Text as="h2" variant="headingMd">Current Plan: {subscription.name}</Text>
            <Text>Status: {subscription.status}</Text>
            <Text>Renews: {new Date(subscription.currentPeriodEnd).toLocaleDateString()}</Text>
          </BlockStack>
        </Card>
      ) : (
        <BlockStack gap="400">
          <Banner title="No active subscription">
            Choose a plan to get started.
          </Banner>

          {Object.entries(plans).map(([key, plan]) => (
            plan.price > 0 && (
              <Card key={key}>
                <BlockStack gap="200">
                  <Text as="h2" variant="headingMd">{plan.name}</Text>
                  <Text>${plan.price}/{plan.interval === "ANNUAL" ? "year" : "month"}</Text>
                  {plan.trialDays && <Text tone="subdued">{plan.trialDays} day free trial</Text>}
                  <Form method="post">
                    <input type="hidden" name="plan" value={key} />
                    <Button submit variant="primary">Subscribe</Button>
                  </Form>
                </BlockStack>
              </Card>
            )
          ))}
        </BlockStack>
      )}
    </Page>
  );
}
```

## Subscription Status Reference

| Status | Description |
|--------|-------------|
| `PENDING` | Awaiting merchant approval |
| `ACTIVE` | Active and billing |
| `DECLINED` | Merchant declined |
| `EXPIRED` | Billing period ended |
| `FROZEN` | Payment failed, grace period |
| `CANCELLED` | Cancelled by app or merchant |

## Pricing Intervals

| Interval | Description |
|----------|-------------|
| `EVERY_30_DAYS` | Monthly billing |
| `ANNUAL` | Yearly billing |

## Best Practices

1. **Always use test mode** in development: `test: true`
2. **Store subscription IDs** in your database for quick lookups
3. **Handle webhook events** to stay in sync with Shopify
4. **Use idempotency keys** for usage records to prevent duplicates
5. **Gracefully handle cap exceeded** errors
6. **Provide upgrade paths** when users hit limits
7. **Show usage stats** so merchants understand their billing