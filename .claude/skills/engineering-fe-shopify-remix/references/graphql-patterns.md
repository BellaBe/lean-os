# GraphQL Patterns

## Query Basics

### Simple Query

```ts
const response = await admin.graphql(`
  query {
    shop {
      name
      email
      myshopifyDomain
    }
  }
`);

const { data } = await response.json();
// data.shop.name, data.shop.email, etc.
```

### Query with Variables

```ts
const response = await admin.graphql(`
  query getProduct($id: ID!) {
    product(id: $id) {
      id
      title
      status
    }
  }
`, {
  variables: {
    id: "gid://shopify/Product/123456789",
  },
});
```

### Multiple Resources

```ts
const response = await admin.graphql(`
  query getDashboardData {
    products(first: 5) {
      edges {
        node {
          id
          title
        }
      }
    }
    orders(first: 5) {
      edges {
        node {
          id
          name
          totalPriceSet {
            shopMoney {
              amount
            }
          }
        }
      }
    }
    shop {
      currencyCode
    }
  }
`);
```

## Pagination

### Cursor-Based Pagination

```ts
// app/lib/shopify-queries.server.ts
export async function getAllProducts(admin: AdminApiContext["admin"]) {
  const products: Product[] = [];
  let hasNextPage = true;
  let cursor: string | null = null;

  while (hasNextPage) {
    const response = await admin.graphql(`
      query getProducts($first: Int!, $after: String) {
        products(first: $first, after: $after) {
          pageInfo {
            hasNextPage
            endCursor
          }
          edges {
            node {
              id
              title
              status
              totalInventory
            }
          }
        }
      }
    `, {
      variables: {
        first: 50,
        after: cursor,
      },
    });

    const { data } = await response.json();
    const { pageInfo, edges } = data.products;

    products.push(...edges.map((edge: any) => edge.node));
    hasNextPage = pageInfo.hasNextPage;
    cursor = pageInfo.endCursor;
  }

  return products;
}
```

### Pagination in Loader

```tsx
// app/routes/app.products/route.tsx
export async function loader({ request }: LoaderFunctionArgs) {
  const { admin } = await authenticate.admin(request);
  const url = new URL(request.url);
  const cursor = url.searchParams.get("cursor");

  const response = await admin.graphql(`
    query getProducts($first: Int!, $after: String) {
      products(first: $first, after: $after) {
        pageInfo {
          hasNextPage
          hasPreviousPage
          startCursor
          endCursor
        }
        edges {
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

  const { data } = await response.json();

  return json({
    products: data.products.edges.map((e: any) => e.node),
    pageInfo: data.products.pageInfo,
  });
}
```

## Mutations

### Create Resource

```ts
const response = await admin.graphql(`
  mutation createProduct($input: ProductInput!) {
    productCreate(input: $input) {
      product {
        id
        title
        handle
      }
      userErrors {
        field
        message
      }
    }
  }
`, {
  variables: {
    input: {
      title: "New Product",
      descriptionHtml: "<p>Product description</p>",
      vendor: "My Store",
      productType: "Accessories",
      tags: ["new", "featured"],
      variants: [{
        price: "29.99",
        sku: "SKU-001",
        inventoryManagement: "SHOPIFY",
        inventoryQuantities: [{
          availableQuantity: 100,
          locationId: "gid://shopify/Location/123",
        }],
      }],
    },
  },
});

const { data } = await response.json();

if (data.productCreate.userErrors.length > 0) {
  throw new Error(data.productCreate.userErrors[0].message);
}

return data.productCreate.product;
```

### Update Resource

```ts
const response = await admin.graphql(`
  mutation updateProduct($input: ProductInput!) {
    productUpdate(input: $input) {
      product {
        id
        title
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
    input: {
      id: "gid://shopify/Product/123456789",
      title: "Updated Title",
      status: "ACTIVE",
    },
  },
});
```

### Delete Resource

```ts
const response = await admin.graphql(`
  mutation deleteProduct($input: ProductDeleteInput!) {
    productDelete(input: $input) {
      deletedProductId
      userErrors {
        field
        message
      }
    }
  }
`, {
  variables: {
    input: {
      id: "gid://shopify/Product/123456789",
    },
  },
});
```

## Metafields

### Read Metafields

```ts
const response = await admin.graphql(`
  query getProductWithMetafields($id: ID!) {
    product(id: $id) {
      id
      title
      metafields(first: 20) {
        edges {
          node {
            id
            namespace
            key
            value
            type
          }
        }
      }
    }
  }
`, {
  variables: { id: productId },
});
```

### Set Metafields

```ts
const response = await admin.graphql(`
  mutation setMetafields($metafields: [MetafieldsSetInput!]!) {
    metafieldsSet(metafields: $metafields) {
      metafields {
        id
        namespace
        key
        value
      }
      userErrors {
        field
        message
      }
    }
  }
`, {
  variables: {
    metafields: [
      {
        ownerId: "gid://shopify/Product/123456789",
        namespace: "custom",
        key: "my_field",
        value: "my value",
        type: "single_line_text_field",
      },
      {
        ownerId: "gid://shopify/Product/123456789",
        namespace: "custom",
        key: "rating",
        value: "4.5",
        type: "number_decimal",
      },
    ],
  },
});
```

### Delete Metafield

```ts
const response = await admin.graphql(`
  mutation deleteMetafield($input: MetafieldDeleteInput!) {
    metafieldDelete(input: $input) {
      deletedId
      userErrors {
        field
        message
      }
    }
  }
`, {
  variables: {
    input: {
      id: "gid://shopify/Metafield/123456789",
    },
  },
});
```

## Bulk Operations

### Start Bulk Query

```ts
const response = await admin.graphql(`
  mutation bulkOperationRunQuery($query: String!) {
    bulkOperationRunQuery(query: $query) {
      bulkOperation {
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
    query: `
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
                    price
                  }
                }
              }
            }
          }
        }
      }
    `,
  },
});
```

### Poll Bulk Operation Status

```ts
const response = await admin.graphql(`
  query getBulkOperation($id: ID!) {
    node(id: $id) {
      ... on BulkOperation {
        id
        status
        errorCode
        objectCount
        url
      }
    }
  }
`, {
  variables: { id: bulkOperationId },
});

const { data } = await response.json();
const operation = data.node;

if (operation.status === "COMPLETED") {
  // Download results from operation.url
  const results = await fetch(operation.url);
  // Results are JSONL format (one JSON object per line)
}
```

### Bulk Mutation

```ts
const response = await admin.graphql(`
  mutation bulkOperationRunMutation($mutation: String!, $stagedUploadPath: String!) {
    bulkOperationRunMutation(
      mutation: $mutation
      stagedUploadPath: $stagedUploadPath
    ) {
      bulkOperation {
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
    mutation: `
      mutation updateInventory($input: InventorySetQuantitiesInput!) {
        inventorySetQuantities(input: $input) {
          userErrors {
            field
            message
          }
        }
      }
    `,
    stagedUploadPath: "uploaded-file-path",
  },
});
```

## Inventory Management

### Get Inventory Levels

```ts
const response = await admin.graphql(`
  query getInventoryLevels($inventoryItemId: ID!) {
    inventoryItem(id: $inventoryItemId) {
      id
      inventoryLevels(first: 10) {
        edges {
          node {
            id
            available
            location {
              id
              name
            }
          }
        }
      }
    }
  }
`, {
  variables: { inventoryItemId },
});
```

### Adjust Inventory

```ts
const response = await admin.graphql(`
  mutation adjustInventory($input: InventoryAdjustQuantitiesInput!) {
    inventoryAdjustQuantities(input: $input) {
      changes {
        name
        delta
      }
      userErrors {
        field
        message
      }
    }
  }
`, {
  variables: {
    input: {
      reason: "correction",
      name: "available",
      changes: [{
        inventoryItemId: "gid://shopify/InventoryItem/123",
        locationId: "gid://shopify/Location/456",
        delta: 10,
      }],
    },
  },
});
```

## Orders

### Get Order Details

```ts
const response = await admin.graphql(`
  query getOrder($id: ID!) {
    order(id: $id) {
      id
      name
      email
      totalPriceSet {
        shopMoney {
          amount
          currencyCode
        }
      }
      lineItems(first: 50) {
        edges {
          node {
            id
            title
            quantity
            originalUnitPriceSet {
              shopMoney {
                amount
              }
            }
            variant {
              id
              sku
            }
          }
        }
      }
      shippingAddress {
        address1
        city
        province
        country
        zip
      }
      fulfillments {
        id
        status
        trackingInfo {
          number
          url
        }
      }
    }
  }
`, {
  variables: { id: orderId },
});
```

### Create Fulfillment

```ts
const response = await admin.graphql(`
  mutation createFulfillment($fulfillment: FulfillmentV2Input!) {
    fulfillmentCreateV2(fulfillment: $fulfillment) {
      fulfillment {
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
    fulfillment: {
      lineItemsByFulfillmentOrder: [{
        fulfillmentOrderId: "gid://shopify/FulfillmentOrder/123",
        fulfillmentOrderLineItems: [{
          id: "gid://shopify/FulfillmentOrderLineItem/456",
          quantity: 1,
        }],
      }],
      trackingInfo: {
        number: "1Z999AA10123456784",
        url: "https://tracking.example.com/1Z999AA10123456784",
        company: "UPS",
      },
    },
  },
});
```

## Error Handling

### Handle GraphQL Errors

```ts
export async function safeGraphQL<T>(
  admin: AdminApiContext["admin"],
  query: string,
  variables?: Record<string, unknown>
): Promise<{ data: T | null; errors: string[] }> {
  try {
    const response = await admin.graphql(query, { variables });
    const result = await response.json();

    // GraphQL-level errors
    if (result.errors?.length > 0) {
      return {
        data: null,
        errors: result.errors.map((e: any) => e.message),
      };
    }

    // Check for userErrors in mutation results
    const mutationKey = Object.keys(result.data || {}).find(
      key => result.data[key]?.userErrors
    );

    if (mutationKey && result.data[mutationKey].userErrors.length > 0) {
      return {
        data: null,
        errors: result.data[mutationKey].userErrors.map(
          (e: any) => `${e.field?.join(".")}: ${e.message}`
        ),
      };
    }

    return { data: result.data as T, errors: [] };
  } catch (error) {
    return {
      data: null,
      errors: [error instanceof Error ? error.message : "Unknown error"],
    };
  }
}
```

### Rate Limiting

```ts
// Check rate limit headers
const response = await admin.graphql(query);
const costHeader = response.headers.get("X-Shopify-Shop-Api-Call-Limit");
// e.g., "125/1000" - current/max

// Parse cost
const [current, max] = costHeader?.split("/").map(Number) || [0, 1000];
const remainingBudget = max - current;

// If low on budget, add delay
if (remainingBudget < 100) {
  await new Promise(resolve => setTimeout(resolve, 1000));
}
```

### Retry with Backoff

```ts
export async function graphqlWithRetry(
  admin: AdminApiContext["admin"],
  query: string,
  variables?: Record<string, unknown>,
  maxRetries = 3
) {
  for (let attempt = 1; attempt <= maxRetries; attempt++) {
    try {
      const response = await admin.graphql(query, { variables });

      // Check for throttling
      if (response.status === 429) {
        const retryAfter = parseInt(response.headers.get("Retry-After") || "1");
        await new Promise(resolve => 
          setTimeout(resolve, retryAfter * 1000)
        );
        continue;
      }

      return response;
    } catch (error) {
      if (attempt === maxRetries) throw error;

      // Exponential backoff
      const delay = Math.pow(2, attempt) * 1000 + Math.random() * 1000;
      await new Promise(resolve => setTimeout(resolve, delay));
    }
  }
}
```

## Query Cost Optimization

### Request Only Needed Fields

```ts
// BAD: Requesting everything
query {
  products(first: 100) {
    edges {
      node {
        id
        title
        description
        descriptionHtml
        handle
        vendor
        productType
        tags
        status
        # ... many more fields
      }
    }
  }
}

// GOOD: Only what you need
query {
  products(first: 100) {
    edges {
      node {
        id
        title
        status
      }
    }
  }
}
```

### Use Fragments for Reuse

```ts
const PRODUCT_FIELDS = `
  fragment ProductFields on Product {
    id
    title
    status
    totalInventory
    priceRangeV2 {
      minVariantPrice {
        amount
        currencyCode
      }
    }
  }
`;

const response = await admin.graphql(`
  ${PRODUCT_FIELDS}
  
  query getProducts($first: Int!) {
    products(first: $first) {
      edges {
        node {
          ...ProductFields
        }
      }
    }
  }
`, {
  variables: { first: 20 },
});
```

### Batch Related Queries

```ts
// Instead of multiple round trips
const shop = await admin.graphql(`query { shop { name } }`);
const products = await admin.graphql(`query { products(first: 5) { ... } }`);

// Combine into one request
const response = await admin.graphql(`
  query getDashboard {
    shop { name currencyCode }
    products(first: 5) { edges { node { id title } } }
    orders(first: 5) { edges { node { id name } } }
  }
`);
```