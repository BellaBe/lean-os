# Loaders and Actions Reference

## Loader Patterns

### Basic Loader with GraphQL

```tsx
// app/routes/app.products/route.tsx
import { json, type LoaderFunctionArgs } from "@remix-run/node";
import { useLoaderData } from "@remix-run/react";
import { authenticate } from "~/lib/shopify.server";

export async function loader({ request }: LoaderFunctionArgs) {
  const { admin, session } = await authenticate.admin(request);

  const response = await admin.graphql(`
    query getProducts($first: Int!) {
      products(first: $first) {
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
    variables: { first: 20 },
  });

  const { data } = await response.json();

  return json({
    products: data.products.edges.map((edge: any) => edge.node),
    shop: session.shop,
  });
}

export default function ProductsPage() {
  const { products, shop } = useLoaderData<typeof loader>();
  // Render with Polaris components
}
```

### Loader with URL Parameters

```tsx
// app/routes/app.products.$id/route.tsx
export async function loader({ request, params }: LoaderFunctionArgs) {
  const { admin } = await authenticate.admin(request);
  const { id } = params;

  const response = await admin.graphql(`
    query getProduct($id: ID!) {
      product(id: $id) {
        id
        title
        descriptionHtml
        status
        variants(first: 100) {
          edges {
            node {
              id
              title
              price
            }
          }
        }
      }
    }
  `, {
    variables: { id: `gid://shopify/Product/${id}` },
  });

  const { data } = await response.json();

  if (!data.product) {
    throw new Response("Product not found", { status: 404 });
  }

  return json({ product: data.product });
}
```

### Loader with App Database

```tsx
export async function loader({ request }: LoaderFunctionArgs) {
  const { session } = await authenticate.admin(request);

  // Always filter by shop!
  const settings = await db.appSettings.findUnique({
    where: { shopDomain: session.shop },
  });

  return json({ settings });
}
```

### Parallel Data Fetching

```tsx
export async function loader({ request }: LoaderFunctionArgs) {
  const { admin, session } = await authenticate.admin(request);

  // Fetch Shopify data and app data in parallel
  const [shopifyResponse, appData] = await Promise.all([
    admin.graphql(`query { shop { name currencyCode } }`),
    db.appSettings.findUnique({ where: { shopDomain: session.shop } }),
  ]);

  const { data } = await shopifyResponse.json();

  return json({
    shop: data.shop,
    settings: appData,
  });
}
```

## Action Patterns

### Basic Create Action

```tsx
// app/routes/app.products.new/route.tsx
import { json, redirect, type ActionFunctionArgs } from "@remix-run/node";
import { authenticate } from "~/lib/shopify.server";
import { z } from "zod";

const createSchema = z.object({
  title: z.string().min(1, "Title is required"),
  description: z.string().optional(),
  price: z.coerce.number().positive("Price must be positive"),
});

export async function action({ request }: ActionFunctionArgs) {
  const { admin } = await authenticate.admin(request);
  const formData = await request.formData();
  const rawData = Object.fromEntries(formData);

  // Validate
  const result = createSchema.safeParse(rawData);
  if (!result.success) {
    return json(
      { errors: result.error.flatten().fieldErrors },
      { status: 400 }
    );
  }

  // Execute mutation
  const response = await admin.graphql(`
    mutation createProduct($input: ProductInput!) {
      productCreate(input: $input) {
        product { id }
        userErrors { field message }
      }
    }
  `, {
    variables: {
      input: {
        title: result.data.title,
        descriptionHtml: result.data.description,
        variants: [{ price: result.data.price.toString() }],
      },
    },
  });

  const { data } = await response.json();

  // Check for Shopify errors
  if (data.productCreate.userErrors.length > 0) {
    return json(
      { errors: { _form: data.productCreate.userErrors.map((e: any) => e.message) } },
      { status: 400 }
    );
  }

  return redirect("/app/products");
}
```

### Multiple Actions with Intent

```tsx
// app/routes/app.products.$id/route.tsx
export async function action({ request, params }: ActionFunctionArgs) {
  const { admin } = await authenticate.admin(request);
  const formData = await request.formData();
  const intent = formData.get("intent");
  const productId = `gid://shopify/Product/${params.id}`;

  switch (intent) {
    case "update": {
      const title = formData.get("title") as string;
      const result = updateSchema.safeParse({ title });

      if (!result.success) {
        return json({ errors: result.error.flatten().fieldErrors }, { status: 400 });
      }

      await admin.graphql(`
        mutation updateProduct($input: ProductInput!) {
          productUpdate(input: $input) {
            product { id }
            userErrors { field message }
          }
        }
      `, {
        variables: { input: { id: productId, title: result.data.title } },
      });

      return json({ success: true });
    }

    case "delete": {
      await admin.graphql(`
        mutation deleteProduct($input: ProductDeleteInput!) {
          productDelete(input: $input) {
            deletedProductId
            userErrors { field message }
          }
        }
      `, {
        variables: { input: { id: productId } },
      });

      return redirect("/app/products");
    }

    case "duplicate": {
      // Fetch original, create copy
      // ...
      return redirect(`/app/products/${newId}`);
    }

    default:
      return json({ error: "Invalid intent" }, { status: 400 });
  }
}
```

### Action with App Database

```tsx
export async function action({ request }: ActionFunctionArgs) {
  const { session } = await authenticate.admin(request);
  const formData = await request.formData();

  const result = settingsSchema.safeParse(Object.fromEntries(formData));
  if (!result.success) {
    return json({ errors: result.error.flatten().fieldErrors }, { status: 400 });
  }

  // Upsert settings for this shop
  await db.appSettings.upsert({
    where: { shopDomain: session.shop },
    update: result.data,
    create: { shopDomain: session.shop, ...result.data },
  });

  return json({ success: true });
}
```

## useFetcher for Non-Navigation Mutations

```tsx
import { useFetcher } from "@remix-run/react";

export function DeleteButton({ productId }: { productId: string }) {
  const fetcher = useFetcher();
  const isDeleting = fetcher.state !== "idle";

  return (
    <fetcher.Form method="post" action={`/app/products/${productId}`}>
      <input type="hidden" name="intent" value="delete" />
      <Button destructive loading={isDeleting} submit>
        Delete
      </Button>
    </fetcher.Form>
  );
}
```

## Loading States

```tsx
import { useNavigation } from "@remix-run/react";

export default function ProductPage() {
  const navigation = useNavigation();
  const isLoading = navigation.state === "loading";
  const isSubmitting = navigation.state === "submitting";

  if (isLoading) {
    return <ProductSkeleton />;
  }

  return (
    <Form method="post">
      {/* form fields */}
      <Button submit loading={isSubmitting}>Save</Button>
    </Form>
  );
}
```

## Error Boundary

```tsx
import { isRouteErrorResponse, useRouteError } from "@remix-run/react";
import { Page, Banner } from "@shopify/polaris";

export function ErrorBoundary() {
  const error = useRouteError();

  if (isRouteErrorResponse(error)) {
    return (
      <Page title="Error">
        <Banner tone="critical">
          <p>{error.status}: {error.statusText}</p>
          {error.data?.message && <p>{error.data.message}</p>}
        </Banner>
      </Page>
    );
  }

  return (
    <Page title="Error">
      <Banner tone="critical">
        <p>An unexpected error occurred.</p>
      </Banner>
    </Page>
  );
}
```