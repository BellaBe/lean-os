# Remix Forms with Zod Validation

Forms in Shopify Remix use Remix's `<Form>` component with Zod validation in actions. This is an atomic pattern — validation and submission happen together.

## Core Pattern

```tsx
// app/routes/app.products.new/route.tsx
import { json, redirect, type ActionFunctionArgs } from "@remix-run/node";
import { Form, useActionData, useNavigation } from "@remix-run/react";
import { Page, Card, FormLayout, TextField, Button, Banner } from "@shopify/polaris";
import { authenticate } from "~/lib/shopify.server";
import { z } from "zod";

// 1. Define schema
const productSchema = z.object({
  title: z.string().min(1, "Title is required"),
  description: z.string().optional(),
  price: z.coerce.number().positive("Price must be positive"),
  vendor: z.string().optional(),
});

// 2. Action handles validation + submission
export async function action({ request }: ActionFunctionArgs) {
  const { admin } = await authenticate.admin(request);
  const formData = await request.formData();
  const rawData = Object.fromEntries(formData);

  const result = productSchema.safeParse(rawData);

  if (!result.success) {
    return json(
      { errors: result.error.flatten().fieldErrors },
      { status: 400 }
    );
  }

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
        vendor: result.data.vendor,
        variants: [{ price: result.data.price.toString() }],
      },
    },
  });

  const { data } = await response.json();

  if (data.productCreate.userErrors.length > 0) {
    return json(
      { errors: { _form: data.productCreate.userErrors.map((e: any) => e.message) } },
      { status: 400 }
    );
  }

  return redirect("/app/products");
}

// 3. Component uses Remix Form + Polaris
export default function NewProductPage() {
  const actionData = useActionData<typeof action>();
  const navigation = useNavigation();
  const isSubmitting = navigation.state === "submitting";

  return (
    <Page title="New Product" backAction={{ url: "/app/products" }}>
      <Form method="post">
        <Card>
          <FormLayout>
            <TextField
              name="title"
              label="Title"
              autoComplete="off"
              error={actionData?.errors?.title?.[0]}
              requiredIndicator
            />
            <TextField
              name="description"
              label="Description"
              multiline={4}
              autoComplete="off"
            />
            <TextField
              name="price"
              label="Price"
              type="number"
              prefix="$"
              autoComplete="off"
              error={actionData?.errors?.price?.[0]}
              requiredIndicator
            />
            <TextField
              name="vendor"
              label="Vendor"
              autoComplete="off"
            />

            {actionData?.errors?._form && (
              <Banner tone="critical">
                {actionData.errors._form.join(", ")}
              </Banner>
            )}

            <Button submit variant="primary" loading={isSubmitting}>
              Create Product
            </Button>
          </FormLayout>
        </Card>
      </Form>
    </Page>
  );
}
```

## Zod Schema Patterns

### Basic Types

```ts
const schema = z.object({
  // Strings
  name: z.string().min(1, "Required"),
  email: z.string().email("Invalid email"),
  url: z.string().url().optional(),
  
  // Numbers (use coerce for form inputs)
  age: z.coerce.number().min(0).max(120),
  price: z.coerce.number().positive("Must be positive"),
  quantity: z.coerce.number().int().min(0),
  
  // Booleans (checkboxes)
  terms: z.literal(true, { errorMap: () => ({ message: "Must accept terms" }) }),
  subscribe: z.preprocess((val) => val === "on" || val === "true", z.boolean()),
  
  // Enums
  status: z.enum(["draft", "active", "archived"]),
  
  // Dates
  startDate: z.coerce.date(),
  
  // Arrays
  tags: z.array(z.string()).min(1, "Select at least one"),
});
```

### Cross-Field Validation

```ts
const passwordSchema = z.object({
  password: z.string().min(8, "At least 8 characters"),
  confirmPassword: z.string(),
}).refine((data) => data.password === data.confirmPassword, {
  message: "Passwords don't match",
  path: ["confirmPassword"],
});
```

### Conditional Validation

```ts
const schema = z.object({
  hasCompany: z.preprocess((val) => val === "on", z.boolean()),
  companyName: z.string().optional(),
  taxId: z.string().optional(),
}).refine(
  (data) => !data.hasCompany || (data.companyName && data.companyName.length > 0),
  { message: "Company name required", path: ["companyName"] }
).refine(
  (data) => !data.hasCompany || (data.taxId && data.taxId.length > 0),
  { message: "Tax ID required", path: ["taxId"] }
);
```

### Date Range Validation

```ts
const dateRangeSchema = z.object({
  startDate: z.coerce.date(),
  endDate: z.coerce.date(),
}).refine((data) => data.endDate > data.startDate, {
  message: "End date must be after start date",
  path: ["endDate"],
});
```

## Form with Edit/Update

```tsx
// app/routes/app.products.$id/route.tsx
import { json, redirect, type LoaderFunctionArgs, type ActionFunctionArgs } from "@remix-run/node";
import { Form, useLoaderData, useActionData, useNavigation } from "@remix-run/react";

const updateSchema = z.object({
  title: z.string().min(1, "Title is required"),
  description: z.string().optional(),
  status: z.enum(["DRAFT", "ACTIVE", "ARCHIVED"]),
});

export async function loader({ request, params }: LoaderFunctionArgs) {
  const { admin } = await authenticate.admin(request);
  
  const response = await admin.graphql(`
    query getProduct($id: ID!) {
      product(id: $id) {
        id
        title
        descriptionHtml
        status
      }
    }
  `, {
    variables: { id: `gid://shopify/Product/${params.id}` },
  });

  const { data } = await response.json();
  return json({ product: data.product });
}

export async function action({ request, params }: ActionFunctionArgs) {
  const { admin } = await authenticate.admin(request);
  const formData = await request.formData();

  const result = updateSchema.safeParse(Object.fromEntries(formData));
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
    variables: {
      input: {
        id: `gid://shopify/Product/${params.id}`,
        title: result.data.title,
        descriptionHtml: result.data.description,
        status: result.data.status,
      },
    },
  });

  return redirect("/app/products");
}

export default function EditProductPage() {
  const { product } = useLoaderData<typeof loader>();
  const actionData = useActionData<typeof action>();
  const navigation = useNavigation();

  return (
    <Page title="Edit Product" backAction={{ url: "/app/products" }}>
      <Form method="post">
        <Card>
          <FormLayout>
            <TextField
              name="title"
              label="Title"
              defaultValue={product.title}
              error={actionData?.errors?.title?.[0]}
            />
            <TextField
              name="description"
              label="Description"
              defaultValue={product.descriptionHtml}
              multiline={4}
            />
            <Select
              name="status"
              label="Status"
              options={[
                { label: "Draft", value: "DRAFT" },
                { label: "Active", value: "ACTIVE" },
                { label: "Archived", value: "ARCHIVED" },
              ]}
              value={product.status}
            />
            <Button submit variant="primary" loading={navigation.state === "submitting"}>
              Save
            </Button>
          </FormLayout>
        </Card>
      </Form>
    </Page>
  );
}
```

## Form with Multiple Actions

```tsx
export default function ProductPage() {
  const { product } = useLoaderData<typeof loader>();
  const actionData = useActionData<typeof action>();
  const navigation = useNavigation();

  return (
    <Page
      title={product.title}
      backAction={{ url: "/app/products" }}
      secondaryActions={[
        <Form method="post" key="delete">
          <input type="hidden" name="intent" value="delete" />
          <Button submit destructive>Delete</Button>
        </Form>,
      ]}
    >
      <Form method="post">
        <input type="hidden" name="intent" value="update" />
        <Card>
          <FormLayout>
            <TextField
              name="title"
              label="Title"
              defaultValue={product.title}
              error={actionData?.errors?.title?.[0]}
            />
            <Button submit variant="primary">Save</Button>
          </FormLayout>
        </Card>
      </Form>
    </Page>
  );
}
```

## Checkbox Handling

HTML checkboxes only submit when checked. Handle this in preprocessing:

```ts
const schema = z.object({
  // Single checkbox
  agreeToTerms: z.preprocess(
    (val) => val === "on" || val === "true" || val === true,
    z.boolean()
  ),
  
  // Required checkbox
  mustAccept: z.preprocess(
    (val) => val === "on" || val === "true" || val === true,
    z.literal(true, { errorMap: () => ({ message: "You must accept" }) })
  ),
});
```

```tsx
<Checkbox
  name="agreeToTerms"
  label="I agree to the terms"
  defaultChecked={false}
/>
```

## Select and ChoiceList

```tsx
<Select
  name="status"
  label="Status"
  options={[
    { label: "Draft", value: "draft" },
    { label: "Active", value: "active" },
  ]}
  value={selectedStatus}
  onChange={setSelectedStatus}
/>

{/* For multiple selection, use hidden inputs */}
<ChoiceList
  title="Tags"
  allowMultiple
  choices={[
    { label: "Featured", value: "featured" },
    { label: "Sale", value: "sale" },
  ]}
  selected={selectedTags}
  onChange={setSelectedTags}
/>
{selectedTags.map((tag) => (
  <input key={tag} type="hidden" name="tags" value={tag} />
))}
```

## Error Display

### Field Errors

```tsx
<TextField
  name="email"
  label="Email"
  error={actionData?.errors?.email?.[0]}
/>
```

### Form-Level Errors

```tsx
{actionData?.errors?._form && (
  <Banner tone="critical">
    <ul>
      {actionData.errors._form.map((error, i) => (
        <li key={i}>{error}</li>
      ))}
    </ul>
  </Banner>
)}
```

## Toast on Success

```tsx
import { useAppBridge } from "@shopify/app-bridge-react";
import { useEffect } from "react";

export default function ProductPage() {
  const shopify = useAppBridge();
  const actionData = useActionData<typeof action>();

  useEffect(() => {
    if (actionData?.success) {
      shopify.toast.show("Product saved successfully");
    }
  }, [actionData, shopify]);

  // ...
}
```

## File Uploads

For file uploads, use `encType="multipart/form-data"`:

```tsx
<Form method="post" encType="multipart/form-data">
  <DropZone onDrop={handleDrop}>
    <DropZone.FileUpload />
  </DropZone>
  <input type="hidden" name="fileUrl" value={uploadedFileUrl} />
  <Button submit>Save</Button>
</Form>
```

Note: For large files, upload to Shopify's staged uploads first, then save the URL.