---
name: polaris
description: Shopify Polaris design system for React applications. Covers component selection, layout patterns, form components, data tables, navigation, and App Bridge integration. Triggers on: Shopify app UI, Polaris components, merchant-facing interfaces, embedded app styling, Shopify admin UI patterns.
---

# Polaris Design System

Build merchant-facing UIs for Shopify apps.

## Setup

```bash
npm install @shopify/polaris @shopify/polaris-icons
```

### App Provider Setup

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

## Component Decision Tree

```
What are you building?
│
├─ Full page layout?
│   └─ Page + Layout + Layout.Section
│
├─ Form?
│   ├─ Simple form → FormLayout + TextField/Select/Checkbox
│   └─ Card-based form → Card + FormLayout
│
├─ Data display?
│   ├─ List of resources → IndexTable or ResourceList
│   ├─ Key-value pairs → DescriptionList
│   └─ Stats/metrics → Card + Text
│
├─ Actions?
│   ├─ Primary action → Button (variant="primary")
│   ├─ Secondary actions → Button (variant="secondary")
│   ├─ Destructive → Button (variant="primary" tone="critical")
│   └─ Menu of actions → ActionList or Popover
│
├─ Feedback?
│   ├─ Form errors → Banner (tone="critical")
│   ├─ Success message → Toast (via App Bridge)
│   ├─ Warnings → Banner (tone="warning")
│   └─ Info → Banner (tone="info")
│
├─ Loading state?
│   ├─ Full page → SkeletonPage
│   ├─ Section → SkeletonBodyText
│   └─ Inline → Spinner
│
└─ Empty state?
    └─ EmptyState with illustration
```

## Page Structure

### Standard Page Layout

```tsx
import {
  Page,
  Layout,
  Card,
  Text,
  BlockStack,
} from "@shopify/polaris";

export default function ProductsPage() {
  return (
    <Page
      title="Products"
      subtitle="Manage your product catalog"
      primaryAction={{ content: "Add product", url: "/app/products/new" }}
      secondaryActions={[
        { content: "Export", onAction: handleExport },
        { content: "Import", onAction: handleImport },
      ]}
    >
      <Layout>
        {/* Main content - 2/3 width */}
        <Layout.Section>
          <Card>
            <ProductTable products={products} />
          </Card>
        </Layout.Section>

        {/* Sidebar - 1/3 width */}
        <Layout.Section variant="oneThird">
          <Card>
            <BlockStack gap="200">
              <Text as="h2" variant="headingMd">Quick stats</Text>
              <Text>Total products: {stats.total}</Text>
              <Text>Active: {stats.active}</Text>
            </BlockStack>
          </Card>
        </Layout.Section>
      </Layout>
    </Page>
  );
}
```

### Page with Tabs

```tsx
import { Page, Tabs } from "@shopify/polaris";
import { useState, useCallback } from "react";

export default function SettingsPage() {
  const [selected, setSelected] = useState(0);

  const tabs = [
    { id: "general", content: "General", panelID: "general-panel" },
    { id: "billing", content: "Billing", panelID: "billing-panel" },
    { id: "notifications", content: "Notifications", panelID: "notifications-panel" },
  ];

  return (
    <Page title="Settings">
      <Tabs tabs={tabs} selected={selected} onSelect={setSelected}>
        {selected === 0 && <GeneralSettings />}
        {selected === 1 && <BillingSettings />}
        {selected === 2 && <NotificationSettings />}
      </Tabs>
    </Page>
  );
}
```

### Page with Back Action

```tsx
<Page
  title="Edit Product"
  backAction={{ content: "Products", url: "/app/products" }}
  primaryAction={{ content: "Save", onAction: handleSave, loading: isSaving }}
>
  {/* content */}
</Page>
```

## Form Components

### TextField

```tsx
import { TextField } from "@shopify/polaris";

<TextField
  label="Product title"
  name="title"
  value={title}
  onChange={setTitle}
  autoComplete="off"
  helpText="Customers will see this in their cart"
  error={errors.title}
  requiredIndicator
/>

// Multiline
<TextField
  label="Description"
  name="description"
  value={description}
  onChange={setDescription}
  multiline={4}
  autoComplete="off"
/>

// Number input
<TextField
  label="Price"
  name="price"
  type="number"
  value={price}
  onChange={setPrice}
  prefix="$"
  autoComplete="off"
/>
```

### Select

```tsx
import { Select } from "@shopify/polaris";

const options = [
  { label: "Draft", value: "draft" },
  { label: "Active", value: "active" },
  { label: "Archived", value: "archived" },
];

<Select
  label="Status"
  name="status"
  options={options}
  value={status}
  onChange={setStatus}
/>
```

### Checkbox and ChoiceList

```tsx
import { Checkbox, ChoiceList } from "@shopify/polaris";

// Single checkbox
<Checkbox
  label="Track inventory"
  checked={trackInventory}
  onChange={setTrackInventory}
/>

// Multiple choices
<ChoiceList
  title="Shipping options"
  choices={[
    { label: "Standard shipping", value: "standard" },
    { label: "Express shipping", value: "express" },
    { label: "Pickup", value: "pickup" },
  ]}
  selected={selectedShipping}
  onChange={setSelectedShipping}
  allowMultiple
/>

// Radio buttons (single choice)
<ChoiceList
  title="Visibility"
  choices={[
    { label: "Online store", value: "online" },
    { label: "Point of sale", value: "pos" },
    { label: "Both", value: "both" },
  ]}
  selected={[visibility]}
  onChange={(value) => setVisibility(value[0])}
/>
```

### FormLayout

```tsx
import { FormLayout, TextField, Select, Button } from "@shopify/polaris";
import { Form } from "@remix-run/react";

<Form method="post">
  <FormLayout>
    <TextField label="Title" name="title" autoComplete="off" />
    
    {/* Two columns */}
    <FormLayout.Group>
      <TextField label="Price" name="price" type="number" prefix="$" autoComplete="off" />
      <TextField label="Compare at price" name="comparePrice" type="number" prefix="$" autoComplete="off" />
    </FormLayout.Group>
    
    <Select
      label="Status"
      name="status"
      options={statusOptions}
      value={status}
      onChange={setStatus}
    />
    
    <Button submit variant="primary">Save</Button>
  </FormLayout>
</Form>
```

## Data Tables

### IndexTable (Recommended for Resources)

```tsx
import {
  IndexTable,
  Card,
  Text,
  Badge,
  useIndexResourceState,
  useBreakpoints,
} from "@shopify/polaris";

export function ProductTable({ products }: { products: Product[] }) {
  const resourceName = {
    singular: "product",
    plural: "products",
  };

  const { selectedResources, allResourcesSelected, handleSelectionChange } =
    useIndexResourceState(products);

  const { smUp } = useBreakpoints();

  const rowMarkup = products.map((product, index) => (
    <IndexTable.Row
      id={product.id}
      key={product.id}
      selected={selectedResources.includes(product.id)}
      position={index}
    >
      <IndexTable.Cell>
        <Text variant="bodyMd" fontWeight="bold" as="span">
          {product.title}
        </Text>
      </IndexTable.Cell>
      <IndexTable.Cell>
        <Badge tone={product.status === "ACTIVE" ? "success" : "info"}>
          {product.status}
        </Badge>
      </IndexTable.Cell>
      <IndexTable.Cell>
        {product.totalInventory} in stock
      </IndexTable.Cell>
      <IndexTable.Cell>
        ${product.price}
      </IndexTable.Cell>
    </IndexTable.Row>
  ));

  return (
    <Card padding="0">
      <IndexTable
        resourceName={resourceName}
        itemCount={products.length}
        selectedItemsCount={
          allResourcesSelected ? "All" : selectedResources.length
        }
        onSelectionChange={handleSelectionChange}
        headings={[
          { title: "Product" },
          { title: "Status" },
          { title: "Inventory" },
          { title: "Price" },
        ]}
        bulkActions={[
          { content: "Activate", onAction: () => handleBulkAction("activate") },
          { content: "Deactivate", onAction: () => handleBulkAction("deactivate") },
        ]}
        promotedBulkActions={[
          { content: "Delete", onAction: () => handleBulkAction("delete") },
        ]}
      >
        {rowMarkup}
      </IndexTable>
    </Card>
  );
}
```

### DataTable (Simple Tables)

```tsx
import { DataTable, Card } from "@shopify/polaris";

const rows = [
  ["Product A", 100, "$29.99", "$2,999.00"],
  ["Product B", 50, "$49.99", "$2,499.50"],
  ["Product C", 200, "$19.99", "$3,998.00"],
];

<Card>
  <DataTable
    columnContentTypes={["text", "numeric", "numeric", "numeric"]}
    headings={["Product", "Quantity", "Price", "Total"]}
    rows={rows}
    totals={["", 350, "", "$9,496.50"]}
    showTotalsInFooter
  />
</Card>
```

## Feedback Components

### Banner

```tsx
import { Banner, Page, Layout } from "@shopify/polaris";

// Critical (error)
<Banner
  title="Order payment failed"
  tone="critical"
  action={{ content: "Retry payment", onAction: handleRetry }}
  onDismiss={() => setShowBanner(false)}
>
  <p>The customer's payment could not be processed.</p>
</Banner>

// Warning
<Banner
  title="Low inventory"
  tone="warning"
>
  <p>5 products have fewer than 10 items in stock.</p>
</Banner>

// Success
<Banner
  title="Product saved"
  tone="success"
  onDismiss={() => setShowBanner(false)}
/>

// Info
<Banner
  title="New feature available"
  tone="info"
>
  <p>Check out our new bulk editing tools.</p>
</Banner>
```

### Toast (via App Bridge)

```tsx
import { useAppBridge } from "@shopify/app-bridge-react";

function SaveButton() {
  const shopify = useAppBridge();
  
  const handleSave = async () => {
    try {
      await saveProduct();
      shopify.toast.show("Product saved successfully");
    } catch (error) {
      shopify.toast.show("Failed to save product", { isError: true });
    }
  };
  
  return <Button onClick={handleSave}>Save</Button>;
}
```

## Loading States

### SkeletonPage

```tsx
import {
  SkeletonPage,
  Layout,
  Card,
  SkeletonBodyText,
  SkeletonDisplayText,
  BlockStack,
} from "@shopify/polaris";

export function ProductPageSkeleton() {
  return (
    <SkeletonPage primaryAction>
      <Layout>
        <Layout.Section>
          <Card>
            <BlockStack gap="400">
              <SkeletonDisplayText size="small" />
              <SkeletonBodyText lines={3} />
            </BlockStack>
          </Card>
          <Card>
            <BlockStack gap="400">
              <SkeletonDisplayText size="small" />
              <SkeletonBodyText lines={2} />
            </BlockStack>
          </Card>
        </Layout.Section>
        <Layout.Section variant="oneThird">
          <Card>
            <SkeletonBodyText lines={4} />
          </Card>
        </Layout.Section>
      </Layout>
    </SkeletonPage>
  );
}
```

### Spinner

```tsx
import { Spinner, Box } from "@shopify/polaris";

// Inline spinner
<Button disabled={isLoading}>
  {isLoading ? <Spinner size="small" /> : "Save"}
</Button>

// Centered spinner
<Box padding="800" width="100%">
  <div style={{ display: "flex", justifyContent: "center" }}>
    <Spinner />
  </div>
</Box>
```

## Empty State

```tsx
import { EmptyState, Page } from "@shopify/polaris";

export function NoProductsState() {
  return (
    <Page>
      <EmptyState
        heading="Add your first product"
        action={{ content: "Add product", url: "/app/products/new" }}
        secondaryAction={{
          content: "Learn more",
          url: "https://help.shopify.com/",
        }}
        image="https://cdn.shopify.com/s/files/1/0262/4071/2726/files/emptystate-files.png"
      >
        <p>Add products to start selling on your store.</p>
      </EmptyState>
    </Page>
  );
}
```

## Actions

### Button Variants

```tsx
import { Button, ButtonGroup, InlineStack } from "@shopify/polaris";

// Primary action
<Button variant="primary">Save product</Button>

// Secondary action
<Button>Cancel</Button>

// Destructive
<Button variant="primary" tone="critical">Delete</Button>

// Plain (link-style)
<Button variant="plain">View details</Button>

// Loading state
<Button variant="primary" loading={isSaving}>Save</Button>

// Disabled
<Button variant="primary" disabled>Save</Button>

// With icon
import { PlusIcon } from "@shopify/polaris-icons";
<Button variant="primary" icon={PlusIcon}>Add product</Button>

// Button group
<ButtonGroup>
  <Button>Cancel</Button>
  <Button variant="primary">Save</Button>
</ButtonGroup>
```

### ActionList (Dropdown Menu)

```tsx
import { ActionList, Popover, Button } from "@shopify/polaris";
import { useState, useCallback } from "react";

export function ActionsMenu() {
  const [active, setActive] = useState(false);
  const toggleActive = useCallback(() => setActive((active) => !active), []);

  const activator = (
    <Button onClick={toggleActive} disclosure>
      More actions
    </Button>
  );

  return (
    <Popover
      active={active}
      activator={activator}
      onClose={toggleActive}
    >
      <ActionList
        actionRole="menuitem"
        items={[
          { content: "Duplicate", onAction: handleDuplicate },
          { content: "Archive", onAction: handleArchive },
          { content: "Delete", destructive: true, onAction: handleDelete },
        ]}
      />
    </Popover>
  );
}
```

## Layout Components

### BlockStack (Vertical)

```tsx
import { BlockStack, Text, Card } from "@shopify/polaris";

<Card>
  <BlockStack gap="400">
    <Text as="h2" variant="headingMd">Section Title</Text>
    <Text>First paragraph of content.</Text>
    <Text>Second paragraph of content.</Text>
  </BlockStack>
</Card>
```

### InlineStack (Horizontal)

```tsx
import { InlineStack, Button, Badge } from "@shopify/polaris";

<InlineStack gap="200" align="center">
  <Text>Product status:</Text>
  <Badge tone="success">Active</Badge>
</InlineStack>

<InlineStack gap="200" align="end">
  <Button>Cancel</Button>
  <Button variant="primary">Save</Button>
</InlineStack>
```

### Box

```tsx
import { Box, Text } from "@shopify/polaris";

<Box
  padding="400"
  background="bg-surface-secondary"
  borderRadius="200"
  borderWidth="025"
  borderColor="border"
>
  <Text>Content with custom styling</Text>
</Box>
```

### Divider

```tsx
import { Divider, BlockStack, Text } from "@shopify/polaris";

<BlockStack gap="400">
  <Text>Section 1</Text>
  <Divider />
  <Text>Section 2</Text>
</BlockStack>
```

## Modal

### Via App Bridge (Recommended for Embedded Apps)

```tsx
import { Modal, TitleBar } from "@shopify/app-bridge-react";

export function DeleteConfirmModal({
  open,
  onClose,
  onConfirm,
  productTitle,
}: {
  open: boolean;
  onClose: () => void;
  onConfirm: () => void;
  productTitle: string;
}) {
  return (
    <Modal open={open} onClose={onClose}>
      <div style={{ padding: "1rem" }}>
        <p>Are you sure you want to delete "{productTitle}"?</p>
        <p>This action cannot be undone.</p>
      </div>
      <TitleBar title="Delete product">
        <button onClick={onClose}>Cancel</button>
        <button variant="primary" tone="critical" onClick={onConfirm}>
          Delete
        </button>
      </TitleBar>
    </Modal>
  );
}
```

## References

| File | Contents |
|------|----------|
| [components.md](references/components.md) | Complete component inventory with all props |
| [accessibility.md](references/accessibility.md) | Polaris a11y patterns and checklist |

**Integration**: Use `shopify-remix` skill for routes and data, forms+validation integrated in shopify-remix