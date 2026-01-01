# Polaris Accessibility

Polaris components have accessibility built-in, but you must use them correctly.

## Built-In Features

| Component | Built-In A11y |
|-----------|---------------|
| Button | Focus states, disabled states, loading announcements |
| TextField | Label association, error announcements |
| Modal | Focus trap, escape to close, ARIA attributes |
| Banner | Role="status" for info, role="alert" for critical |
| IndexTable | Row selection announcements, sortable headers |
| Navigation | Landmark, current page indication |

## Common Patterns

### Form Fields

```tsx
// ✅ Polaris handles label association automatically
<TextField
  label="Email"
  type="email"
  value={email}
  onChange={setEmail}
  error={errors.email}  // Announced to screen readers
  helpText="We'll never share your email"
/>

// ✅ Required fields
<TextField
  label="Product title"
  requiredIndicator  // Adds visual indicator + aria-required
  value={title}
  onChange={setTitle}
/>

// ✅ Hidden label (use sparingly)
<TextField
  label="Search"
  labelHidden  // Visually hidden but still accessible
  placeholder="Search products..."
  prefix={<Icon source={SearchIcon} />}
/>
```

### Form Layout

```tsx
// Group related fields
<FormLayout>
  <FormLayout.Group>
    <TextField label="First name" />
    <TextField label="Last name" />
  </FormLayout.Group>
  <TextField label="Email" type="email" />
</FormLayout>

// Condensed for dense forms
<FormLayout>
  <FormLayout.Group condensed>
    <TextField label="City" />
    <TextField label="State" />
    <TextField label="ZIP" />
  </FormLayout.Group>
</FormLayout>
```

### Buttons

```tsx
// ✅ Clear button text
<Button onClick={handleSave}>Save product</Button>

// ✅ Loading state (announced)
<Button loading={saving} onClick={handleSave}>
  Save product
</Button>

// ✅ Icon-only buttons need accessibilityLabel
<Button
  icon={DeleteIcon}
  accessibilityLabel="Delete product"
  onClick={handleDelete}
/>

// ✅ Destructive actions
<Button destructive onClick={handleDelete}>
  Delete
</Button>
```

### Page Actions

```tsx
<Page
  title="Product"
  backAction={{ content: 'Products', url: '/app/products' }}
  primaryAction={{
    content: 'Save',
    onAction: handleSave,
    loading: saving,
  }}
  secondaryActions={[
    {
      content: 'Duplicate',
      accessibilityLabel: 'Duplicate this product',
      onAction: handleDuplicate,
    },
    {
      content: 'Delete',
      destructive: true,
      onAction: handleDelete,
    },
  ]}
>
```

### Banners

```tsx
// Info (role="status" - polite)
<Banner title="Order updated">
  <p>The order has been updated.</p>
</Banner>

// Warning
<Banner title="Low inventory" tone="warning">
  <p>Only 5 items remaining.</p>
</Banner>

// Critical (role="alert" - assertive)
<Banner title="Payment failed" tone="critical">
  <p>The payment could not be processed.</p>
</Banner>

// With actions
<Banner
  title="Subscription expiring"
  tone="warning"
  action={{ content: 'Renew', onAction: handleRenew }}
  secondaryAction={{ content: 'Learn more', url: '/help' }}
>
  <p>Your subscription expires in 3 days.</p>
</Banner>
```

### Modals

```tsx
// Polaris Modal handles focus trap and escape
<Modal
  open={active}
  onClose={handleClose}
  title="Delete product?"  // Announced on open
  primaryAction={{
    content: 'Delete',
    destructive: true,
    onAction: handleDelete,
  }}
  secondaryActions={[
    { content: 'Cancel', onAction: handleClose },
  ]}
>
  <Modal.Section>
    <p>This action cannot be undone.</p>
  </Modal.Section>
</Modal>
```

### Data Tables

```tsx
// IndexTable for selectable resources
<IndexTable
  resourceName={{ singular: 'product', plural: 'products' }}
  itemCount={products.length}
  selectedItemsCount={selectedResources.length}
  onSelectionChange={handleSelectionChange}
  headings={[
    { title: 'Product' },
    { title: 'Status' },
    { title: 'Inventory', alignment: 'end' },
  ]}
  // Sortable columns
  sortable={[true, false, true]}
  sortDirection={sortDirection}
  sortColumnIndex={sortColumnIndex}
  onSort={handleSort}
>
  {products.map((product, index) => (
    <IndexTable.Row
      id={product.id}
      key={product.id}
      position={index}
      selected={selectedResources.includes(product.id)}
    >
      <IndexTable.Cell>
        <Text variant="bodyMd" fontWeight="bold">
          {product.title}
        </Text>
      </IndexTable.Cell>
      <IndexTable.Cell>
        <Badge tone={product.status === 'active' ? 'success' : undefined}>
          {product.status}
        </Badge>
      </IndexTable.Cell>
      <IndexTable.Cell>
        <Text alignment="end">{product.inventory}</Text>
      </IndexTable.Cell>
    </IndexTable.Row>
  ))}
</IndexTable>
```

### Navigation

```tsx
// NavMenu handles current page indication
<NavMenu>
  <Link url="/app" rel="home">Dashboard</Link>
  <Link url="/app/products">Products</Link>
  <Link url="/app/orders">Orders</Link>
  <Link url="/app/settings">Settings</Link>
</NavMenu>
```

### Empty States

```tsx
<EmptyState
  heading="No products yet"
  action={{
    content: 'Add product',
    onAction: handleAddProduct,
  }}
  secondaryAction={{
    content: 'Learn more',
    url: 'https://help.shopify.com',
  }}
  image="https://cdn.shopify.com/..."
>
  <p>Add products to start selling.</p>
</EmptyState>
```

## Loading States

### Skeleton Components

```tsx
// Page loading
function ProductPageSkeleton() {
  return (
    <SkeletonPage title="Product" primaryAction>
      <Card>
        <SkeletonBodyText lines={3} />
      </Card>
      <Card>
        <SkeletonDisplayText size="small" />
        <SkeletonBodyText lines={2} />
      </Card>
    </SkeletonPage>
  );
}

// Inline loading
<Card>
  {loading ? (
    <>
      <SkeletonDisplayText size="small" />
      <SkeletonBodyText lines={3} />
    </>
  ) : (
    <ProductDetails product={product} />
  )}
</Card>
```

### Spinner with Announcements

```tsx
// Spinner is announced to screen readers
<Spinner accessibilityLabel="Loading products" size="large" />

// Inline spinner
<Button loading={saving}>
  Save  {/* "Loading" announced while loading */}
</Button>
```

## App Bridge Accessibility

### Toast Notifications

```tsx
// Toasts are automatically announced
const shopify = useAppBridge();

// Success
shopify.toast.show("Product saved");

// Error
shopify.toast.show("Failed to save product", { isError: true });
```

### Modal via App Bridge

```tsx
// App Bridge modals handle focus correctly
<Modal
  open={active}
  onClose={handleClose}
  title="Edit product"
>
  {/* Content */}
</Modal>
```

## Edge Cases

### Dynamic Content

```tsx
// Announce dynamic updates
function OrderCount({ count }: { count: number }) {
  return (
    <div aria-live="polite" aria-atomic="true">
      {count} orders pending
    </div>
  );
}
```

### Custom Components

```tsx
// When building custom components, follow Polaris patterns
function CustomCard({ 
  title, 
  children,
  actions,
}: CustomCardProps) {
  return (
    <Card>
      <BlockStack gap="200">
        <InlineStack align="space-between">
          <Text as="h2" variant="headingMd">{title}</Text>
          {actions && (
            <ButtonGroup>
              {actions.map((action, i) => (
                <Button
                  key={i}
                  onClick={action.onAction}
                  accessibilityLabel={action.accessibilityLabel}
                >
                  {action.content}
                </Button>
              ))}
            </ButtonGroup>
          )}
        </InlineStack>
        {children}
      </BlockStack>
    </Card>
  );
}
```

### Error Handling

```tsx
// Errors should be announced
function ProductForm() {
  const actionData = useActionData<typeof action>();
  
  return (
    <Form method="post">
      {actionData?.errors?._form && (
        <Banner tone="critical" role="alert">
          <p>{actionData.errors._form.join(', ')}</p>
        </Banner>
      )}
      
      <TextField
        label="Title"
        name="title"
        error={actionData?.errors?.title?.[0]}  // Associated with field
      />
    </Form>
  );
}
```

## Checklist

### Forms
- [ ] All fields have labels (visible or labelHidden)
- [ ] Required fields use requiredIndicator
- [ ] Error messages use error prop
- [ ] Help text uses helpText prop
- [ ] Form groups use FormLayout

### Buttons
- [ ] Icon-only buttons have accessibilityLabel
- [ ] Loading states use loading prop
- [ ] Destructive actions use destructive prop

### Feedback
- [ ] Use Banner for persistent messages
- [ ] Use Toast for transient messages
- [ ] Critical errors use tone="critical"
- [ ] Loading states use Skeleton or Spinner

### Tables
- [ ] Use IndexTable for resource lists
- [ ] Define resourceName for announcements
- [ ] Sortable columns indicated
- [ ] Selection state announced

### Navigation
- [ ] Use NavMenu for app navigation
- [ ] Back actions on detail pages
- [ ] Current page indicated automatically

### Modals
- [ ] Title describes purpose
- [ ] Primary action is clear
- [ ] Cancel/close action available
- [ ] Destructive actions marked