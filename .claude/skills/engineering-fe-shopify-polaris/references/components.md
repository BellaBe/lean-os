# Polaris Component Inventory

## Layout Components

### Page

Top-level container for all page content.

```tsx
import { Page } from "@shopify/polaris";

<Page
  title="Page title"
  subtitle="Optional subtitle"
  titleMetadata={<Badge>Draft</Badge>}
  compactTitle                           // Smaller title
  backAction={{ content: "Back", url: "/app" }}
  primaryAction={{ content: "Save", onAction: save, loading: isSaving }}
  secondaryActions={[
    { content: "Duplicate", onAction: duplicate },
    { content: "Archive", onAction: archive },
  ]}
  actionGroups={[
    {
      title: "More actions",
      actions: [
        { content: "Share", onAction: share },
        { content: "Print", onAction: print },
      ],
    },
  ]}
  pagination={{
    hasPrevious: true,
    hasNext: true,
    onPrevious: goToPrevious,
    onNext: goToNext,
  }}
  fullWidth                              // Remove max-width
  narrowWidth                            // Narrower max-width
>
  {/* Page content */}
</Page>
```

### Layout

Two-column layout system.

```tsx
import { Layout } from "@shopify/polaris";

<Layout>
  {/* Full width */}
  <Layout.Section>
    <Card>Main content</Card>
  </Layout.Section>

  {/* Two columns */}
  <Layout.Section>
    <Card>Left (2/3)</Card>
  </Layout.Section>
  <Layout.Section variant="oneThird">
    <Card>Right (1/3)</Card>
  </Layout.Section>

  {/* Annotated section (form layouts) */}
  <Layout.AnnotatedSection
    title="Account details"
    description="Update your account information"
  >
    <Card>Form content</Card>
  </Layout.AnnotatedSection>
</Layout>
```

### Card

Container for related content.

```tsx
import { Card, BlockStack, Text, InlineStack, Button } from "@shopify/polaris";

// Basic
<Card>
  <Text>Card content</Text>
</Card>

// With sections
<Card>
  <BlockStack gap="400">
    <Text as="h2" variant="headingMd">Title</Text>
    <Text>Content</Text>
  </BlockStack>
</Card>

// Card with actions (use BlockStack + InlineStack)
<Card>
  <BlockStack gap="400">
    <InlineStack align="space-between">
      <Text as="h2" variant="headingMd">Products</Text>
      <Button variant="plain">Manage</Button>
    </InlineStack>
    <Text>Content here</Text>
  </BlockStack>
</Card>

// Subdued background
<Card background="bg-surface-secondary">
  <Text>Secondary content</Text>
</Card>

// No padding (for tables)
<Card padding="0">
  <IndexTable>...</IndexTable>
</Card>
```

### Box

Flexible container with style props.

```tsx
import { Box } from "@shopify/polaris";

<Box
  // Spacing
  padding="400"                    // All sides
  paddingBlock="400"               // Top and bottom
  paddingInline="400"              // Left and right
  paddingBlockStart="200"          // Top only
  paddingBlockEnd="200"            // Bottom only
  paddingInlineStart="200"         // Left only
  paddingInlineEnd="200"           // Right only

  // Background
  background="bg-surface"
  background="bg-surface-secondary"
  background="bg-surface-success"
  background="bg-surface-warning"
  background="bg-surface-critical"

  // Border
  borderWidth="025"
  borderColor="border"
  borderRadius="200"

  // Sizing
  width="100%"
  minHeight="100px"

  // Other
  shadow="100"
  position="relative"
  overflow="hidden"
>
  Content
</Box>
```

### BlockStack

Vertical stack with gap.

```tsx
import { BlockStack } from "@shopify/polaris";

<BlockStack
  gap="400"                        // 100|200|300|400|500|600|800|1000|1200|1600|2000
  align="start"                    // start|center|end|space-around|space-between|space-evenly
  inlineAlign="start"              // start|center|end|stretch
>
  <div>Item 1</div>
  <div>Item 2</div>
</BlockStack>
```

### InlineStack

Horizontal stack with gap.

```tsx
import { InlineStack } from "@shopify/polaris";

<InlineStack
  gap="400"
  align="start"                    // start|center|end|space-around|space-between|space-evenly
  blockAlign="start"               // start|center|end|baseline|stretch
  wrap={true}                      // Allow wrapping
>
  <div>Item 1</div>
  <div>Item 2</div>
</InlineStack>
```

### InlineGrid

CSS Grid layout.

```tsx
import { InlineGrid } from "@shopify/polaris";

<InlineGrid
  columns={3}                      // Number or responsive { xs: 1, sm: 2, md: 3 }
  gap="400"
>
  <div>Cell 1</div>
  <div>Cell 2</div>
  <div>Cell 3</div>
</InlineGrid>
```

### Divider

Horizontal rule.

```tsx
import { Divider } from "@shopify/polaris";

<Divider />
<Divider borderColor="border-inverse" />
```

### Bleed

Negative margin to break out of parent padding.

```tsx
import { Bleed, Box, Divider } from "@shopify/polaris";

<Box padding="400">
  <Text>Content</Text>
  <Bleed marginInline="400">
    <Divider />
  </Bleed>
  <Text>More content</Text>
</Box>
```

## Typography

### Text

```tsx
import { Text } from "@shopify/polaris";

// Variants
<Text as="h1" variant="headingXl">Extra Large Heading</Text>
<Text as="h2" variant="headingLg">Large Heading</Text>
<Text as="h3" variant="headingMd">Medium Heading</Text>
<Text as="h4" variant="headingSm">Small Heading</Text>
<Text as="p" variant="bodyLg">Large body</Text>
<Text as="p" variant="bodyMd">Medium body (default)</Text>
<Text as="p" variant="bodySm">Small body</Text>

// Modifiers
<Text fontWeight="bold">Bold text</Text>
<Text fontWeight="semibold">Semibold text</Text>
<Text tone="subdued">Subdued text</Text>
<Text tone="success">Success text</Text>
<Text tone="critical">Critical text</Text>
<Text tone="caution">Caution text</Text>
<Text alignment="center">Centered</Text>
<Text truncate>Very long text that will truncate...</Text>
<Text breakWord>Long text that will wrap</Text>
```

## Forms

### TextField

```tsx
import { TextField } from "@shopify/polaris";

<TextField
  label="Field label"
  name="fieldName"
  value={value}
  onChange={setValue}
  placeholder="Placeholder text"
  helpText="Help text below field"
  error="Error message"
  requiredIndicator
  disabled
  readOnly
  autoComplete="off"
  
  // Types
  type="text"                      // text|email|number|password|search|tel|url|date|datetime-local|month|time|week
  
  // Number specific
  type="number"
  min={0}
  max={100}
  step={1}
  
  // Multiline
  multiline={4}                    // Number of rows
  
  // Prefix/suffix
  prefix="$"
  suffix="kg"
  
  // Connected fields
  connectedLeft={<Select />}
  connectedRight={<Button>Apply</Button>}
  
  // Character count
  showCharacterCount
  maxLength={100}
  
  // Clear button
  clearButton
  onClearButtonClick={handleClear}
  
  // Label visibility
  labelHidden
/>
```

### Select

```tsx
import { Select } from "@shopify/polaris";

<Select
  label="Select label"
  name="selectName"
  options={[
    { label: "Option 1", value: "1" },
    { label: "Option 2", value: "2" },
    { label: "Option 3", value: "3", disabled: true },
  ]}
  value={value}
  onChange={setValue}
  placeholder="Select an option"
  helpText="Help text"
  error="Error message"
  disabled
  labelHidden
/>
```

### Checkbox

```tsx
import { Checkbox } from "@shopify/polaris";

<Checkbox
  label="Checkbox label"
  checked={checked}
  onChange={setChecked}
  helpText="Help text"
  error="Error message"
  disabled
  
  // Indeterminate (for "select all" scenarios)
  indeterminate={someSelected && !allSelected}
/>
```

### ChoiceList

```tsx
import { ChoiceList } from "@shopify/polaris";

// Multiple selection (checkboxes)
<ChoiceList
  title="Select options"
  choices={[
    { label: "Option A", value: "a" },
    { label: "Option B", value: "b" },
    { label: "Option C", value: "c", helpText: "With help text" },
  ]}
  selected={selected}
  onChange={setSelected}
  allowMultiple
  error="Error message"
/>

// Single selection (radio buttons)
<ChoiceList
  title="Choose one"
  choices={[
    { label: "Option A", value: "a" },
    { label: "Option B", value: "b" },
  ]}
  selected={[selected]}
  onChange={(value) => setSelected(value[0])}
/>
```

### RadioButton

```tsx
import { RadioButton, BlockStack } from "@shopify/polaris";

<BlockStack gap="200">
  <RadioButton
    label="Option A"
    id="optionA"
    name="options"
    checked={selected === "a"}
    onChange={() => setSelected("a")}
  />
  <RadioButton
    label="Option B"
    id="optionB"
    name="options"
    checked={selected === "b"}
    onChange={() => setSelected("b")}
  />
</BlockStack>
```

### FormLayout

```tsx
import { FormLayout, TextField } from "@shopify/polaris";

<FormLayout>
  <TextField label="First name" name="firstName" autoComplete="given-name" />
  <TextField label="Last name" name="lastName" autoComplete="family-name" />
  
  {/* Two columns */}
  <FormLayout.Group>
    <TextField label="City" name="city" autoComplete="address-level2" />
    <TextField label="State" name="state" autoComplete="address-level1" />
  </FormLayout.Group>
  
  {/* Condensed (tighter spacing) */}
  <FormLayout.Group condensed>
    <TextField label="Price" name="price" autoComplete="off" />
    <TextField label="Compare at" name="comparePrice" autoComplete="off" />
  </FormLayout.Group>
</FormLayout>
```

### DatePicker

```tsx
import { DatePicker } from "@shopify/polaris";
import { useState, useCallback } from "react";

function DatePickerExample() {
  const [{ month, year }, setDate] = useState({ month: 0, year: 2024 });
  const [selectedDates, setSelectedDates] = useState({
    start: new Date(),
    end: new Date(),
  });

  const handleMonthChange = useCallback(
    (month: number, year: number) => setDate({ month, year }),
    []
  );

  return (
    <DatePicker
      month={month}
      year={year}
      onChange={setSelectedDates}
      onMonthChange={handleMonthChange}
      selected={selectedDates}
      allowRange                   // Enable date range selection
      multiMonth                   // Show two months
      disableDatesBefore={new Date()} // Disable past dates
    />
  );
}
```

### DropZone

```tsx
import { DropZone, BlockStack, Thumbnail, Text } from "@shopify/polaris";
import { useState, useCallback } from "react";

function FileUpload() {
  const [files, setFiles] = useState<File[]>([]);

  const handleDrop = useCallback(
    (_droppedFiles: File[], acceptedFiles: File[]) => {
      setFiles((files) => [...files, ...acceptedFiles]);
    },
    []
  );

  const uploadedFiles = files.length > 0 && (
    <BlockStack gap="200">
      {files.map((file, index) => (
        <InlineStack gap="200" key={index}>
          <Thumbnail
            size="small"
            alt={file.name}
            source={window.URL.createObjectURL(file)}
          />
          <Text variant="bodySm">{file.name}</Text>
        </InlineStack>
      ))}
    </BlockStack>
  );

  return (
    <DropZone onDrop={handleDrop} accept="image/*">
      {uploadedFiles}
      <DropZone.FileUpload />
    </DropZone>
  );
}
```

## Data Display

### Badge

```tsx
import { Badge } from "@shopify/polaris";

// Tones
<Badge>Default</Badge>
<Badge tone="info">Info</Badge>
<Badge tone="success">Success</Badge>
<Badge tone="warning">Warning</Badge>
<Badge tone="critical">Critical</Badge>
<Badge tone="attention">Attention</Badge>
<Badge tone="new">New</Badge>
<Badge tone="read-only">Read only</Badge>
<Badge tone="enabled">Enabled</Badge>

// Progress (partially filled)
<Badge progress="incomplete">Incomplete</Badge>
<Badge progress="partiallyComplete">Partial</Badge>
<Badge progress="complete">Complete</Badge>

// Size
<Badge size="small">Small</Badge>
```

### Avatar

```tsx
import { Avatar } from "@shopify/polaris";

<Avatar customer name="John Doe" />
<Avatar customer initials="JD" />
<Avatar source="https://example.com/avatar.jpg" />
<Avatar size="xs" />   // xs|sm|md|lg|xl
```

### Thumbnail

```tsx
import { Thumbnail } from "@shopify/polaris";

<Thumbnail
  source="https://example.com/image.jpg"
  alt="Product image"
  size="small"         // small|medium|large
/>
```

### Icon

```tsx
import { Icon } from "@shopify/polaris";
import { PlusIcon, DeleteIcon, SearchIcon } from "@shopify/polaris-icons";

<Icon source={PlusIcon} />
<Icon source={DeleteIcon} tone="critical" />
<Icon source={SearchIcon} tone="subdued" />
```

### Tag

```tsx
import { Tag } from "@shopify/polaris";

<Tag>Basic tag</Tag>
<Tag onRemove={handleRemove}>Removable</Tag>
<Tag url="/products?tag=sale">Linked tag</Tag>
```

### DescriptionList

```tsx
import { DescriptionList } from "@shopify/polaris";

<DescriptionList
  items={[
    { term: "Shipping method", description: "Standard shipping" },
    { term: "Delivery time", description: "3-5 business days" },
    { term: "Cost", description: "$5.99" },
  ]}
/>
```

## Feedback

### Banner

```tsx
import { Banner, List } from "@shopify/polaris";

<Banner
  title="Banner title"
  tone="info"                      // info|success|warning|critical
  action={{ content: "Action", onAction: handleAction }}
  secondaryAction={{ content: "Learn more", url: "https://..." }}
  onDismiss={handleDismiss}
>
  <p>Banner content</p>
  <List>
    <List.Item>First item</List.Item>
    <List.Item>Second item</List.Item>
  </List>
</Banner>
```

### ProgressBar

```tsx
import { ProgressBar } from "@shopify/polaris";

<ProgressBar progress={75} />
<ProgressBar progress={75} size="small" />
<ProgressBar progress={75} tone="success" />
<ProgressBar progress={75} animated={false} />
```

### Spinner

```tsx
import { Spinner } from "@shopify/polaris";

<Spinner size="small" />
<Spinner size="large" />
<Spinner accessibilityLabel="Loading" />
```

## Navigation

### Tabs

```tsx
import { Tabs, Card } from "@shopify/polaris";
import { useState, useCallback } from "react";

function TabsExample() {
  const [selected, setSelected] = useState(0);
  const handleTabChange = useCallback(
    (selectedTabIndex: number) => setSelected(selectedTabIndex),
    []
  );

  const tabs = [
    { id: "all", content: "All", badge: "10" },
    { id: "active", content: "Active" },
    { id: "draft", content: "Draft" },
  ];

  return (
    <Tabs tabs={tabs} selected={selected} onSelect={handleTabChange}>
      <Card>
        {selected === 0 && <p>All content</p>}
        {selected === 1 && <p>Active content</p>}
        {selected === 2 && <p>Draft content</p>}
      </Card>
    </Tabs>
  );
}
```

### Pagination

```tsx
import { Pagination } from "@shopify/polaris";

<Pagination
  hasPrevious
  hasNext
  onPrevious={handlePrevious}
  onNext={handleNext}
  label="Page 2 of 10"
/>
```

### Link

```tsx
import { Link } from "@shopify/polaris";

<Link url="/app/products">Internal link</Link>
<Link url="https://shopify.com" external>External link</Link>
<Link onClick={handleClick}>Button-style link</Link>
<Link monochrome>Monochrome link</Link>
```

## Overlays

### Popover

```tsx
import { Popover, Button, ActionList } from "@shopify/polaris";
import { useState, useCallback } from "react";

function PopoverExample() {
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
      preferredAlignment="right"    // left|center|right
      preferredPosition="below"     // above|below|mostSpace
    >
      <ActionList
        items={[
          { content: "Edit", onAction: toggleActive },
          { content: "Delete", destructive: true, onAction: toggleActive },
        ]}
      />
    </Popover>
  );
}
```

### Tooltip

```tsx
import { Tooltip, Button } from "@shopify/polaris";

<Tooltip content="This is a tooltip">
  <Button>Hover me</Button>
</Tooltip>

<Tooltip
  content="More info"
  preferredPosition="above"
  dismissOnMouseOut
>
  <span>Info</span>
</Tooltip>
```

## Skeletons

### SkeletonPage

```tsx
import { SkeletonPage, Layout, Card, SkeletonBodyText, SkeletonDisplayText } from "@shopify/polaris";

<SkeletonPage primaryAction>
  <Layout>
    <Layout.Section>
      <Card>
        <SkeletonDisplayText size="small" />
        <SkeletonBodyText />
      </Card>
    </Layout.Section>
  </Layout>
</SkeletonPage>
```

### Individual Skeletons

```tsx
import { SkeletonDisplayText, SkeletonBodyText, SkeletonThumbnail, SkeletonTabs } from "@shopify/polaris";

<SkeletonDisplayText size="small" />  // small|medium|large|extraLarge
<SkeletonBodyText lines={3} />
<SkeletonThumbnail size="small" />    // small|medium|large
<SkeletonTabs count={3} />
```

## Common Patterns

### Resource Page with Filters

```tsx
import {
  Page,
  Card,
  IndexTable,
  IndexFilters,
  useSetIndexFiltersMode,
  useIndexResourceState,
} from "@shopify/polaris";

function ResourcePage() {
  const { mode, setMode } = useSetIndexFiltersMode();
  const [queryValue, setQueryValue] = useState("");

  return (
    <Page title="Products">
      <Card padding="0">
        <IndexFilters
          mode={mode}
          setMode={setMode}
          queryValue={queryValue}
          queryPlaceholder="Search products"
          onQueryChange={setQueryValue}
          onQueryClear={() => setQueryValue("")}
          filters={[]}
          tabs={[
            { id: "all", content: "All" },
            { id: "active", content: "Active" },
            { id: "draft", content: "Draft" },
          ]}
          selected={0}
          onSelect={() => {}}
          canCreateNewView={false}
        />
        <IndexTable {...indexTableProps} />
      </Card>
    </Page>
  );
}
```

### Settings Page Pattern

```tsx
import { Page, Layout, Card, FormLayout, TextField, Button, BlockStack, Text } from "@shopify/polaris";

function SettingsPage() {
  return (
    <Page title="Settings">
      <Layout>
        <Layout.AnnotatedSection
          title="Store details"
          description="Shopify will use this information to contact you."
        >
          <Card>
            <FormLayout>
              <TextField label="Store name" autoComplete="organization" />
              <TextField label="Email" type="email" autoComplete="email" />
            </FormLayout>
          </Card>
        </Layout.AnnotatedSection>

        <Layout.AnnotatedSection
          title="Notifications"
          description="Manage how you receive notifications."
        >
          <Card>
            <BlockStack gap="400">
              <Checkbox label="Email notifications" />
              <Checkbox label="SMS notifications" />
            </BlockStack>
          </Card>
        </Layout.AnnotatedSection>
      </Layout>
    </Page>
  );
}
```