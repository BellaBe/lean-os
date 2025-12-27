# Untitled UI + Next.js Quick Reference

**Version**: 4.0.0  
**Purpose**: Fast lookups for component implementation

---

## Setup Commands

```bash
# New project
npx untitledui@latest init --nextjs

# Add components
npx untitledui@latest add button
npx untitledui@latest add input
npx untitledui@latest add dropdown

# Add icons (npm package)
# Already installed via init
import { Check, X, Search } from "@untitledui/icons";
```

---

## File Structure

```
app/
├── layout.tsx         # Theme provider
├── page.tsx           # Home
└── globals.css        # @import tailwindcss + theme

components/ui/         # CLI-added components
lib/utils.ts           # cx() utility
styles/theme.css       # Design tokens (~400 variables)
```

---

## Component Tiers

**Free (40+):** Button, Input, Select, Checkbox, Badge, Avatar, Dropdown, Tooltip, Progress, Tabs, Alerts

**PRO (Build yourself):** Tables, Charts, Modals, Calendars, File Uploaders, Dashboards

**Custom:** Domain-specific components

---

## Token Quick Lookup

### Colors (Semantic Only)

```tsx
// Backgrounds
bg-primary              // Main
bg-secondary            // Secondary
bg-brand-solid          // Brand
bg-error-primary        // Error

// Text
text-primary            // Main
text-secondary          // Secondary
text-brand-primary      // Brand

// Borders
border-primary
border-secondary
border-brand

// States
hover:bg-primary_hover
focus:ring-brand
disabled:bg-disabled
```

### Border Radius

```tsx
rounded-sm       // 4px - small
rounded-md       // 6px - buttons, inputs
rounded-lg       // 8px - cards
rounded-xl       // 12px - large cards
rounded-2xl      // 16px - modals
rounded-3xl      // 20px - panels
rounded-full     // pills, avatars
```

### Spacing

```tsx
// Common patterns
p-4              // 16px padding
p-6              // 24px padding (cards)
px-3.5 py-2.5    // Button medium
px-4 py-3        // Button large
gap-2            // 8px gap
gap-4            // 16px gap
```

### Component Sizes

```tsx
// Buttons & Inputs
sm:  h-9 px-3 py-2
md:  h-10 px-3.5 py-2.5
lg:  h-11 px-4 py-2.5
xl:  h-12 px-4 py-3
```

---

## Build PRO Component Pattern

**1. Use React Aria primitive**
```tsx
import { Table, Column, Row } from "react-aria-components";
```

**2. Add TypeScript types**
```tsx
type MyComponentProps = {
  variant?: "default" | "bordered";
  size?: "sm" | "md" | "lg";
}
```

**3. Create variant maps**
```tsx
const variantClasses = {
  default: "border border-secondary",
  bordered: "border-2 border-primary",
};
```

**4. Use semantic tokens**
```tsx
className="bg-primary text-primary border-secondary rounded-lg"
```

**5. Add `cx()` for merging**
```tsx
import { cx } from "@/lib/utils";
className={cx(variantClasses[variant], "base-classes")}
```

---

## Common Imports

```tsx
// Utilities
import { cx } from "@/lib/utils";

// Free components (CLI-added)
import { Button } from "@/components/ui/button";
import { Input } from "@/components/ui/input";

// React Aria primitives
import { 
  Button, Dialog, Table, Select, Menu 
} from "react-aria-components";

// Icons
import { Check, X, Search } from "@untitledui/icons";
```

---

## React Aria Primitives Reference

```tsx
// Buttons
Button

// Forms
TextField, TextArea, Select, ComboBox
Checkbox, RadioGroup, Radio, Switch

// Overlays
Dialog, Modal, ModalOverlay, Popover

// Collections
Table, Column, Row, Cell, TableHeader
ListBox, ListBoxItem
Menu, MenuItem

// Date
DatePicker, Calendar, TimeField

// Utilities
Label, Input, Group, FieldError
```

---

## PRO Component Examples

### Data Table

```tsx
import { Table, Column, Row, Cell } from "react-aria-components";

<Table className="w-full">
  <TableHeader className="bg-secondary border-b border-secondary">
    <Column className="px-4 py-3 text-sm font-semibold">Name</Column>
  </TableHeader>
  <tbody>
    <Row className="hover:bg-primary_hover">
      <Cell className="px-4 py-3 text-sm">Value</Cell>
    </Row>
  </tbody>
</Table>
```

### Modal

```tsx
import { Dialog, Modal, ModalOverlay } from "react-aria-components";

<ModalOverlay className="fixed inset-0 bg-overlay/50 flex items-center justify-center z-modal">
  <Modal className="bg-primary border border-secondary rounded-2xl shadow-2xl max-w-lg p-6">
    <Dialog>
      <h2 className="text-lg font-semibold mb-4">Title</h2>
      {children}
    </Dialog>
  </Modal>
</ModalOverlay>
```

### Command Menu

```tsx
import { Dialog, Input, ListBox, ListBoxItem } from "react-aria-components";

<Dialog className="bg-primary rounded-lg">
  <Input 
    placeholder="Search..." 
    className="w-full px-4 py-3 border-b border-secondary"
  />
  <ListBox className="p-2">
    <ListBoxItem className="px-3 py-2 rounded-md hover:bg-primary_hover">
      Item
    </ListBoxItem>
  </ListBox>
</Dialog>
```

---

## Dark Mode

```tsx
// Add to any element to test dark mode
className="dark-mode"

// Or use ThemeProvider (included in init)
import { useTheme } from "next-themes";
const { theme, setTheme } = useTheme();
```

---

## Common Patterns

### Card

```tsx
<div className="bg-primary border border-secondary rounded-lg shadow-sm p-6">
  {content}
</div>
```

### Form Field

```tsx
<div className="space-y-2">
  <label className="text-sm font-medium text-secondary">Label</label>
  <Input className="w-full h-10 px-3.5 py-2.5 border border-primary rounded-md" />
  <p className="text-xs text-tertiary">Helper text</p>
</div>
```

### Empty State

```tsx
<div className="text-center py-12">
  <div className="text-tertiary mb-2">Icon</div>
  <h3 className="text-sm font-semibold text-primary mb-1">No items</h3>
  <p className="text-sm text-tertiary">Get started by creating one</p>
</div>
```

---

## Troubleshooting

**Component not found:**
```bash
npx untitledui@latest add [component-name]
```

**Dark mode not working:**
- Check `ThemeProvider` in `app/layout.tsx`
- Verify `theme.css` imported in `globals.css`
- Test with `className="dark-mode"`

**Tokens not working:**
- Verify `@import "./theme.css"` in `globals.css`
- Check `theme.css` exists in `styles/`
- Restart dev server

**Icons not showing:**
```bash
npm install @untitledui/icons
```

---

## Production Checklist

- [ ] Use semantic tokens (not raw colors)
- [ ] Test dark mode
- [ ] Keyboard navigation works
- [ ] Screen reader tested
- [ ] Mobile responsive
- [ ] Loading/error/empty states
- [ ] TypeScript types defined
- [ ] `cx()` for conditional classes
