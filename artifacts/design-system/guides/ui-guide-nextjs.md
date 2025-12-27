# Claude Code UI Implementation Guide
## Untitled UI React + Next.js (Official Approach)

**Version**: 4.0.0 (Official)  
**Target**: Claude Code autonomous UI implementation  
**Foundation**: Official Untitled UI React + Next.js 15  
**Strategy**: Use official free components + build PRO-level features

---

## Quick Start (Official CLI)

```bash
# Initialize new Next.js project with Untitled UI
npx untitledui@latest init --nextjs

# Add components as needed
npx untitledui@latest add button
npx untitledui@latest add input
npx untitledui@latest add dropdown
```

**Result:**
- Next.js 15 + App Router
- Tailwind CSS v4
- Complete theme.css with ~400 tokens
- React Aria for accessibility
- Dark mode support (next-themes)

---

## Project Structure

```
my-app/
├── app/
│   ├── layout.tsx          # Root layout + providers
│   ├── page.tsx            # Home page
│   └── globals.css         # @import tailwindcss + theme
├── components/ui/          # Untitled UI components (CLI-added)
│   ├── button.tsx
│   ├── input.tsx
│   └── ...
├── lib/utils.ts            # cx() for class merging
├── providers/
│   ├── theme-provider.tsx  # Dark mode
│   └── route-provider.tsx  # Navigation
├── styles/theme.css        # Complete design tokens
└── package.json
```

---

## Component Strategy: Three Tiers

### Tier 1: Free Components (Use CLI)

**40+ components available:**
- Base UI: Button, Input, Select, Checkbox, Radio, Toggle, Textarea
- Feedback: Badge, Avatar, Tooltip, Progress, Slider
- Navigation: Dropdown, Breadcrumbs, Tabs
- Display: Alerts, Notifications, Empty States, Code Snippets
- Marketing: Headers, Footers, Hero sections, CTAs, Testimonials

**Usage:**
```bash
npx untitledui@latest add [component-name]
```

### Tier 2: PRO Components (Build from Patterns)

**Build these yourself using free component patterns:**
- Tables (sorting, filtering, pagination)
- Charts (line, bar, pie)
- Modals, Slideouts, Command Menus
- Calendars, Date Pickers
- File Uploaders
- Dashboards, Settings Pages

**Strategy:** Reverse-engineer from free components (see below)

### Tier 3: Custom Components (Build from Scratch)

**Domain-specific UI:**
- Business logic components
- Custom visualizations
- Unique interactions

**Use:** Design tokens + React Aria primitives

---

## Building PRO-Level Components

### The Reverse-Engineering Method

When you need a PRO component (table, chart, modal):

**Step 1: Study Free Component Patterns**

Look at any free component (e.g., Button):

```tsx
// components/ui/button.tsx (official, added via CLI)

import { Button as AriaButton } from "react-aria-components";
import { cx } from "@/lib/utils";

type ButtonProps = {
  size?: "sm" | "md" | "lg";
  hierarchy?: "primary" | "secondary-gray";
  // ... props
}

export function Button({ size = "md", hierarchy = "primary", ...props }: ButtonProps) {
  const sizeClasses = {
    sm: "h-9 px-3 py-2 rounded-md text-sm",
    md: "h-10 px-3.5 py-2.5 rounded-md text-sm",
    lg: "h-11 px-4 py-2.5 rounded-md text-md",
  };
  
  const hierarchyClasses = {
    primary: "bg-brand-solid text-white hover:bg-brand-solid_hover",
    "secondary-gray": "bg-secondary text-secondary border border-secondary",
  };
  
  return (
    <AriaButton 
      className={cx(sizeClasses[size], hierarchyClasses[hierarchy])}
      {...props}
    />
  );
}
```

**Key patterns observed:**
1. ✅ React Aria primitive (`AriaButton`)
2. ✅ TypeScript prop types with defaults
3. ✅ Variant class maps (size, hierarchy)
4. ✅ Semantic token usage (`bg-brand-solid`, `text-white`)
5. ✅ `cx()` utility for class merging
6. ✅ Spread `...props` for flexibility

**Step 2: Apply Pattern to PRO Component**

Build a Data Table using the same pattern:

```tsx
// components/ui/data-table.tsx (PRO-level, built by you)

import { Table, Column, Row, Cell, TableHeader } from "react-aria-components";
import { cx } from "@/lib/utils";

type DataTableProps<T> = {
  data: T[];
  columns: Array<{ key: keyof T; name: string; width?: string }>;
  variant?: "default" | "bordered" | "striped";
}

export function DataTable<T>({ 
  data, 
  columns, 
  variant = "default" 
}: DataTableProps<T>) {
  
  const variantClasses = {
    default: "border border-secondary",
    bordered: "border-2 border-primary",
    striped: "border border-secondary [&_tbody_tr:nth-child(even)]:bg-secondary_subtle",
  };
  
  return (
    <div className={cx("rounded-lg overflow-hidden", variantClasses[variant])}>
      <Table className="w-full">
        <TableHeader className="bg-secondary border-b border-secondary">
          {columns.map(col => (
            <Column 
              key={String(col.key)}
              className="px-4 py-3 text-left text-sm font-semibold text-secondary"
            >
              {col.name}
            </Column>
          ))}
        </TableHeader>
        <tbody>
          {data.map((row, i) => (
            <Row 
              key={i}
              className="border-b border-tertiary last:border-0 hover:bg-primary_hover transition-colors"
            >
              {columns.map(col => (
                <Cell 
                  key={String(col.key)}
                  className="px-4 py-3 text-sm text-primary"
                >
                  {String(row[col.key])}
                </Cell>
              ))}
            </Row>
          ))}
        </tbody>
      </Table>
    </div>
  );
}

// Usage:
// <DataTable 
//   data={users} 
//   columns={[
//     { key: "name", name: "Name" },
//     { key: "email", name: "Email" },
//   ]}
//   variant="striped"
// />
```

**Patterns applied:**
- ✅ React Aria Table primitives
- ✅ Generic TypeScript (`<T>`)
- ✅ Variant system (default, bordered, striped)
- ✅ Semantic tokens (bg-secondary, text-primary, border-tertiary)
- ✅ Hover states (hover:bg-primary_hover)
- ✅ Consistent spacing (px-4 py-3)
- ✅ Border radius (rounded-lg)

**Step 3: Add More PRO Features**

Extend with sorting, filtering, pagination:

```tsx
import { useState } from "react";
import { Button } from "@/components/ui/button";

type SortableDataTableProps<T> = DataTableProps<T> & {
  sortable?: boolean;
  onRowClick?: (row: T) => void;
}

export function SortableDataTable<T>({ 
  data, 
  columns, 
  sortable = false,
  onRowClick,
  ...props 
}: SortableDataTableProps<T>) {
  
  const [sortKey, setSortKey] = useState<keyof T | null>(null);
  const [sortDirection, setSortDirection] = useState<"asc" | "desc">("asc");
  
  const sortedData = sortable && sortKey
    ? [...data].sort((a, b) => {
        const aVal = a[sortKey];
        const bVal = b[sortKey];
        const direction = sortDirection === "asc" ? 1 : -1;
        return aVal < bVal ? -direction : direction;
      })
    : data;
  
  const handleSort = (key: keyof T) => {
    if (sortKey === key) {
      setSortDirection(prev => prev === "asc" ? "desc" : "asc");
    } else {
      setSortKey(key);
      setSortDirection("asc");
    }
  };
  
  return (
    <div className="rounded-lg overflow-hidden border border-secondary">
      <Table className="w-full">
        <TableHeader className="bg-secondary border-b border-secondary">
          {columns.map(col => (
            <Column 
              key={String(col.key)}
              className="px-4 py-3 text-left text-sm font-semibold text-secondary"
            >
              <button
                onClick={() => sortable && handleSort(col.key)}
                className="flex items-center gap-1 hover:text-primary transition-colors"
              >
                {col.name}
                {sortable && sortKey === col.key && (
                  <span className="text-xs">
                    {sortDirection === "asc" ? "↑" : "↓"}
                  </span>
                )}
              </button>
            </Column>
          ))}
        </TableHeader>
        <tbody>
          {sortedData.map((row, i) => (
            <Row 
              key={i}
              onPress={() => onRowClick?.(row)}
              className={cx(
                "border-b border-tertiary last:border-0 hover:bg-primary_hover transition-colors",
                onRowClick && "cursor-pointer"
              )}
            >
              {columns.map(col => (
                <Cell 
                  key={String(col.key)}
                  className="px-4 py-3 text-sm text-primary"
                >
                  {String(row[col.key])}
                </Cell>
              ))}
            </Row>
          ))}
        </tbody>
      </Table>
    </div>
  );
}
```

### More PRO Component Examples

**Modal (PRO)**

```tsx
import { Dialog, Modal, ModalOverlay } from "react-aria-components";
import { cx } from "@/lib/utils";

type CustomModalProps = {
  isOpen: boolean;
  onClose: () => void;
  title: string;
  children: React.ReactNode;
  size?: "sm" | "md" | "lg";
}

export function CustomModal({ 
  isOpen, 
  onClose, 
  title, 
  children,
  size = "md" 
}: CustomModalProps) {
  
  const sizeClasses = {
    sm: "max-w-sm",
    md: "max-w-lg",
    lg: "max-w-2xl",
  };
  
  return (
    <ModalOverlay 
      isOpen={isOpen}
      onOpenChange={onClose}
      className="fixed inset-0 bg-overlay/50 flex items-center justify-center z-modal p-4"
    >
      <Modal className={cx(
        "bg-primary border border-secondary rounded-2xl shadow-2xl w-full p-6",
        sizeClasses[size]
      )}>
        <Dialog className="outline-none">
          <div className="flex items-center justify-between mb-4">
            <h2 className="text-lg font-semibold text-primary">{title}</h2>
            <button
              onClick={onClose}
              className="text-tertiary hover:text-primary transition-colors"
            >
              ✕
            </button>
          </div>
          {children}
        </Dialog>
      </Modal>
    </ModalOverlay>
  );
}
```

**Command Menu (PRO)**

```tsx
import { Dialog, Input, ListBox, ListBoxItem } from "react-aria-components";
import { useState } from "react";

type CommandItem = {
  id: string;
  label: string;
  icon?: string;
  onSelect: () => void;
}

type CommandMenuProps = {
  isOpen: boolean;
  onClose: () => void;
  items: CommandItem[];
  placeholder?: string;
}

export function CommandMenu({ 
  isOpen, 
  onClose, 
  items,
  placeholder = "Search commands..." 
}: CommandMenuProps) {
  
  const [search, setSearch] = useState("");
  
  const filteredItems = items.filter(item =>
    item.label.toLowerCase().includes(search.toLowerCase())
  );
  
  return (
    <ModalOverlay 
      isOpen={isOpen}
      onOpenChange={onClose}
      className="fixed inset-0 bg-overlay/50 flex items-start justify-center pt-[20vh] z-modal"
    >
      <Dialog className="bg-primary border border-secondary rounded-lg shadow-2xl w-full max-w-lg overflow-hidden">
        <Input
          autoFocus
          value={search}
          onChange={(e) => setSearch(e.target.value)}
          placeholder={placeholder}
          className="w-full px-4 py-3 border-b border-secondary text-md outline-none"
        />
        <ListBox className="max-h-80 overflow-y-auto p-2">
          {filteredItems.map(item => (
            <ListBoxItem
              key={item.id}
              onAction={() => {
                item.onSelect();
                onClose();
              }}
              className="px-3 py-2 rounded-md hover:bg-primary_hover cursor-pointer transition-colors"
            >
              <div className="flex items-center gap-2">
                {item.icon && <span className="text-tertiary">{item.icon}</span>}
                <span className="text-sm text-primary">{item.label}</span>
              </div>
            </ListBoxItem>
          ))}
          {filteredItems.length === 0 && (
            <div className="px-3 py-8 text-center text-sm text-tertiary">
              No results found
            </div>
          )}
        </ListBox>
      </Dialog>
    </ModalOverlay>
  );
}
```

---

## Design System Token Usage

### Semantic Color Tokens (Always Use These)

```tsx
// Background colors
className="bg-primary"           // Main background
className="bg-secondary"         // Secondary background
className="bg-tertiary"          // Tertiary background
className="bg-brand-solid"       // Brand color
className="bg-error-primary"     // Error state

// Text colors
className="text-primary"         // Main text
className="text-secondary"       // Secondary text
className="text-tertiary"        // Tertiary text
className="text-brand-primary"   // Brand text

// Border colors
className="border-primary"       // Main border
className="border-secondary"     // Secondary border
className="border-brand"         // Brand border

// States
className="hover:bg-primary_hover"
className="focus:ring-brand"
className="disabled:bg-disabled"
```

### Border Radius Scale

```tsx
className="rounded-sm"    // 4px - Small elements
className="rounded-md"    // 6px - Buttons, inputs
className="rounded-lg"    // 8px - Cards
className="rounded-xl"    // 12px - Large cards
className="rounded-2xl"   // 16px - Modals, panels
className="rounded-3xl"   // 20px - Large panels
className="rounded-4xl"   // 24px - Hero sections
className="rounded-full"  // 9999px - Pills, avatars
```

### Spacing Scale

```tsx
// Numeric scale (Tailwind defaults)
className="p-4"       // 16px
className="px-3.5"    // 14px horizontal
className="py-2.5"    // 10px vertical
className="gap-2"     // 8px gap

// Named tokens (semantic)
className="p-md"      // --spacing-md (8px)
className="p-lg"      // --spacing-lg (12px)
className="p-xl"      // --spacing-xl (16px)
```

### Component Sizing Patterns

```tsx
// Buttons
sm:  "h-9 px-3 py-2"      // 36px height
md:  "h-10 px-3.5 py-2.5" // 40px height
lg:  "h-11 px-4 py-2.5"   // 44px height

// Inputs
sm:  "h-9 px-3 py-2"
md:  "h-10 px-3.5 py-2.5"
lg:  "h-12 px-4 py-3"

// Cards
className="p-6"           // Standard card padding
className="p-4"           // Compact card
className="p-8"           // Large card
```

---

## React Aria Primitives

Use these for accessibility:

```tsx
import {
  // Buttons
  Button,
  
  // Forms
  TextField, TextArea, Select, ComboBox,
  Checkbox, RadioGroup, Radio, Switch,
  
  // Overlays
  Dialog, Modal, ModalOverlay, Popover,
  
  // Collections
  Table, Column, Row, Cell, TableHeader,
  ListBox, ListBoxItem, Menu, MenuItem,
  
  // Date & Time
  DatePicker, Calendar, TimeField,
  
  // Utilities
  Label, Input, Group, FieldError,
} from "react-aria-components";
```

---

## Production Checklist

### Before Deployment

- [ ] All components use semantic color tokens (not hardcoded colors)
- [ ] Dark mode tested (add `.dark-mode` class to test)
- [ ] Accessibility verified (keyboard navigation, screen readers)
- [ ] Responsive breakpoints tested (sm, md, lg, xl, 2xl)
- [ ] Loading states implemented
- [ ] Error states implemented
- [ ] Empty states implemented
- [ ] Icons loaded via `@untitledui/icons` package

### Performance

- [ ] Components use `"use client"` only when needed
- [ ] Server Components used for static content
- [ ] Images optimized with `next/image`
- [ ] Fonts loaded via `next/font`
- [ ] CSS is bundled (using Tailwind v4)

### Code Quality

- [ ] TypeScript types defined for all props
- [ ] `cx()` used for conditional classes
- [ ] No magic numbers (use spacing tokens)
- [ ] Consistent naming (PascalCase for components)
- [ ] Props spread with `...props` for flexibility

---

## Quick Reference

**Add component:**
```bash
npx untitledui@latest add [component]
```

**Common imports:**
```tsx
import { cx } from "@/lib/utils";
import { Button } from "@/components/ui/button";
import { Button as AriaButton } from "react-aria-components";
```

**Token usage:**
```tsx
bg-{primary|secondary|tertiary|brand-solid}
text-{primary|secondary|tertiary|brand-primary}
border-{primary|secondary|brand}
rounded-{sm|md|lg|xl|2xl|3xl|4xl|full}
```

**Build PRO component:**
1. Study free component pattern
2. Use React Aria primitives
3. Apply semantic tokens
4. Add variant system
5. Include accessibility features
