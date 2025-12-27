# Untitled UI Agent Guide
## Design Expertise & Component Implementation

**Version**: 4.0.0  
**Purpose**: Design system knowledge + PRO component building strategies  
**Audience**: AI agents (Claude Code, etc.)

---

## System Overview

**Foundation:** Official Untitled UI React + Next.js 15

**Component Sources:**
1. **Free (40+):** Via `npx untitledui@latest add [component]`
2. **PRO (200+):** Build using patterns from free components
3. **Custom:** Build from scratch using design tokens

**Design System:** ~400 CSS variables in `styles/theme.css`

---

## Design Philosophy

### Core Principles

**1. Semantic Over Specific**
```tsx
// ✅ Correct - Semantic tokens
className="bg-primary text-primary border-primary"

// ❌ Wrong - Hardcoded colors
className="bg-gray-50 text-gray-900 border-gray-200"
```

**Rationale:** Semantic tokens adapt to light/dark mode and brand changes automatically.

**2. Token-Driven Spacing**
```tsx
// ✅ Correct - Consistent spacing
className="p-6 gap-4"      // Card padding + gap

// ❌ Wrong - Random values
className="p-[23px] gap-[17px]"
```

**Rationale:** Token-based spacing maintains visual rhythm across the entire UI.

**3. Accessibility First**
```tsx
// ✅ Correct - React Aria primitive
import { Button } from "react-aria-components";

// ❌ Wrong - Plain HTML
<button>Click</button>
```

**Rationale:** React Aria handles keyboard navigation, focus management, ARIA attributes automatically.

---

## Token System Reference

### Color Hierarchy

**Background Tokens:**
```tsx
--color-bg-primary           // Main background (white in light, dark in dark mode)
--color-bg-secondary         // Secondary background (gray-50 in light)
--color-bg-tertiary          // Tertiary background (gray-100 in light)
--color-bg-quaternary        // Quaternary background (gray-200 in light)

--color-bg-brand-solid       // Brand color (brand-600)
--color-bg-brand-primary     // Light brand (brand-50)
--color-bg-brand-secondary   // Medium brand (brand-100)

--color-bg-error-primary     // Error background (error-50)
--color-bg-success-primary   // Success background (success-50)
--color-bg-warning-primary   // Warning background (warning-50)

// States
--color-bg-primary_hover     // Hover state
--color-bg-disabled          // Disabled state
--color-bg-active            // Active/selected state
--color-bg-overlay           // Modal overlay (rgba)
```

**Text Tokens:**
```tsx
--color-text-primary         // Main text (gray-900 in light)
--color-text-secondary       // Secondary text (gray-700)
--color-text-tertiary        // Tertiary text (gray-600)
--color-text-quaternary      // Quaternary text (gray-500)

--color-text-brand-primary   // Brand text (brand-900)
--color-text-brand-secondary // Brand text secondary (brand-700)

--color-text-error-primary   // Error text (error-600)
--color-text-disabled        // Disabled text (gray-500)
--color-text-placeholder     // Placeholder text (gray-500)
```

**Border Tokens:**
```tsx
--color-border-primary       // Main border (gray-300)
--color-border-secondary     // Secondary border (gray-200)
--color-border-tertiary      // Tertiary border (gray-100)
--color-border-brand         // Brand border (brand-500)
--color-border-error         // Error border (error-500)
--color-border-disabled      // Disabled border (gray-300)
```

### Spacing Scale

```tsx
--spacing-none:  0px
--spacing-xxs:   2px
--spacing-xs:    4px
--spacing-sm:    6px
--spacing-md:    8px
--spacing-lg:    12px
--spacing-xl:    16px
--spacing-2xl:   20px
--spacing-3xl:   24px
--spacing-4xl:   32px
--spacing-5xl:   40px
--spacing-6xl:   48px
--spacing-7xl:   64px
--spacing-8xl:   80px
--spacing-9xl:   96px
--spacing-10xl:  128px
--spacing-11xl:  160px
```

### Border Radius Scale

```tsx
--radius-none:  0px
--radius-sm:    4px      // Small elements (badges, pills)
--radius-md:    6px      // Buttons, inputs, selects
--radius-lg:    8px      // Cards, containers
--radius-xl:    12px     // Large cards
--radius-2xl:   16px     // Modals, panels
--radius-3xl:   20px     // Large panels
--radius-4xl:   24px     // Hero sections
--radius-full:  9999px   // Pills, avatars, progress bars
```

### Typography Scale

```tsx
// Text sizes
--text-xs:   12px / 18px line-height
--text-sm:   14px / 20px line-height
--text-md:   16px / 24px line-height
--text-lg:   18px / 28px line-height
--text-xl:   20px / 30px line-height

// Display sizes
--display-xs:   24px / 32px line-height
--display-sm:   30px / 38px line-height
--display-md:   36px / 44px line-height
--display-lg:   48px / 60px line-height
--display-xl:   60px / 72px line-height
--display-2xl:  72px / 90px line-height

// Font weights
--font-regular:   400
--font-medium:    500
--font-semibold:  600
--font-bold:      700
```

---

## Component Specification Format

### Standard Component Structure

Every component follows this pattern:

```tsx
// 1. Imports
import { ComponentType } from "react-aria-components";
import { cx } from "@/lib/utils";
import type { ComponentProps } from "react";

// 2. TypeScript types
type MyComponentProps = ComponentProps<typeof ComponentType> & {
  variant?: "default" | "bordered" | "elevated";
  size?: "sm" | "md" | "lg";
  // ... custom props
}

// 3. Variant class definitions
const variants = {
  default: "bg-primary border border-secondary",
  bordered: "bg-secondary border-2 border-primary",
  elevated: "bg-primary shadow-lg",
};

const sizes = {
  sm: "h-9 px-3 py-2 text-sm",
  md: "h-10 px-3.5 py-2.5 text-sm",
  lg: "h-11 px-4 py-2.5 text-md",
};

// 4. Component with default props
export function MyComponent({ 
  variant = "default",
  size = "md",
  className,
  ...props 
}: MyComponentProps) {
  return (
    <ComponentType 
      className={cx(
        variants[variant],
        sizes[size],
        className
      )}
      {...props}
    />
  );
}
```

---

## Building PRO Components

### Methodology: Pattern Extraction

**When you need a PRO component (table, chart, modal, calendar):**

### Step 1: Identify Required React Aria Primitives

```tsx
// Data Table
import { Table, Column, Row, Cell, TableHeader } from "react-aria-components";

// Modal/Dialog
import { Dialog, Modal, ModalOverlay } from "react-aria-components";

// Command Menu
import { Dialog, Input, ListBox, ListBoxItem } from "react-aria-components";

// Calendar/Date Picker
import { Calendar, DatePicker, DateInput, DateSegment } from "react-aria-components";

// Charts (no React Aria - use Recharts)
import { LineChart, BarChart, PieChart } from "recharts";

// File Upload (use plain HTML + custom styling)
<input type="file" />
```

### Step 2: Apply Design System Tokens

**Container Styling:**
```tsx
className={cx(
  // Background
  "bg-primary",
  
  // Border
  "border border-secondary",
  
  // Radius
  "rounded-lg",
  
  // Shadow
  "shadow-sm",
  
  // Padding
  "p-6",
)}
```

**Interactive Elements:**
```tsx
className={cx(
  // Default state
  "bg-secondary text-secondary",
  
  // Hover
  "hover:bg-primary_hover hover:text-primary",
  
  // Focus
  "focus:ring-2 focus:ring-brand",
  
  // Active
  "active:bg-active",
  
  // Disabled
  "disabled:bg-disabled disabled:text-disabled disabled:cursor-not-allowed",
  
  // Transitions
  "transition-colors duration-200",
)}
```

### Step 3: Create Variant System

```tsx
type ComponentVariant = "default" | "bordered" | "elevated" | "striped";

const variantStyles: Record<ComponentVariant, string> = {
  default: "border border-secondary",
  
  bordered: cx(
    "border-2 border-primary",
    "shadow-sm"
  ),
  
  elevated: cx(
    "border border-secondary",
    "shadow-lg"
  ),
  
  striped: cx(
    "border border-secondary",
    "[&_tbody_tr:nth-child(even)]:bg-secondary_subtle"
  ),
};
```

### Step 4: Add Size Variants

```tsx
type ComponentSize = "sm" | "md" | "lg";

const sizeStyles: Record<ComponentSize, {
  container: string;
  text: string;
  padding: string;
}> = {
  sm: {
    container: "h-9",
    text: "text-xs",
    padding: "px-3 py-2",
  },
  md: {
    container: "h-10",
    text: "text-sm",
    padding: "px-3.5 py-2.5",
  },
  lg: {
    container: "h-12",
    text: "text-md",
    padding: "px-4 py-3",
  },
};
```

---

## PRO Component Implementations

### Data Table with Sorting

```tsx
import { Table, Column, Row, Cell, TableHeader } from "react-aria-components";
import { useState } from "react";
import { cx } from "@/lib/utils";

type SortDirection = "asc" | "desc";

type DataTableProps<T> = {
  data: T[];
  columns: Array<{
    key: keyof T;
    name: string;
    sortable?: boolean;
    width?: string;
  }>;
  variant?: "default" | "bordered" | "striped";
  onRowClick?: (row: T) => void;
}

export function DataTable<T extends Record<string, any>>({ 
  data, 
  columns,
  variant = "default",
  onRowClick 
}: DataTableProps<T>) {
  
  const [sortKey, setSortKey] = useState<keyof T | null>(null);
  const [sortDir, setSortDir] = useState<SortDirection>("asc");
  
  const sortedData = sortKey
    ? [...data].sort((a, b) => {
        const aVal = a[sortKey];
        const bVal = b[sortKey];
        const multiplier = sortDir === "asc" ? 1 : -1;
        return aVal < bVal ? -multiplier : multiplier;
      })
    : data;
  
  const handleSort = (key: keyof T) => {
    if (sortKey === key) {
      setSortDir(prev => prev === "asc" ? "desc" : "asc");
    } else {
      setSortKey(key);
      setSortDir("asc");
    }
  };
  
  const variantStyles = {
    default: "border border-secondary",
    bordered: "border-2 border-primary shadow-sm",
    striped: "border border-secondary [&_tbody_tr:nth-child(even)]:bg-secondary_subtle",
  };
  
  return (
    <div className={cx("rounded-lg overflow-hidden", variantStyles[variant])}>
      <Table className="w-full">
        <TableHeader className="bg-secondary border-b border-secondary">
          {columns.map(col => (
            <Column 
              key={String(col.key)}
              className={cx(
                "px-4 py-3 text-left text-sm font-semibold text-secondary",
                col.width && `w-${col.width}`
              )}
            >
              {col.sortable ? (
                <button
                  onClick={() => handleSort(col.key)}
                  className="flex items-center gap-2 hover:text-primary transition-colors"
                >
                  {col.name}
                  {sortKey === col.key && (
                    <span className="text-brand-primary">
                      {sortDir === "asc" ? "↑" : "↓"}
                    </span>
                  )}
                </button>
              ) : (
                col.name
              )}
            </Column>
          ))}
        </TableHeader>
        <tbody>
          {sortedData.map((row, i) => (
            <Row 
              key={i}
              onPress={() => onRowClick?.(row)}
              className={cx(
                "border-b border-tertiary last:border-0",
                "hover:bg-primary_hover transition-colors",
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
      
      {sortedData.length === 0 && (
        <div className="text-center py-12 text-tertiary">
          <p className="text-sm">No data available</p>
        </div>
      )}
    </div>
  );
}
```

### Modal with Sizes

```tsx
import { Dialog, Modal, ModalOverlay } from "react-aria-components";
import { cx } from "@/lib/utils";
import { X } from "@untitledui/icons";

type ModalProps = {
  isOpen: boolean;
  onClose: () => void;
  title: string;
  description?: string;
  children: React.ReactNode;
  size?: "sm" | "md" | "lg" | "xl";
  footer?: React.ReactNode;
}

export function CustomModal({
  isOpen,
  onClose,
  title,
  description,
  children,
  size = "md",
  footer
}: ModalProps) {
  
  const sizeStyles = {
    sm: "max-w-sm",
    md: "max-w-lg",
    lg: "max-w-2xl",
    xl: "max-w-4xl",
  };
  
  return (
    <ModalOverlay 
      isOpen={isOpen}
      onOpenChange={onClose}
      className={cx(
        "fixed inset-0 bg-overlay/50",
        "flex items-center justify-center",
        "z-modal p-4",
        "backdrop-blur-sm"
      )}
    >
      <Modal className={cx(
        "bg-primary border border-secondary",
        "rounded-2xl shadow-2xl",
        "w-full overflow-hidden",
        sizeStyles[size]
      )}>
        <Dialog className="outline-none">
          {/* Header */}
          <div className="flex items-start justify-between p-6 border-b border-tertiary">
            <div className="flex-1">
              <h2 className="text-lg font-semibold text-primary">
                {title}
              </h2>
              {description && (
                <p className="mt-1 text-sm text-tertiary">
                  {description}
                </p>
              )}
            </div>
            <button
              onClick={onClose}
              className={cx(
                "text-quaternary hover:text-primary",
                "transition-colors",
                "p-1 rounded-md hover:bg-secondary"
              )}
            >
              <X className="w-5 h-5" />
            </button>
          </div>
          
          {/* Content */}
          <div className="p-6">
            {children}
          </div>
          
          {/* Footer */}
          {footer && (
            <div className="flex items-center justify-end gap-3 p-6 border-t border-tertiary bg-secondary_subtle">
              {footer}
            </div>
          )}
        </Dialog>
      </Modal>
    </ModalOverlay>
  );
}
```

### Command Menu (⌘K)

```tsx
import { Dialog, Input, ListBox, ListBoxItem } from "react-aria-components";
import { useState, useEffect } from "react";
import { cx } from "@/lib/utils";
import { Search } from "@untitledui/icons";

type CommandItem = {
  id: string;
  label: string;
  icon?: React.ReactNode;
  shortcut?: string;
  category?: string;
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
  
  // Close on Escape
  useEffect(() => {
    const handleEscape = (e: KeyboardEvent) => {
      if (e.key === "Escape") onClose();
    };
    document.addEventListener("keydown", handleEscape);
    return () => document.removeEventListener("keydown", handleEscape);
  }, [onClose]);
  
  const filteredItems = items.filter(item =>
    item.label.toLowerCase().includes(search.toLowerCase())
  );
  
  // Group by category
  const groupedItems = filteredItems.reduce((acc, item) => {
    const category = item.category || "General";
    if (!acc[category]) acc[category] = [];
    acc[category].push(item);
    return acc;
  }, {} as Record<string, CommandItem[]>);
  
  return (
    <ModalOverlay 
      isOpen={isOpen}
      onOpenChange={onClose}
      className={cx(
        "fixed inset-0 bg-overlay/50",
        "flex items-start justify-center pt-[20vh]",
        "z-modal p-4"
      )}
    >
      <Dialog className={cx(
        "bg-primary border border-secondary",
        "rounded-lg shadow-2xl",
        "w-full max-w-lg overflow-hidden"
      )}>
        {/* Search Input */}
        <div className="relative border-b border-secondary">
          <Search className="absolute left-4 top-1/2 -translate-y-1/2 w-5 h-5 text-quaternary" />
          <Input
            autoFocus
            value={search}
            onChange={(e) => setSearch(e.target.value)}
            placeholder={placeholder}
            className={cx(
              "w-full pl-12 pr-4 py-3",
              "text-md text-primary placeholder:text-placeholder",
              "outline-none bg-transparent"
            )}
          />
        </div>
        
        {/* Results */}
        <div className="max-h-80 overflow-y-auto">
          {Object.entries(groupedItems).map(([category, categoryItems]) => (
            <div key={category}>
              <div className="px-4 py-2 text-xs font-semibold text-tertiary uppercase">
                {category}
              </div>
              <ListBox className="px-2 pb-2">
                {categoryItems.map(item => (
                  <ListBoxItem
                    key={item.id}
                    onAction={() => {
                      item.onSelect();
                      onClose();
                    }}
                    className={cx(
                      "flex items-center justify-between",
                      "px-3 py-2 rounded-md",
                      "hover:bg-primary_hover cursor-pointer",
                      "transition-colors group"
                    )}
                  >
                    <div className="flex items-center gap-3">
                      {item.icon && (
                        <span className="text-tertiary group-hover:text-secondary">
                          {item.icon}
                        </span>
                      )}
                      <span className="text-sm text-primary">
                        {item.label}
                      </span>
                    </div>
                    {item.shortcut && (
                      <kbd className="px-2 py-0.5 text-xs font-medium text-tertiary bg-secondary rounded border border-tertiary">
                        {item.shortcut}
                      </kbd>
                    )}
                  </ListBoxItem>
                ))}
              </ListBox>
            </div>
          ))}
          
          {/* Empty State */}
          {filteredItems.length === 0 && (
            <div className="px-4 py-12 text-center">
              <p className="text-sm text-tertiary">No results found</p>
              <p className="text-xs text-quaternary mt-1">
                Try a different search term
              </p>
            </div>
          )}
        </div>
      </Dialog>
    </ModalOverlay>
  );
}
```

---

## Design Patterns

### Empty States

```tsx
<div className="flex flex-col items-center justify-center py-12 px-4 text-center">
  <div className="w-12 h-12 rounded-full bg-tertiary flex items-center justify-center mb-4">
    <Icon className="w-6 h-6 text-quaternary" />
  </div>
  <h3 className="text-sm font-semibold text-primary mb-1">
    No items yet
  </h3>
  <p className="text-sm text-tertiary max-w-sm">
    Get started by creating your first item
  </p>
  <Button className="mt-4" size="sm">
    Create Item
  </Button>
</div>
```

### Loading States

```tsx
<div className="flex items-center justify-center py-12">
  <div className="animate-spin rounded-full h-8 w-8 border-2 border-brand-solid border-t-transparent" />
</div>
```

### Error States

```tsx
<div className="bg-error-primary border border-error text-error-primary rounded-lg p-4">
  <div className="flex items-start gap-3">
    <Icon className="w-5 h-5 flex-shrink-0" />
    <div>
      <h4 className="text-sm font-semibold">Error occurred</h4>
      <p className="text-sm mt-1">Error message details</p>
    </div>
  </div>
</div>
```

---

## Agent Instructions

### When Building Components

1. **Always use official CLI for free components**
   - Never manually recreate Button, Input, etc.
   - Use `npx untitledui@latest add [component]`

2. **For PRO components, follow the pattern extraction method**
   - Study free components first
   - Use React Aria primitives
   - Apply semantic tokens consistently
   - Create variant system
   - Add size variants
   - Include states (hover, focus, disabled)

3. **Token usage rules**
   - Always use semantic tokens (`bg-primary` not `bg-gray-50`)
   - Never hardcode pixel values
   - Use spacing scale consistently
   - Follow radius hierarchy

4. **Accessibility requirements**
   - Always use React Aria when possible
   - Include keyboard navigation
   - Add ARIA attributes
   - Test with screen readers

5. **TypeScript requirements**
   - Define prop types
   - Use generic types for collections
   - Export types alongside components
   - Use `ComponentProps<typeof X>` for extending
