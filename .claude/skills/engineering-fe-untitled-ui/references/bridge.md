# Design System → React Bridge Patterns

Complete examples of translating design system JSON specs to React components.

## Pattern 1: Atom (Button)

### Design System Spec

```json
{
  "meta": { "name": "Button", "category": "atom" },
  "variants": {
    "size": ["sm", "md", "lg", "xl", "2xl"],
    "hierarchy": ["primary", "secondary-color", "secondary-gray", "tertiary-color", "tertiary-gray"]
  },
  "props": {
    "children": { "type": "string", "required": true },
    "size": { "type": "enum", "default": "md" },
    "hierarchy": { "type": "enum", "default": "primary" },
    "disabled": { "type": "boolean", "default": false },
    "leadingIcon": { "type": "string" },
    "trailingIcon": { "type": "string" }
  },
  "sizing": {
    "sm": { "height": "Button/height-sm", "paddingX": "spacing-lg", "typography": "Text sm/Semibold" },
    "md": { "height": "Button/height-md", "paddingX": "spacing-xl", "typography": "Text sm/Semibold" },
    "lg": { "height": "Button/height-lg", "paddingX": "spacing-2xl", "typography": "Text md/Semibold" }
  },
  "tokens": {
    "primary": {
      "default": { "background": "bg-brand-solid", "text": "text-white" },
      "hover": { "background": "bg-brand-solid_hover" },
      "disabled": { "background": "bg-disabled", "text": "text-disabled" }
    },
    "secondary-gray": {
      "default": { "background": "bg-primary", "text": "text-secondary", "border": "border-primary" },
      "hover": { "background": "bg-primary_hover" }
    }
  }
}
```

### React Implementation

```tsx
"use client";

import { Button as AriaButton, type ButtonProps as AriaButtonProps } from "react-aria-components";
import { cx } from "@/lib/utils";

type ButtonProps = AriaButtonProps & {
  size?: "sm" | "md" | "lg" | "xl" | "2xl";
  hierarchy?: "primary" | "secondary-color" | "secondary-gray" | "tertiary-color" | "tertiary-gray";
  leadingIcon?: React.ReactNode;
  trailingIcon?: React.ReactNode;
};

const sizes = {
  sm: "h-9 px-3 gap-1 text-sm font-semibold",
  md: "h-10 px-4 gap-2 text-sm font-semibold",
  lg: "h-11 px-5 gap-2 text-md font-semibold",
  xl: "h-12 px-5 gap-2 text-md font-semibold",
  "2xl": "h-14 px-6 gap-3 text-lg font-semibold",
};

const hierarchies = {
  primary: "bg-brand-solid text-white hover:bg-brand-solid_hover disabled:bg-disabled disabled:text-disabled",
  "secondary-color": "bg-brand-secondary text-brand-secondary border border-brand hover:bg-brand-primary",
  "secondary-gray": "bg-primary text-secondary border border-primary hover:bg-primary_hover",
  "tertiary-color": "text-brand-secondary hover:bg-brand-primary",
  "tertiary-gray": "text-tertiary hover:bg-primary_hover",
};

export function Button({
  size = "md",
  hierarchy = "primary",
  leadingIcon,
  trailingIcon,
  children,
  className,
  ...props
}: ButtonProps) {
  return (
    <AriaButton
      className={cx(
        "inline-flex items-center justify-center rounded-md transition-colors",
        "focus:outline-none focus:ring-2 focus:ring-brand focus:ring-offset-2",
        "disabled:cursor-not-allowed",
        sizes[size],
        hierarchies[hierarchy],
        className
      )}
      {...props}
    >
      {leadingIcon}
      {children}
      {trailingIcon}
    </AriaButton>
  );
}
```

## Pattern 2: Molecule (Alert)

### Design System Spec

```json
{
  "meta": { "name": "Alert", "category": "molecule" },
  "dependencies": { "atoms": ["Icon", "Button"] },
  "variants": {
    "type": ["info", "success", "warning", "error"],
    "style": ["light", "filled"]
  },
  "props": {
    "title": { "type": "string" },
    "description": { "type": "string", "required": true },
    "type": { "type": "enum", "default": "info" },
    "dismissible": { "type": "boolean", "default": false },
    "action": { "type": "object" }
  },
  "tokens": {
    "info": { "background": "bg-brand-primary", "border": "border-brand", "icon": "fg-brand-primary" },
    "success": { "background": "bg-success-primary", "border": "border-success", "icon": "fg-success-primary" },
    "warning": { "background": "bg-warning-primary", "border": "border-warning", "icon": "fg-warning-primary" },
    "error": { "background": "bg-error-primary", "border": "border-error", "icon": "fg-error-primary" }
  }
}
```

### React Implementation

```tsx
import { AlertCircle, CheckCircle, AlertTriangle, XCircle, X } from "@untitledui/icons";
import { cx } from "@/lib/utils";

type AlertProps = {
  title?: string;
  description: string;
  type?: "info" | "success" | "warning" | "error";
  dismissible?: boolean;
  onDismiss?: () => void;
  action?: { label: string; onClick: () => void };
};

const types = {
  info: {
    container: "bg-brand-primary border-brand",
    icon: "text-fg-brand-primary",
    Icon: AlertCircle,
  },
  success: {
    container: "bg-success-primary border-success",
    icon: "text-fg-success-primary",
    Icon: CheckCircle,
  },
  warning: {
    container: "bg-warning-primary border-warning",
    icon: "text-fg-warning-primary",
    Icon: AlertTriangle,
  },
  error: {
    container: "bg-error-primary border-error",
    icon: "text-fg-error-primary",
    Icon: XCircle,
  },
};

export function Alert({
  title,
  description,
  type = "info",
  dismissible = false,
  onDismiss,
  action,
}: AlertProps) {
  const config = types[type];
  const Icon = config.Icon;

  return (
    <div className={cx("flex gap-3 p-4 rounded-lg border", config.container)}>
      <Icon className={cx("size-5 shrink-0 mt-0.5", config.icon)} />
      
      <div className="flex-1 min-w-0">
        {title && <p className="text-sm font-semibold text-primary">{title}</p>}
        <p className="text-sm text-tertiary">{description}</p>
        
        {action && (
          <button
            onClick={action.onClick}
            className="mt-3 text-sm font-semibold text-brand-secondary hover:text-brand-primary"
          >
            {action.label}
          </button>
        )}
      </div>

      {dismissible && (
        <button onClick={onDismiss} className="shrink-0 text-fg-quinary hover:text-fg-quaternary">
          <X className="size-5" />
        </button>
      )}
    </div>
  );
}
```

## Pattern 3: Organism (Modal)

### Design System Spec

```json
{
  "meta": { "name": "Modal", "category": "organism" },
  "dependencies": { "molecules": ["ModalHeader", "ModalFooter"] },
  "variants": { "size": ["sm", "md", "lg", "xl"] },
  "props": {
    "open": { "type": "boolean", "required": true },
    "title": { "type": "string", "required": true },
    "description": { "type": "string" },
    "children": { "type": "node" },
    "primaryAction": { "type": "object" },
    "secondaryAction": { "type": "object" },
    "onClose": { "type": "function" }
  },
  "sizing": {
    "sm": { "width": "width-sm" },
    "md": { "width": "width-md" },
    "lg": { "width": "width-lg" }
  },
  "accessibility": {
    "role": "dialog",
    "keyboardInteraction": { "Escape": "close", "Tab": "trap focus" }
  }
}
```

### React Implementation

```tsx
"use client";

import { Dialog, Heading, Modal, ModalOverlay } from "react-aria-components";
import { X } from "@untitledui/icons";
import { cx } from "@/lib/utils";
import { Button } from "./button";

type ModalProps = {
  open: boolean;
  size?: "sm" | "md" | "lg" | "xl";
  title: string;
  description?: string;
  children?: React.ReactNode;
  primaryAction?: { label: string; onClick: () => void; destructive?: boolean };
  secondaryAction?: { label: string; onClick: () => void };
  onClose: () => void;
};

const sizes = {
  sm: "max-w-sm",
  md: "max-w-md",
  lg: "max-w-lg",
  xl: "max-w-xl",
};

export function CustomModal({
  open,
  size = "md",
  title,
  description,
  children,
  primaryAction,
  secondaryAction,
  onClose,
}: ModalProps) {
  return (
    <ModalOverlay
      isOpen={open}
      onOpenChange={(isOpen) => !isOpen && onClose()}
      className={cx(
        "fixed inset-0 z-50 flex items-center justify-center p-4",
        "bg-overlay backdrop-blur-sm",
        "data-[entering]:animate-in data-[entering]:fade-in",
        "data-[exiting]:animate-out data-[exiting]:fade-out"
      )}
    >
      <Modal
        className={cx(
          "w-full bg-primary border border-secondary rounded-xl shadow-xl",
          "data-[entering]:animate-in data-[entering]:zoom-in-95",
          "data-[exiting]:animate-out data-[exiting]:zoom-out-95",
          sizes[size]
        )}
      >
        <Dialog className="outline-none">
          {({ close }) => (
            <>
              {/* Header */}
              <div className="flex items-start justify-between p-6 pb-0">
                <div>
                  <Heading slot="title" className="text-lg font-semibold text-primary">
                    {title}
                  </Heading>
                  {description && (
                    <p className="mt-1 text-sm text-tertiary">{description}</p>
                  )}
                </div>
                <button
                  onClick={close}
                  className="text-fg-quinary hover:text-fg-quaternary"
                >
                  <X className="size-6" />
                </button>
              </div>

              {/* Content */}
              {children && <div className="p-6">{children}</div>}

              {/* Footer */}
              {(primaryAction || secondaryAction) && (
                <div className="flex justify-end gap-3 p-6 pt-0">
                  {secondaryAction && (
                    <Button hierarchy="secondary-gray" onClick={secondaryAction.onClick}>
                      {secondaryAction.label}
                    </Button>
                  )}
                  {primaryAction && (
                    <Button
                      hierarchy={primaryAction.destructive ? "primary" : "primary"}
                      onClick={primaryAction.onClick}
                      className={primaryAction.destructive ? "bg-error-solid hover:bg-error-solid_hover" : ""}
                    >
                      {primaryAction.label}
                    </Button>
                  )}
                </div>
              )}
            </>
          )}
        </Dialog>
      </Modal>
    </ModalOverlay>
  );
}
```

## Pattern 4: Data Table (Complex Organism)

### Design System Spec

```json
{
  "meta": { "name": "Table", "category": "organism" },
  "dependencies": { "molecules": ["TableHeaderCell", "TableCell"], "atoms": ["Checkbox", "Badge", "Avatar"] },
  "variants": { "style": ["default", "bordered", "striped"] },
  "props": {
    "columns": { "type": "array", "required": true },
    "data": { "type": "array", "required": true },
    "selectable": { "type": "boolean", "default": false },
    "sortable": { "type": "boolean", "default": false }
  }
}
```

### React Implementation

```tsx
"use client";

import {
  Table,
  TableHeader,
  TableBody,
  Column,
  Row,
  Cell,
  type SortDescriptor,
} from "react-aria-components";
import { ArrowUp, ArrowDown } from "@untitledui/icons";
import { cx } from "@/lib/utils";

type ColumnDef<T> = {
  key: keyof T | string;
  header: string;
  sortable?: boolean;
  render?: (item: T) => React.ReactNode;
};

type DataTableProps<T extends { id: string }> = {
  columns: ColumnDef<T>[];
  data: T[];
  variant?: "default" | "bordered" | "striped";
  onRowClick?: (item: T) => void;
  sortDescriptor?: SortDescriptor;
  onSortChange?: (descriptor: SortDescriptor) => void;
};

const variants = {
  default: "",
  bordered: "border border-secondary rounded-lg overflow-hidden",
  striped: "[&_tr:nth-child(even)]:bg-secondary",
};

export function DataTable<T extends { id: string }>({
  columns,
  data,
  variant = "default",
  onRowClick,
  sortDescriptor,
  onSortChange,
}: DataTableProps<T>) {
  return (
    <Table
      aria-label="Data table"
      sortDescriptor={sortDescriptor}
      onSortChange={onSortChange}
      className={cx("w-full", variants[variant])}
    >
      <TableHeader className="bg-secondary">
        {columns.map((col) => (
          <Column
            key={String(col.key)}
            id={String(col.key)}
            allowsSorting={col.sortable}
            className={cx(
              "px-6 py-3 text-left text-xs font-medium text-tertiary uppercase tracking-wider",
              col.sortable && "cursor-pointer hover:text-secondary"
            )}
          >
            {({ sortDirection }) => (
              <div className="flex items-center gap-2">
                {col.header}
                {sortDirection === "ascending" && <ArrowUp className="size-4" />}
                {sortDirection === "descending" && <ArrowDown className="size-4" />}
              </div>
            )}
          </Column>
        ))}
      </TableHeader>
      
      <TableBody items={data}>
        {(item) => (
          <Row
            className={cx(
              "border-t border-secondary",
              onRowClick && "cursor-pointer hover:bg-primary_hover"
            )}
            onAction={() => onRowClick?.(item)}
          >
            {columns.map((col) => (
              <Cell key={String(col.key)} className="px-6 py-4 text-sm text-primary">
                {col.render
                  ? col.render(item)
                  : String(item[col.key as keyof T] ?? "")}
              </Cell>
            ))}
          </Row>
        )}
      </TableBody>
    </Table>
  );
}
```

## Token to Tailwind Cheatsheet

### Colors

| Token Pattern | Tailwind |
|--------------|----------|
| `bg-primary` | `bg-primary` |
| `bg-brand-solid` | `bg-brand-solid` |
| `bg-error-primary` | `bg-error-primary` |
| `text-primary` | `text-primary` |
| `text-tertiary` | `text-tertiary` |
| `border-secondary` | `border-secondary` |
| `fg-brand-primary` | `text-fg-brand-primary` |

### Spacing

| Token | Value | Tailwind |
|-------|-------|----------|
| `spacing-xs` | 4px | `p-1`, `gap-1` |
| `spacing-sm` | 6px | `p-1.5`, `gap-1.5` |
| `spacing-md` | 8px | `p-2`, `gap-2` |
| `spacing-lg` | 12px | `p-3`, `gap-3` |
| `spacing-xl` | 16px | `p-4`, `gap-4` |
| `spacing-2xl` | 20px | `p-5`, `gap-5` |
| `spacing-3xl` | 24px | `p-6`, `gap-6` |
| `spacing-4xl` | 32px | `p-8`, `gap-8` |

### Typography

| Token | Tailwind |
|-------|----------|
| `Text xs/Regular` | `text-xs font-normal` |
| `Text sm/Medium` | `text-sm font-medium` |
| `Text sm/Semibold` | `text-sm font-semibold` |
| `Text md/Semibold` | `text-md font-semibold` |
| `Display sm/Semibold` | `text-display-sm font-semibold` |

### Sizing

| Token | Value | Tailwind |
|-------|-------|----------|
| `Button/height-sm` | 36px | `h-9` |
| `Button/height-md` | 40px | `h-10` |
| `Button/height-lg` | 44px | `h-11` |
| `Button/height-xl` | 48px | `h-12` |
| `Icon/size-sm` | 20px | `size-5` |
| `Icon/size-md` | 24px | `size-6` |

### Radius

| Token | Value | Tailwind |
|-------|-------|----------|
| `radius-sm` | 4px | `rounded-sm` |
| `radius-md` | 6px | `rounded-md` |
| `radius-lg` | 8px | `rounded-lg` |
| `radius-xl` | 12px | `rounded-xl` |
| `radius-2xl` | 16px | `rounded-2xl` |
| `radius-full` | 9999px | `rounded-full` |