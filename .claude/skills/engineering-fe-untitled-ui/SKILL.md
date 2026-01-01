---
name: untitled-ui
description: Build production interfaces using Untitled UI design system for Next.js 15. React 19.1 + Tailwind CSS 4.1 + TypeScript 5.8 + React Aria. Bridges Figma design system JSON to React components. Triggers on: Next.js UI, Untitled UI components, building missing/PRO components, design-to-code translation.
---

# Untitled UI Design System Skill

Bridge Figma design system → React/Next.js production code.

## Decision Tree

```
Project status?
│
├─ New project? → See references/react-setup.md
│
└─ Existing project? → Discovery first (see Existing Project Workflow below)
    │
    ├─ Component exists in project?
    │   └─ Yes → Extend it, don't duplicate
    │
    ├─ Component in CLI inventory?
    │   └─ npx untitledui@latest add [component]
    │
    ├─ Not in CLI? → Find spec in `references/design-system/`:
    │   0-tokens/  → Token values
    │   1-atoms/          → button.json, input.json, badge.json...
    │   2-molecules/      → alert.json, table-cell.json, modal-header.json...
    │   3-organisms/      → modal.json, table.json, command-menu.json...
    │   4-layouts/        → Auth pages, error pages
    │   5-pages/          → Complete page examples
    │
    └─ Build matching project patterns (variants style, naming, exports)
```

## CLI Commands

```bash
# New project setup - see references/react-setup.md
npx untitledui@latest init --nextjs

# Add components
npx untitledui@latest add                      # Interactive menu
npx untitledui@latest add button input select  # Specific
npx untitledui@latest add -t base              # All atoms
npx untitledui@latest add -t application       # App UI
npx untitledui@latest add -t marketing         # Marketing sections
```

## Existing Project Workflow

When project already has Untitled UI set up:

### 1. Discovery First

```bash
# Find existing components
ls -la src/components/
ls -la src/components/base/
ls -la src/components/application/

# Check for custom components (not from CLI)
grep -r "export function\|export const" src/components/ --include="*.tsx" | head -20

# Find existing patterns
grep -r "cx(" src/components/ --include="*.tsx" | head -5
grep -r "className=" src/components/ --include="*.tsx" | head -10
```

### 2. Match Existing Patterns

Before building anything new, identify:

```tsx
// Check: How are variants structured?
// Some projects use objects:
const sizes = { sm: "...", md: "...", lg: "..." };

// Others use cva/class-variance-authority:
const buttonVariants = cva("base-classes", { variants: {...} });

// Match whatever exists in the project.
```

### 3. Extend, Don't Duplicate

```tsx
// ❌ WRONG - Creating new Button when one exists
// src/components/CustomButton.tsx
export function CustomButton() { ... }

// ✅ CORRECT - Extend existing
// Check src/components/base/Button.tsx first
// Add new variant to existing component if needed
```

### 4. Component Discovery Checklist

Before creating ANY component:

- [ ] Search `src/components/` for similar component
- [ ] Check if CLI component was already added (`npx untitledui@latest add` shows installed)
- [ ] Look for shared utilities (`src/lib/utils.ts`, `src/lib/cn.ts`)
- [ ] Check existing import patterns (`@/components/...` vs relative)
- [ ] Match file naming convention (PascalCase.tsx vs kebab-case.tsx)
- [ ] Match export style (named vs default exports)

### 5. When Modifying Existing Components

```tsx
// Add variants to existing - don't fork
// Before: Button has primary, secondary
// Need: destructive variant

// Find: src/components/base/Button.tsx
// Add to existing hierarchies object:
const hierarchies = {
  primary: "...",
  secondary: "...",
  destructive: "bg-error-primary text-white hover:bg-error-secondary", // ADD
};

// Update types:
type ButtonProps = {
  hierarchy?: "primary" | "secondary" | "destructive"; // ADD
};
```

### 6. Project-Specific Tokens

Check if project extended design tokens:

```bash
# Find custom tokens
cat src/styles/theme.css | grep -E "^\s*--" | head -20

# Check tailwind config extensions (if exists)
cat tailwind.config.ts 2>/dev/null || cat tailwind.config.js 2>/dev/null
```

Use project-specific tokens if they exist, fall back to design system defaults.

---

## CLI Component Inventory

Check here first before building custom. If listed → use CLI.

### Base Components (`-t base`)
| Component | CLI Name | Variants |
|-----------|----------|----------|
| Buttons | `buttons` | 13 variants |
| Social Buttons | `social-buttons` | 12 variants |
| App Store Buttons | `mobile-app-store-buttons` | 8 variants |
| Utility Buttons | `utility-buttons` | 5 variants |
| Button Groups | `button-groups` | 6 variants |
| Badges | `badges` | 25 variants |
| Badge Groups | `badge-groups` | 20 variants |
| Tags | `tags` | variants |
| Dropdowns | `dropdowns` | 3 variants |
| Select | `select` | 8 variants |
| Inputs | `inputs` | 10 variants |
| Textareas | `textareas` | 3 variants |
| Verification Code | `verification-code-inputs` | 4 variants |
| Text Editors | `text-editors` | 5 variants |
| Toggles | `toggles` | 7 variants |
| Checkboxes | `checkboxes` | 5 variants |
| Radio Buttons | `radio-buttons` | 5 variants |
| Radio Groups | `radio-groups` | 5 components |
| Avatars | `avatars` | 11 variants |
| Tooltips | `tooltips` | 11 variants |
| Progress Indicators | `progress-indicators` | 9 variants |
| Sliders | `sliders` | 4 variants |
| Featured Icons | `featured-icons` | 6 variants |
| Video Players | `video-players` | 3 variants |
| Credit Cards | `credit-cards` | 13 variants |
| QR Codes | `qr-codes` | 4 variants |
| Rating Stars | `rating-badge-and-stars` | 3 components |

### Application UI (`-t application`)
| Component | CLI Name | Count |
|-----------|----------|-------|
| Page Headers | `page-headers` | 6 |
| Card Headers | `card-headers` | 2 |
| Section Headers | `section-headers` | 7 |
| Section Footers | `section-footers` | 4 |
| Sidebar Nav | `sidebar-navigations` | 5 |
| Header Nav | `header-navigations` | 2 |
| Modals | `modals` | 46 |
| Command Menus | `command-menus` | 9 |
| Slideout Menus | `slideout-menus` | 20 |
| Tables | `tables` | 12 |
| Tabs | `tabs` | 10 |
| Alerts | `alerts` | 12 |
| Notifications | `notifications` | 9 |
| Pagination | `pagination` | 14 |
| Breadcrumbs | `breadcrumbs` | 3 |
| Progress Steps | `progress-steps` | 18 |
| Date Pickers | `date-pickers` | 6 |
| Calendars | `calendars` | 3 |
| File Uploaders | `file-uploaders` | 5 |
| Empty States | `empty-states` | 3 |
| Loading Indicators | `loading-indicators` | 3 |
| Charts (Line/Bar) | `line-bar-charts` | 4 |
| Pie Charts | `pie-charts` | 4 |
| Metrics | `metrics` | 16 |

### Marketing (`-t marketing`)
| Component | CLI Name | Count |
|-----------|----------|-------|
| Header Nav | `header-navigations` | 20 |
| Header Sections | `header-sections` | 44 |
| Features Sections | `features-sections` | 42 |
| Pricing Sections | `pricing-sections` | 22 |
| CTA Sections | `cta-sections` | 20 |
| Testimonials | `testimonial-sections` | 26 |
| FAQ Sections | `faq-sections` | 16 |
| Blog Sections | `blog-sections` | 24 |
| Contact Sections | `contact-sections` | 36 |
| Team Sections | `team-sections` | 14 |
| Footers | `footers` | 40 |
| Banners | `banners` | 16 |

### Shared Pages (Auth, Error)
`log-in-pages`, `sign-up-pages`, `verification-pages`, `forgot-password-pages`, `404-pages`, `email-templates`

**Not in CLI?** → Build from design system spec using patterns below.

## Reading Design System Specs

Each component JSON has this structure:

```json
{
  "meta": { "name": "Modal", "category": "organism" },
  "dependencies": { "molecules": ["ModalHeader", "ModalFooter"] },
  "variants": { "size": ["sm", "md", "lg"], "type": ["default", "destructive"] },
  "props": {
    "open": { "type": "boolean", "required": true },
    "size": { "type": "enum", "default": "md", "options": ["sm", "md", "lg"] }
  },
  "sizing": {
    "sm": { "width": { "collection": "Width Styles", "name": "width-sm" } },
    "borderRadius": { "collection": "Radius Styles", "name": "radius-xl" }
  },
  "tokens": {
    "container": {
      "background": { "collection": "Color Styles", "name": "Colors/Background/bg-primary" },
      "border": { "collection": "Color Styles", "name": "Colors/Border/border-secondary" }
    }
  },
  "accessibility": {
    "role": "dialog",
    "keyboardInteraction": { "Escape": "close", "Tab": "trap focus" }
  }
}
```

## Spec → React Translation

### 1. Map `props` to TypeScript interface

```tsx
// From spec: "props": { "size": { "type": "enum", "default": "md", "options": ["sm", "md", "lg"] } }

type ModalProps = {
  open: boolean;
  size?: "sm" | "md" | "lg";
  title: string;
  children?: React.ReactNode;
  onClose?: () => void;
};
```

### 2. Map `tokens` to semantic Tailwind classes

```tsx
// From spec: "collection": "Color Styles", "name": "Colors/Background/bg-primary"
// Becomes: className="bg-primary"

// From spec: "collection": "Radius Styles", "name": "radius-xl"  
// Becomes: className="rounded-xl"

// From spec: "collection": "Spacing Styles", "name": "spacing-3xl"
// Becomes: className="p-6" (24px)
```

### 3. Map `variants` to class maps

```tsx
const sizes = {
  sm: "max-w-sm",   // width-sm token
  md: "max-w-md",   // width-md token
  lg: "max-w-lg",   // width-lg token
};
```

### 4. Use React Aria for accessibility spec

```tsx
// From spec: "role": "dialog", "keyboardInteraction": { "Escape": "close" }
import { Dialog, Modal, ModalOverlay } from "react-aria-components";

// React Aria handles:
// - role="dialog"
// - aria-modal="true"
// - Escape to close
// - Focus trapping
// - Body scroll lock
```

### 5. Complete component template

```tsx
"use client";

import { Dialog, Modal, ModalOverlay } from "react-aria-components";
import { cx } from "@/lib/utils";

type ModalProps = {
  open: boolean;
  size?: "sm" | "md" | "lg";
  children: React.ReactNode;
  onClose: () => void;
};

const sizes = {
  sm: "max-w-sm",
  md: "max-w-md", 
  lg: "max-w-lg",
};

export function CustomModal({ open, size = "md", children, onClose }: ModalProps) {
  return (
    <ModalOverlay
      isOpen={open}
      onOpenChange={(isOpen) => !isOpen && onClose()}
      className="fixed inset-0 z-50 bg-overlay flex items-center justify-center"
    >
      <Modal className={cx(
        "bg-primary border border-secondary rounded-xl shadow-xl p-6",
        sizes[size]
      )}>
        <Dialog className="outline-none">
          {children}
        </Dialog>
      </Modal>
    </ModalOverlay>
  );
}
```

## Token Mapping Reference

| Design System Token | Tailwind Class |
|---------------------|----------------|
| `Colors/Background/bg-primary` | `bg-primary` |
| `Colors/Text/text-primary` | `text-primary` |
| `Colors/Border/border-secondary` | `border-secondary` |
| `spacing-xs` (4px) | `gap-1`, `p-1` |
| `spacing-md` (8px) | `gap-2`, `p-2` |
| `spacing-lg` (12px) | `gap-3`, `p-3` |
| `spacing-xl` (16px) | `gap-4`, `p-4` |
| `spacing-3xl` (24px) | `gap-6`, `p-6` |
| `radius-md` | `rounded-md` |
| `radius-xl` | `rounded-xl` |
| `Text sm/Semibold` | `text-sm font-semibold` |
| `Effect/shadow-xl` | `shadow-xl` |

## React Aria Component Mapping

| Design System Component | React Aria Primitive |
|------------------------|---------------------|
| Button | `Button` |
| Input/TextField | `TextField`, `Input`, `Label` |
| Select | `Select`, `SelectValue`, `Popover`, `ListBox` |
| Checkbox | `Checkbox` |
| Toggle | `Switch` |
| Modal | `ModalOverlay`, `Modal`, `Dialog` |
| Dropdown | `Menu`, `MenuItem`, `Popover` |
| Tooltip | `Tooltip`, `TooltipTrigger` |
| Table | `Table`, `TableHeader`, `Column`, `Row`, `Cell` |
| Tabs | `Tabs`, `TabList`, `Tab`, `TabPanel` |
| DatePicker | `DatePicker`, `Calendar` |
| ComboBox | `ComboBox`, `Input`, `Popover`, `ListBox` |

## Dark Mode

Uses `.light-mode`/`.dark-mode` classes, NOT Tailwind `dark:` prefix.
See [references/react-setup.md](references/react-setup.md) for ThemeProvider setup.

## Responsive Breakpoints

| Design Token | Tailwind | Value |
|--------------|----------|-------|
| Breakpoint/sm | `sm:` | 640px |
| Breakpoint/md | `md:` | 768px |
| Breakpoint/lg | `lg:` | 1024px |
| Breakpoint/xl | `xl:` | 1280px |
| Breakpoint/2xl | `2xl:` | 1536px |

```tsx
// Mobile-first (always)
className="flex flex-col gap-4 md:flex-row md:gap-6"
className="w-full md:w-auto"
className="text-sm md:text-md"tokens
```

## Motion Tokens

| Design Token | Tailwind | Use |
|--------------|----------|-----|
| duration-fast | `duration-150` | Hover, focus |
| duration-normal | `duration-200` | Standard transitions |
| duration-slow | `duration-300` | Modals, slideouts |
| duration-slower | `duration-500` | Page transitions |

```tsx
// Standard transition
className="transition-colors duration-150"

// Modal animation (with tailwindcss-animate)
className="animate-in fade-in zoom-in-95 duration-200"
```

## References

- **Setup**: See [references/react-setup.md](references/react-setup.md) for starter kit, deps, ThemeProvider, icons, cx()
- **Bridge patterns**: See [references/bridge.md](references/bridge.md) for complete spec → React examples
- **Guardrails**: See [references/guardrails.md](references/guardrails.md) for AI deviation prevention, composition rules, responsive patterns

## AI Deviation Quick Check

Before generating any code, verify:
- **NO hardcoded colors** (`bg-gray-*`, `text-blue-*`, `#hex`) → Use `bg-primary`, `text-secondary`
- **NO `dark:` prefix** → CSS variables handle both modes automatically
- **NO arbitrary values** (`p-[18px]`) → Use token scale (`p-4`, `p-5`)
- **NO Lucide/Heroicons** → Use `@untitledui/icons`
- **NO custom focus rings** → React Aria handles focus states

See [references/guardrails.md](references/guardrails.md) for full deviation list.

## Production Checklist

- [ ] CLI component available? Use it first
- [ ] Semantic tokens only (`bg-primary` not `bg-gray-50`)
- [ ] No hardcoded colors or `dark:` prefix
- [ ] React Aria for interactive components
- [ ] Icons from `@untitledui/icons`
- [ ] TypeScript props from design system spec
- [ ] All variants mapped to class objects
- [ ] Mobile-first responsive (`flex-col md:flex-row`)
- [ ] Transitions use duration tokens (`duration-150`, `duration-200`)
- [ ] Follows atomic hierarchy (atoms → molecules → organisms)
- [ ] Dark mode tested (toggle `.light-mode`/`.dark-mode`)
- [ ] Keyboard navigation works
- [ ] Loading/error/empty states

## References

| File | Contents |
|------|----------|
| [bridge.md](references/bridge.md) | Figma-to-code mapping for all components |
| [react-setup.md](references/react-setup.md) | React Aria setup and integration |
| [guardrails.md](references/guardrails.md) | Allowed deviations and constraints |
| [accessibility.md](references/accessibility.md) | ARIA patterns, keyboard nav, screen readers |