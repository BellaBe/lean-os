# AI Guardrails & Composition Rules

Prevent design system drift. AI tends to deviate—this document enforces consistency.

---

## Common AI Deviations (NEVER DO)

### 1. Hardcoded Colors
```tsx
// ❌ WRONG - AI loves to hardcode colors
className="bg-gray-50 text-gray-900 border-gray-200"
className="bg-white dark:bg-gray-800"
className="text-[#344054]"

// ✅ CORRECT - Always semantic tokens
className="bg-primary text-primary border-secondary"
```

### 2. Tailwind `dark:` Prefix
```tsx
// ❌ WRONG - Untitled UI doesn't use dark: prefix
className="bg-white dark:bg-gray-900"

// ✅ CORRECT - CSS variables handle both modes
className="bg-primary"  // theme.css defines light/dark values
```

### 3. Arbitrary Values
```tsx
// ❌ WRONG - AI generates arbitrary spacing/sizing
className="p-[18px] gap-[14px] rounded-[10px] w-[342px]"

// ✅ CORRECT - Use token scale
className="p-4 gap-3 rounded-xl w-80"
// Spacing: 1,2,3,4,5,6,8,10,12,16,20,24
// Radius: sm, md, lg, xl, 2xl, full
```

### 4. Custom Focus Rings
```tsx
// ❌ WRONG - AI adds custom focus styles
className="focus:ring-2 focus:ring-blue-500 focus:ring-offset-2"

// ✅ CORRECT - Use token or React Aria handles it
className="focus-visible:ring-2 focus-visible:ring-brand focus-visible:ring-offset-2"
// Better: Let React Aria components handle focus
```

### 5. Inline onClick Handlers (for complex interactions)
```tsx
// ❌ WRONG - AI bypasses React Aria
<div onClick={() => setOpen(true)} tabIndex={0} role="button">

// ✅ CORRECT - Use React Aria primitive
<Button onPress={() => setOpen(true)}>
```

### 6. Generic Icon Libraries
```tsx
// ❌ WRONG - AI defaults to Lucide/Heroicons
import { X } from "lucide-react";
import { XMarkIcon } from "@heroicons/react/24/outline";

// ✅ CORRECT - Use Untitled UI icons
import { XClose } from "@untitledui/icons";
```

### 7. Shadow Approximations
```tsx
// ❌ WRONG - AI guesses shadow values
className="shadow-[0_4px_6px_-1px_rgba(0,0,0,0.1)]"

// ✅ CORRECT - Use effect tokens
className="shadow-xs"  // xs, sm, md, lg, xl, 2xl, 3xl
```

### 8. Typography Combos
```tsx
// ❌ WRONG - AI mixes arbitrary text styles
className="text-[15px] leading-[22px] tracking-tight"

// ✅ CORRECT - Match design system typography
className="text-sm leading-5"  // text-xs/sm/md/lg/xl/2xl
```

---

## Composition Rules

### Atomic Design Hierarchy

```
0-design-tokens/  → Primitives (colors, spacing, typography)
       ↓
1-atoms/          → Single-purpose (Button, Input, Badge, Avatar)
       ↓
2-molecules/      → Atom combinations (Alert, ModalHeader, TableCell)
       ↓
3-organisms/      → Complex features (Modal, Table, Navigation)
       ↓
4-layouts/        → Page scaffolds (AuthLayout, DashboardLayout)
       ↓
5-pages/          → Complete views
```

### Composition Principles

**1. Atoms are indivisible**
```tsx
// Atoms take tokens directly, no child components
<Button size="md" hierarchy="primary">Label</Button>
<Badge color="success">Active</Badge>
<Avatar src={user.avatar} size="md" />
```

**2. Molecules combine atoms**
```tsx
// Molecule = atoms + layout logic
function Alert({ type, title, description, onClose }) {
  return (
    <div className="flex gap-3 p-4 bg-primary rounded-xl border border-secondary">
      <FeaturedIcon type={type} />           {/* atom */}
      <div className="flex-1">
        <Text weight="semibold">{title}</Text> {/* atom */}
        <Text color="tertiary">{description}</Text>
      </div>
      <IconButton icon={XClose} onPress={onClose} /> {/* atom */}
    </div>
  );
}
```

**3. Organisms compose molecules + atoms**
```tsx
// Organism = molecules + atoms + state/behavior
function Modal({ open, onClose, title, children, actions }) {
  return (
    <ModalOverlay isOpen={open} onOpenChange={(v) => !v && onClose()}>
      <Modal>
        <Dialog>
          <ModalHeader title={title} onClose={onClose} />  {/* molecule */}
          <div className="p-6">{children}</div>            {/* content slot */}
          <ModalFooter actions={actions} />                {/* molecule */}
        </Dialog>
      </Modal>
    </ModalOverlay>
  );
}
```

**4. Never skip hierarchy levels**
```tsx
// ❌ WRONG - Page directly uses atoms
function SettingsPage() {
  return (
    <div>
      <Button>Save</Button>
      <Input />
      <Badge>Pro</Badge>
    </div>
  );
}

// ✅ CORRECT - Page uses organisms/molecules
function SettingsPage() {
  return (
    <PageLayout>
      <PageHeader title="Settings" />           {/* organism */}
      <SettingsForm />                          {/* organism */}
      <SectionFooter actions={[...]} />         {/* molecule */}
    </PageLayout>
  );
}
```

---

## Responsive Patterns

### Breakpoints (Tailwind matches design system)

| Token | Value | Tailwind Prefix |
|-------|-------|-----------------|
| sm | 640px | `sm:` |
| md | 768px | `md:` |
| lg | 1024px | `lg:` |
| xl | 1280px | `xl:` |
| 2xl | 1536px | `2xl:` |

### Mobile-First Always

```tsx
// ✅ CORRECT - Mobile first, scale up
className="flex flex-col gap-4 md:flex-row md:gap-6 lg:gap-8"
className="w-full md:w-auto"
className="text-sm md:text-md lg:text-lg"
className="p-4 md:p-6 lg:p-8"

// ❌ WRONG - Desktop first (max-width thinking)
className="flex-row max-md:flex-col"
```

### Container Patterns

```tsx
// Standard container with responsive padding
<div className="mx-auto max-w-7xl px-4 md:px-6 lg:px-8">

// Full-bleed with contained content
<section className="w-full bg-secondary">
  <div className="mx-auto max-w-7xl px-4 md:px-6 lg:px-8 py-16 md:py-24">
```

### Component Responsive Variants

```tsx
// Grid columns
className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 xl:grid-cols-4 gap-6"

// Navigation: mobile hamburger → desktop horizontal
<nav className="hidden md:flex items-center gap-6">  {/* desktop */}
<MobileNav className="md:hidden" />                   {/* mobile */}

// Stack → inline buttons
<div className="flex flex-col gap-3 sm:flex-row sm:gap-4">
  <Button className="w-full sm:w-auto">Primary</Button>
  <Button className="w-full sm:w-auto" hierarchy="secondary">Secondary</Button>
</div>

// Table: scroll on mobile, full on desktop
<div className="overflow-x-auto -mx-4 px-4 md:mx-0 md:px-0">
  <Table className="min-w-[600px] md:min-w-0 w-full">
```

### Typography Responsive Scale

```tsx
// Headings scale appropriately
<h1 className="text-2xl md:text-3xl lg:text-4xl font-semibold">

// Body maintains readability
<p className="text-sm md:text-md text-tertiary max-w-prose">
```

---

## Motion & Animation

### Duration Tokens

| Design Token | Tailwind | Use Case |
|-------------|----------|----------|
| duration-fast | `duration-150` | Micro-interactions (hover, focus) |
| duration-normal | `duration-200` | Standard transitions |
| duration-slow | `duration-300` | Modals, slideouts |
| duration-slower | `duration-500` | Page transitions, complex animations |

### Standard Transitions

```tsx
// Button hover
className="transition-colors duration-150"

// Modal enter/exit
className="transition-all duration-300 ease-out"

// Dropdown open
className="transition-opacity duration-200"
```

### Animation Classes (tailwindcss-animate)

```tsx
// Fade in modal
className="animate-in fade-in duration-200"

// Slide in slideout
className="animate-in slide-in-from-right duration-300"

// Zoom dialog
className="animate-in zoom-in-95 duration-200"

// Exit animations
className="data-[exiting]:animate-out data-[exiting]:fade-out"
```

### React Aria Animation States

```tsx
// React Aria provides data attributes for animation
<ModalOverlay className={cx(
  "fixed inset-0 bg-overlay",
  "data-[entering]:animate-in data-[entering]:fade-in",
  "data-[exiting]:animate-out data-[exiting]:fade-out"
)}>
  <Modal className={cx(
    "bg-primary rounded-xl",
    "data-[entering]:animate-in data-[entering]:zoom-in-95",
    "data-[exiting]:animate-out data-[exiting]:zoom-out-95"
  )}>
```

### Reduced Motion

```tsx
// Always respect user preference
className="motion-safe:transition-all motion-safe:duration-200"

// Or disable animations entirely
className="motion-reduce:transition-none motion-reduce:animate-none"
```

---

## Acceptable Shortcuts

### When You CAN Deviate

**1. One-off layouts** (not reusable components)
```tsx
// OK for page-specific grid that won't be reused
className="grid grid-cols-[200px_1fr_300px]"
```

**2. Content-specific dimensions**
```tsx
// OK for specific image aspect ratios
className="aspect-[16/9]"
className="max-w-[65ch]"  // prose width
```

**3. Third-party integrations**
```tsx
// OK when wrapping external components
<div className="[&_.external-widget]:rounded-lg">
```

**4. Animation keyframes** (when token doesn't exist)
```tsx
// OK for custom animation not in design system
className="animate-[shimmer_2s_infinite]"
```

### Always Document Deviations

```tsx
// Non-standard: Using custom width for dashboard sidebar
// Rationale: Design system doesn't have 280px width token
// TODO: Request token addition
className="w-[280px]"
```

---

## Validation Checklist

Before shipping any component:

- [ ] No hardcoded colors (grep for `#`, `rgb`, `gray-`, `blue-`)
- [ ] No `dark:` prefix usage
- [ ] No arbitrary values unless documented
- [ ] Icons from `@untitledui/icons`
- [ ] Interactive elements use React Aria
- [ ] Mobile-first responsive classes
- [ ] Transitions use duration tokens
- [ ] Follows atomic design hierarchy
- [ ] Semantic token names match design system