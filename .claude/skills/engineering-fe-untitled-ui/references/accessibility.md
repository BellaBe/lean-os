# Accessibility Patterns

## WCAG Compliance Levels

| Level | Requirement | Target |
|-------|-------------|--------|
| **A** | Basic accessibility | Minimum |
| **AA** | Standard accessibility | Required for most |
| **AAA** | Enhanced accessibility | Ideal |

**Target**: WCAG 2.1 AA compliance

## Semantic HTML

### Use Correct Elements

```tsx
// ❌ BAD: Div soup
<div className="header">
  <div className="nav">
    <div onClick={handleClick}>Home</div>
  </div>
</div>

// ✅ GOOD: Semantic elements
<header>
  <nav aria-label="Main navigation">
    <a href="/">Home</a>
  </nav>
</header>
```

### Heading Hierarchy

```tsx
// ❌ BAD: Skipped heading levels
<h1>Page Title</h1>
<h3>Section</h3>  // Skipped h2

// ✅ GOOD: Proper hierarchy
<h1>Page Title</h1>
<h2>Section</h2>
<h3>Subsection</h3>
```

### Landmarks

```tsx
<header>           {/* Banner landmark */}
  <nav>            {/* Navigation landmark */}
</header>
<main>             {/* Main landmark - only one per page */}
  <aside>          {/* Complementary landmark */}
  </aside>
</main>
<footer>           {/* Contentinfo landmark */}
</footer>
```

## Keyboard Navigation

### Focus Management

```tsx
"use client";
import { useRef, useEffect } from 'react';

export function Modal({ isOpen, onClose, children }: ModalProps) {
  const closeButtonRef = useRef<HTMLButtonElement>(null);
  const previousFocusRef = useRef<HTMLElement | null>(null);

  useEffect(() => {
    if (isOpen) {
      // Store previous focus
      previousFocusRef.current = document.activeElement as HTMLElement;
      // Move focus into modal
      closeButtonRef.current?.focus();
    } else {
      // Restore focus on close
      previousFocusRef.current?.focus();
    }
  }, [isOpen]);

  if (!isOpen) return null;

  return (
    <div
      role="dialog"
      aria-modal="true"
      aria-labelledby="modal-title"
      onKeyDown={e => e.key === 'Escape' && onClose()}
    >
      <button ref={closeButtonRef} onClick={onClose} aria-label="Close modal">
        ×
      </button>
      {children}
    </div>
  );
}
```

### Focus Trap

```tsx
"use client";
import { useEffect, useRef } from 'react';

export function FocusTrap({ children }: { children: React.ReactNode }) {
  const containerRef = useRef<HTMLDivElement>(null);

  useEffect(() => {
    const container = containerRef.current;
    if (!container) return;

    const focusableElements = container.querySelectorAll<HTMLElement>(
      'button, [href], input, select, textarea, [tabindex]:not([tabindex="-1"])'
    );
    const firstElement = focusableElements[0];
    const lastElement = focusableElements[focusableElements.length - 1];

    const handleKeyDown = (e: KeyboardEvent) => {
      if (e.key !== 'Tab') return;

      if (e.shiftKey) {
        if (document.activeElement === firstElement) {
          e.preventDefault();
          lastElement.focus();
        }
      } else {
        if (document.activeElement === lastElement) {
          e.preventDefault();
          firstElement.focus();
        }
      }
    };

    container.addEventListener('keydown', handleKeyDown);
    return () => container.removeEventListener('keydown', handleKeyDown);
  }, []);

  return <div ref={containerRef}>{children}</div>;
}
```

### Skip Links

```tsx
// app/layout.tsx
export default function RootLayout({ children }: { children: React.ReactNode }) {
  return (
    <html>
      <body>
        <a
          href="#main-content"
          className="sr-only focus:not-sr-only focus:absolute focus:top-4 focus:left-4 focus:z-50 focus:bg-white focus:p-4"
        >
          Skip to main content
        </a>
        <Header />
        <main id="main-content" tabIndex={-1}>
          {children}
        </main>
        <Footer />
      </body>
    </html>
  );
}
```

### Keyboard Patterns

| Pattern | Keys | Behavior |
|---------|------|----------|
| Button | Enter, Space | Activate |
| Link | Enter | Navigate |
| Menu | Arrow keys | Navigate items |
| Modal | Escape | Close |
| Tabs | Arrow keys | Switch tabs |
| Dropdown | Arrow keys, Escape | Navigate, close |

## ARIA Attributes

### Common Patterns

```tsx
// Buttons with icons only
<button aria-label="Close dialog">
  <XIcon aria-hidden="true" />
</button>

// Loading states
<button disabled={loading} aria-busy={loading}>
  {loading ? <Spinner aria-hidden="true" /> : null}
  {loading ? 'Saving...' : 'Save'}
</button>

// Expanded/collapsed
<button aria-expanded={isOpen} aria-controls="menu">
  Menu
</button>
<ul id="menu" hidden={!isOpen}>
  ...
</ul>

// Current page in navigation
<nav aria-label="Main">
  <a href="/" aria-current="page">Home</a>
  <a href="/products">Products</a>
</nav>

// Required fields
<label htmlFor="email">
  Email <span aria-hidden="true">*</span>
</label>
<input id="email" type="email" required aria-required="true" />

// Error states
<input
  id="email"
  type="email"
  aria-invalid={!!error}
  aria-describedby={error ? "email-error" : undefined}
/>
{error && <p id="email-error" role="alert">{error}</p>}
```

### Live Regions

```tsx
// Announce dynamic content
<div aria-live="polite" aria-atomic="true">
  {notification && <p>{notification}</p>}
</div>

// Urgent announcements
<div role="alert" aria-live="assertive">
  {error && <p>{error}</p>}
</div>

// Status updates
<div role="status" aria-live="polite">
  {itemCount} items in cart
</div>
```

### ARIA Roles

```tsx
// Custom components need roles
<div role="tablist">
  <button role="tab" aria-selected={active === 0} aria-controls="panel-0">
    Tab 1
  </button>
  <button role="tab" aria-selected={active === 1} aria-controls="panel-1">
    Tab 2
  </button>
</div>
<div role="tabpanel" id="panel-0" aria-labelledby="tab-0">
  Content 1
</div>

// Search landmark
<form role="search">
  <input type="search" aria-label="Search products" />
</form>

// Alert dialogs
<div role="alertdialog" aria-labelledby="dialog-title" aria-describedby="dialog-desc">
  <h2 id="dialog-title">Delete Item?</h2>
  <p id="dialog-desc">This action cannot be undone.</p>
</div>
```

## Forms

### Labels & Descriptions

```tsx
// Always associate labels with inputs
<label htmlFor="username">Username</label>
<input id="username" type="text" />

// Or wrap input in label
<label>
  Username
  <input type="text" />
</label>

// Additional descriptions
<label htmlFor="password">Password</label>
<input
  id="password"
  type="password"
  aria-describedby="password-hint"
/>
<p id="password-hint">Must be at least 8 characters</p>
```

### Error Handling

```tsx
export function FormField({
  label,
  error,
  children,
}: {
  label: string;
  error?: string;
  children: React.ReactElement;
}) {
  const id = useId();
  const errorId = `${id}-error`;

  return (
    <div>
      <label htmlFor={id}>{label}</label>
      {cloneElement(children, {
        id,
        'aria-invalid': !!error,
        'aria-describedby': error ? errorId : undefined,
      })}
      {error && (
        <p id={errorId} role="alert" className="text-red-600">
          {error}
        </p>
      )}
    </div>
  );
}

// Usage
<FormField label="Email" error={errors.email}>
  <input type="email" {...register('email')} />
</FormField>
```

### Form Validation

```tsx
// Announce errors on submit
export function Form({ onSubmit, children }: FormProps) {
  const [errorSummary, setErrorSummary] = useState<string[]>([]);
  const summaryRef = useRef<HTMLDivElement>(null);

  const handleSubmit = async (e: FormEvent) => {
    e.preventDefault();
    const errors = await validate();
    
    if (errors.length > 0) {
      setErrorSummary(errors);
      summaryRef.current?.focus();  // Focus error summary
      return;
    }
    
    onSubmit();
  };

  return (
    <form onSubmit={handleSubmit}>
      {errorSummary.length > 0 && (
        <div
          ref={summaryRef}
          tabIndex={-1}
          role="alert"
          aria-labelledby="error-heading"
        >
          <h2 id="error-heading">Please fix the following errors:</h2>
          <ul>
            {errorSummary.map((error, i) => (
              <li key={i}>{error}</li>
            ))}
          </ul>
        </div>
      )}
      {children}
    </form>
  );
}
```

## Color & Contrast

### Contrast Ratios

| Element | Minimum Ratio (AA) | Enhanced (AAA) |
|---------|-------------------|----------------|
| Normal text | 4.5:1 | 7:1 |
| Large text (18px+) | 3:1 | 4.5:1 |
| UI components | 3:1 | - |

### Don't Rely on Color Alone

```tsx
// ❌ BAD: Color is only indicator
<span className={status === 'error' ? 'text-red-500' : 'text-green-500'}>
  {status}
</span>

// ✅ GOOD: Color + icon + text
<span className={status === 'error' ? 'text-red-500' : 'text-green-500'}>
  {status === 'error' ? <XIcon aria-hidden="true" /> : <CheckIcon aria-hidden="true" />}
  {status === 'error' ? 'Failed' : 'Success'}
</span>
```

### Focus Indicators

```css
/* Ensure visible focus indicators */
:focus-visible {
  outline: 2px solid #2563eb;
  outline-offset: 2px;
}

/* Don't remove focus styles */
/* ❌ NEVER: button:focus { outline: none; } */
```

## Images & Media

### Alt Text

```tsx
// Informative images
<Image src="/chart.png" alt="Sales increased 25% in Q4 2024" />

// Decorative images
<Image src="/decorative-border.png" alt="" aria-hidden="true" />

// Complex images
<figure>
  <Image src="/complex-chart.png" alt="Sales comparison chart" />
  <figcaption>
    Figure 1: Quarterly sales comparison showing Q4 2024 
    outperformed Q4 2023 by 25%.
  </figcaption>
</figure>

// Linked images
<a href="/products/laptop">
  <Image src="/laptop.jpg" alt="MacBook Pro - View details" />
</a>
```

### Video & Audio

```tsx
// Provide captions and transcripts
<video controls>
  <source src="/video.mp4" type="video/mp4" />
  <track kind="captions" src="/captions.vtt" srclang="en" label="English" />
  <track kind="descriptions" src="/descriptions.vtt" srclang="en" label="Audio descriptions" />
</video>

// Audio with transcript
<audio controls aria-describedby="transcript">
  <source src="/podcast.mp3" type="audio/mpeg" />
</audio>
<details id="transcript">
  <summary>Transcript</summary>
  <p>...</p>
</details>
```

## Screen Reader Testing

### Testing Checklist

1. **Navigate with Tab** — Can you reach all interactive elements?
2. **Navigate with Arrow keys** — Do menus and tabs work?
3. **Activate with Enter/Space** — Do buttons and links respond?
4. **Screen reader** — Is all content announced properly?
5. **Zoom to 200%** — Is content still usable?
6. **Disable CSS** — Does content make sense?

### Screen Reader Utilities

```tsx
// Visually hidden but readable
<span className="sr-only">
  Opens in new tab
</span>

// Or with Tailwind
<span className="absolute w-px h-px p-0 -m-px overflow-hidden whitespace-nowrap border-0">
  Opens in new tab
</span>
```

### Test with Real Screen Readers

| Platform | Screen Reader | Browser |
|----------|--------------|---------|
| macOS | VoiceOver | Safari |
| Windows | NVDA | Firefox, Chrome |
| Windows | JAWS | Chrome, Edge |
| iOS | VoiceOver | Safari |
| Android | TalkBack | Chrome |

## Component Patterns

### Button

```tsx
type ButtonProps = {
  variant?: 'primary' | 'secondary' | 'destructive';
  loading?: boolean;
  disabled?: boolean;
  children: React.ReactNode;
} & React.ButtonHTMLAttributes<HTMLButtonElement>;

export function Button({
  variant = 'primary',
  loading = false,
  disabled = false,
  children,
  ...props
}: ButtonProps) {
  return (
    <button
      disabled={disabled || loading}
      aria-busy={loading}
      aria-disabled={disabled}
      {...props}
    >
      {loading && <Spinner aria-hidden="true" className="mr-2" />}
      {children}
    </button>
  );
}
```

### Tabs

```tsx
"use client";
import { useState, useId } from 'react';

export function Tabs({ tabs }: { tabs: { label: string; content: React.ReactNode }[] }) {
  const [activeIndex, setActiveIndex] = useState(0);
  const baseId = useId();

  const handleKeyDown = (e: React.KeyboardEvent, index: number) => {
    if (e.key === 'ArrowRight') {
      setActiveIndex((index + 1) % tabs.length);
    } else if (e.key === 'ArrowLeft') {
      setActiveIndex((index - 1 + tabs.length) % tabs.length);
    }
  };

  return (
    <div>
      <div role="tablist" aria-label="Content tabs">
        {tabs.map((tab, index) => (
          <button
            key={index}
            role="tab"
            id={`${baseId}-tab-${index}`}
            aria-selected={activeIndex === index}
            aria-controls={`${baseId}-panel-${index}`}
            tabIndex={activeIndex === index ? 0 : -1}
            onClick={() => setActiveIndex(index)}
            onKeyDown={e => handleKeyDown(e, index)}
          >
            {tab.label}
          </button>
        ))}
      </div>
      {tabs.map((tab, index) => (
        <div
          key={index}
          role="tabpanel"
          id={`${baseId}-panel-${index}`}
          aria-labelledby={`${baseId}-tab-${index}`}
          hidden={activeIndex !== index}
          tabIndex={0}
        >
          {tab.content}
        </div>
      ))}
    </div>
  );
}
```

### Dropdown Menu

```tsx
"use client";
import { useState, useRef, useId } from 'react';

export function Dropdown({ trigger, items }: DropdownProps) {
  const [isOpen, setIsOpen] = useState(false);
  const [focusedIndex, setFocusedIndex] = useState(-1);
  const menuRef = useRef<HTMLUListElement>(null);
  const menuId = useId();

  const handleKeyDown = (e: React.KeyboardEvent) => {
    switch (e.key) {
      case 'ArrowDown':
        e.preventDefault();
        setFocusedIndex(prev => Math.min(prev + 1, items.length - 1));
        break;
      case 'ArrowUp':
        e.preventDefault();
        setFocusedIndex(prev => Math.max(prev - 1, 0));
        break;
      case 'Escape':
        setIsOpen(false);
        break;
      case 'Enter':
        if (focusedIndex >= 0) {
          items[focusedIndex].onClick();
          setIsOpen(false);
        }
        break;
    }
  };

  return (
    <div className="relative">
      <button
        aria-expanded={isOpen}
        aria-haspopup="menu"
        aria-controls={menuId}
        onClick={() => setIsOpen(!isOpen)}
      >
        {trigger}
      </button>
      {isOpen && (
        <ul
          ref={menuRef}
          id={menuId}
          role="menu"
          aria-label="Actions"
          onKeyDown={handleKeyDown}
        >
          {items.map((item, index) => (
            <li
              key={index}
              role="menuitem"
              tabIndex={focusedIndex === index ? 0 : -1}
              onClick={() => {
                item.onClick();
                setIsOpen(false);
              }}
            >
              {item.label}
            </li>
          ))}
        </ul>
      )}
    </div>
  );
}
```

## Accessibility Checklist

### Structure
- [ ] Proper heading hierarchy (h1 → h2 → h3)
- [ ] Semantic HTML elements used
- [ ] Landmarks present (main, nav, header, footer)
- [ ] Skip link to main content

### Keyboard
- [ ] All interactive elements focusable
- [ ] Visible focus indicators
- [ ] Logical tab order
- [ ] No keyboard traps
- [ ] Escape closes modals/dropdowns

### Forms
- [ ] All inputs have labels
- [ ] Required fields indicated
- [ ] Error messages associated with inputs
- [ ] Error summary on submit

### Images & Media
- [ ] Meaningful alt text
- [ ] Decorative images have empty alt
- [ ] Videos have captions
- [ ] Audio has transcripts

### Color & Contrast
- [ ] Text meets contrast ratios (4.5:1)
- [ ] UI components meet 3:1
- [ ] Information not conveyed by color alone
- [ ] Focus states visible

### Screen Readers
- [ ] Content announced in logical order
- [ ] Dynamic content uses live regions
- [ ] Icons have accessible names
- [ ] State changes announced