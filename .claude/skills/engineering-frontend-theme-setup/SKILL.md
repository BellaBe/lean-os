---
name: frontend-theme-setup
description: Setup Untitled UI theme for Next.js project. One-time initialization - installs Untitled UI, configures Tailwind, downloads resources. Use when starting new frontend project.
allowed-tools: Read, Write, Bash
---

# Frontend Theme Setup Skill

Initialize Untitled UI design system for Next.js project.

## Purpose

Set up complete design system infrastructure:
- Install Untitled UI for Next.js
- Configure Tailwind with design tokens
- Download design resources (icons, flags, avatars, logos)
- Apply project theme

## Inputs

**Required:**
- Project name (e.g., "chromly", "detekta", "leanos")
- Brand color (if custom theme needed)

**Optional:**
- Design system JSON location: `artifacts/design-system/`

## Installation Process

### Step 1: Initialize Untitled UI

```bash
# Install Untitled UI for Next.js
npx untitledui@latest init untitled-ui --nextjs

# This creates:
# - components/ui/ (base Untitled UI components)
# - lib/utils.ts (cn helper)
# - Updates tailwind.config.ts
# - Installs dependencies
```

**What's Included (Free):**
Base components from https://www.untitledui.com/react/components
- Button, Input, Badge, Avatar
- Checkbox, Radio, Switch, Select
- Card, Alert, Dialog, Dropdown
- Plus 20+ more base components

### Step 2: Download Design Resources

```bash
# Create resources directory
mkdir -p public/resources/{icons,flags,avatars,logos}

# Icons from https://github.com/untitleduico/icons
# Download or install npm package:
npm install @untitleduico/icons

# Flags from https://www.untitledui.com/resources/flag-icons
# Download flag icon set to public/resources/flags/

# Avatars from https://www.untitledui.com/resources/avatars
# Download avatar set to public/resources/avatars/

# Logos from https://www.untitledui.com/resources/logos
# Download logo set to public/resources/logos/
```

### Step 3: Configure Tailwind with Design Tokens

```typescript
// tailwind.config.ts
import type { Config } from 'tailwindcss';

const config: Config = {
  darkMode: ["class"],
  content: [
    './app/**/*.{js,ts,jsx,tsx,mdx}',
    './components/**/*.{js,ts,jsx,tsx,mdx}',
  ],
  theme: {
    extend: {
      colors: {
        // Untitled UI base colors (auto-configured by init)
        gray: {
          25: '#FCFCFD',
          50: '#F9FAFB',
          100: '#F2F4F7',
          200: '#EAECF0',
          300: '#D0D5DD',
          400: '#98A2B3',
          500: '#667085',
          600: '#475467',
          700: '#344054',
          800: '#1D2939',
          900: '#101828',
          950: '#0C111D',
        },
        // Brand colors (customize per project)
        brand: {
          25: '#FEF6FB',
          50: '#FDF2FA',
          100: '#FCE7F6',
          200: '#FCCEEE',
          300: '#FAA7E0',
          400: '#F670C7',
          500: '#EE46BC', // Primary brand color
          600: '#DD2590',
          700: '#C11574',
          800: '#9E165F',
          900: '#851651',
          950: '#4F0D30',
        },
        error: {
          // Untitled UI error scale
        },
        warning: {
          // Untitled UI warning scale
        },
        success: {
          // Untitled UI success scale
        },
      },
      spacing: {
        // Untitled UI spacing scale
        xxs: '2px',
        xs: '4px',
        sm: '6px',
        md: '8px',
        lg: '12px',
        xl: '16px',
        '2xl': '20px',
        '3xl': '24px',
        '4xl': '32px',
        '5xl': '40px',
        '6xl': '48px',
        '7xl': '64px',
        '8xl': '80px',
        '9xl': '96px',
        '10xl': '128px',
        '11xl': '160px',
      },
      fontSize: {
        // Untitled UI typography scale
        xs: ['12px', { lineHeight: '18px' }],
        sm: ['14px', { lineHeight: '20px' }],
        md: ['16px', { lineHeight: '24px' }],
        lg: ['18px', { lineHeight: '28px' }],
        xl: ['20px', { lineHeight: '30px' }],
        'display-xs': ['24px', { lineHeight: '32px' }],
        'display-sm': ['30px', { lineHeight: '38px' }],
        'display-md': ['36px', { lineHeight: '44px', letterSpacing: '-0.02em' }],
        'display-lg': ['48px', { lineHeight: '60px', letterSpacing: '-0.02em' }],
        'display-xl': ['60px', { lineHeight: '72px', letterSpacing: '-0.02em' }],
        'display-2xl': ['72px', { lineHeight: '90px', letterSpacing: '-0.02em' }],
      },
      borderRadius: {
        xxs: '2px',
        xs: '4px',
        sm: '6px',
        md: '8px',
        lg: '10px',
        xl: '12px',
        '2xl': '16px',
        '3xl': '20px',
        '4xl': '24px',
      },
      boxShadow: {
        xs: '0px 1px 2px 0px rgba(16, 24, 40, 0.05)',
        sm: '0px 1px 2px 0px rgba(16, 24, 40, 0.06), 0px 1px 3px 0px rgba(16, 24, 40, 0.10)',
        md: '0px 2px 4px -2px rgba(16, 24, 40, 0.06), 0px 4px 8px -2px rgba(16, 24, 40, 0.10)',
        lg: '0px 4px 6px -2px rgba(16, 24, 40, 0.03), 0px 12px 16px -4px rgba(16, 24, 40, 0.08)',
        xl: '0px 8px 8px -4px rgba(16, 24, 40, 0.03), 0px 20px 24px -4px rgba(16, 24, 40, 0.08)',
        '2xl': '0px 24px 48px -12px rgba(16, 24, 40, 0.18)',
        '3xl': '0px 32px 64px -12px rgba(16, 24, 40, 0.14)',
      },
    },
  },
  plugins: [require("tailwindcss-animate")],
};

export default config;
```

### Step 4: Apply Project Theme

**For custom theme (e.g., Chromly pink):**

```typescript
// Update brand colors in tailwind.config.ts
brand: {
  500: '#EE46BC', // Chromly pink
  600: '#DD2590',
  // ... full scale
}
```

**Read from design tokens (if available):**

```bash
# If design tokens exist
cat artifacts/design-system/0-design-tokens/colors.primitives.json

# Extract brand colors
# Update tailwind.config.ts accordingly
```

### Step 5: Configure CSS Variables

```css
/* app/globals.css */
@tailwind base;
@tailwind components;
@tailwind utilities;

@layer base {
  :root {
    /* Semantic tokens for app structure */
    --bg-primary: theme('colors.gray.950');
    --bg-secondary: theme('colors.gray.900');
    --bg-active: theme('colors.gray.800');
    --bg-hover: theme('colors.gray.800');
    
    --border-primary: theme('colors.gray.800');
    --border-secondary: theme('colors.gray.700');
    
    --text-primary: theme('colors.white');
    --text-secondary: theme('colors.gray.400');
    --text-tertiary: theme('colors.gray.500');
  }
  
  .dark {
    /* Dark mode already configured by Untitled UI */
  }
}
```

### Step 6: Create Resource Helpers

```typescript
// lib/resources.ts

// Icons (from @untitleduico/icons)
export { 
  CheckIcon,
  ChevronRightIcon,
  XIcon,
  // ... import as needed
} from '@untitleduico/icons';

// Flags
export function getFlagIcon(countryCode: string) {
  return `/resources/flags/${countryCode.toLowerCase()}.svg`;
}

// Avatars
export function getAvatar(avatarId: string) {
  return `/resources/avatars/${avatarId}.png`;
}

// Logos
export function getLogo(logoName: string) {
  return `/resources/logos/${logoName}.svg`;
}
```

## Verification Checklist

After setup, verify:

```bash
# 1. Untitled UI installed
ls components/ui/button.tsx  # Should exist

# 2. Tailwind compiles
npm run build  # Should succeed

# 3. Resources downloaded
ls public/resources/icons/
ls public/resources/flags/
ls public/resources/avatars/
ls public/resources/logos/

# 4. Theme applied
grep "brand-500" tailwind.config.ts  # Should show project color
```

## Outputs

```
Project structure after setup:
├── components/
│   └── ui/              # Untitled UI base components
├── lib/
│   ├── utils.ts        # cn() helper
│   └── resources.ts    # Resource helpers
├── public/
│   └── resources/
│       ├── icons/
│       ├── flags/
│       ├── avatars/
│       └── logos/
├── app/
│   └── globals.css     # CSS variables
├── tailwind.config.ts  # Theme configuration
└── package.json        # Dependencies
```

## Available Untitled UI Components

**Free base components:**
- Button, Input, Textarea, Select, Checkbox, Radio, Switch
- Badge, Avatar, Card, Alert, Toast, Dialog, Dropdown
- Tabs, Accordion, Tooltip, Popover
- Progress, Skeleton, Spinner
- Breadcrumb, Pagination
- Label, Separator

**Pro components (if purchased):**
- Data tables, charts, forms
- Complex layouts, navigation
- Advanced patterns

## Common Patterns

### Using Untitled UI Components

```typescript
import { Button } from '@/components/ui/button';
import { Input } from '@/components/ui/input';
import { Badge } from '@/components/ui/badge';

export function Example() {
  return (
    <div>
      <Button variant="primary" size="md">
        Click me
      </Button>
      <Input placeholder="Enter text..." />
      <Badge variant="success">Active</Badge>
    </div>
  );
}
```

### Using Icons

```typescript
import { CheckIcon, XIcon } from '@untitleduico/icons';

export function IconExample() {
  return (
    <div>
      <CheckIcon className="h-5 w-5 text-success-500" />
      <XIcon className="h-5 w-5 text-error-500" />
    </div>
  );
}
```

### Using Resources

```typescript
import { getFlagIcon, getAvatar } from '@/lib/resources';

export function ResourceExample() {
  return (
    <div>
      <img src={getFlagIcon('us')} alt="US Flag" />
      <img src={getAvatar('avatar-1')} alt="User" />
    </div>
  );
}
```

## Troubleshooting

**Import errors:**
```bash
# Clear cache and reinstall
rm -rf .next node_modules
npm install
```

**Tailwind not working:**
```bash
# Verify content paths in tailwind.config.ts
# Ensure all component paths included
```

**Missing resources:**
```bash
# Verify public/resources/ structure
# Re-download from Untitled UI website
```

## Notes

- Run `npx untitledui@latest init` once per project
- Design tokens can override Tailwind config
- Free components cover 80% of needs
- Custom components only for missing patterns
- Resources are static assets, cache-friendly