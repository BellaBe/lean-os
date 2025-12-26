---
name: frontend-page-builder
description: Build pages from product specs using Untitled UI components and design system. Main frontend implementation - maps wireframes to code, uses free components when available, builds custom only when needed.
allowed-tools: Read, Write, Bash
---

# Frontend Page Builder Skill

Transform product specifications into production Next.js pages.

## Purpose

Product spec + Design system → Working page

## Inputs

**Required:**
- Product spec: `artifacts/product/specs/[feature].md`
- Design system: `artifacts/design-system/`

**Optional:**
- Wireframes: `artifacts/product/wireframes/[page].md`
- Backend API specs (for data shape)

## Component Strategy

### 1. Use Untitled UI Components First

**Available free components** (from `npx untitledui@latest init`):

```typescript
// Forms & Inputs
import { Button } from '@/components/ui/button';
import { Input } from '@/components/ui/input';
import { Textarea } from '@/components/ui/textarea';
import { Select } from '@/components/ui/select';
import { Checkbox } from '@/components/ui/checkbox';
import { Radio } from '@/components/ui/radio';
import { Switch } from '@/components/ui/switch';
import { Label } from '@/components/ui/label';

// Display
import { Badge } from '@/components/ui/badge';
import { Avatar } from '@/components/ui/avatar';
import { Card } from '@/components/ui/card';
import { Alert } from '@/components/ui/alert';
import { Separator } from '@/components/ui/separator';

// Overlay
import { Dialog } from '@/components/ui/dialog';
import { Dropdown } from '@/components/ui/dropdown';
import { Popover } from '@/components/ui/popover';
import { Tooltip } from '@/components/ui/tooltip';
import { Toast } from '@/components/ui/toast';

// Navigation
import { Tabs } from '@/components/ui/tabs';
import { Breadcrumb } from '@/components/ui/breadcrumb';
import { Pagination } from '@/components/ui/pagination';

// Feedback
import { Progress } from '@/components/ui/progress';
import { Skeleton } from '@/components/ui/skeleton';
import { Spinner } from '@/components/ui/spinner';

// Layout
import { Accordion } from '@/components/ui/accordion';
```

**Icons:**
```typescript
import { 
  CheckIcon,
  XIcon,
  ChevronRightIcon,
  ArrowRightIcon,
  // ... 200+ more
} from '@untitleduico/icons';
```

**Resources:**
```typescript
import { getFlagIcon, getAvatar, getLogo } from '@/lib/resources';

<img src={getFlagIcon('us')} />
<img src={getAvatar('avatar-1')} />
<img src={getLogo('company-logo')} />
```

### 2. Build Custom Components Only When Needed

**When to build custom:**
- Component not in Untitled UI free set
- Specific pattern in design system JSON
- Complex composition (organism level)

**How to build custom:**

```typescript
// Read design system JSON
const spec = readJSON('artifacts/design-system/2-molecules/stat-card.json');

// Generate component
// components/custom/stat-card.tsx
import { Card } from '@/components/ui/card';
import { Badge } from '@/components/ui/badge';

interface StatCardProps {
  title: string;
  value: string;
  change?: string;
  trend?: 'up' | 'down';
}

export function StatCard({ title, value, change, trend }: StatCardProps) {
  return (
    <Card className="p-6">
      <div className="text-sm text-gray-500">{title}</div>
      <div className="text-3xl font-semibold mt-2">{value}</div>
      {change && (
        <div className="flex items-center gap-2 mt-2">
          <Badge variant={trend === 'up' ? 'success' : 'error'}>
            {change}
          </Badge>
        </div>
      )}
    </Card>
  );
}
```

## Page Building Process

### Step 1: Read Product Spec

```markdown
# From artifacts/product/specs/dashboard.md

Extract:
- Page purpose: "User dashboard showing key metrics and activity"
- Layout: "Header + 2-column grid"
- Components: 
  - Header with search
  - 4 metric cards
  - Activity list
  - Quick actions sidebar
- Interactions:
  - Search filters activity
  - Cards link to detail views
  - Real-time updates for metrics
```

### Step 2: Map Components

```
Spec Component          → Implementation Strategy
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Header with search      → <Input /> (Untitled UI)
Metric cards            → Custom StatCard (build)
Activity list           → Custom ActivityList (build)
Quick actions sidebar   → <Card /> + <Button /> (Untitled UI)
Search icon             → <SearchIcon /> (@untitleduico/icons)
User avatar             → <Avatar /> (Untitled UI)
```

### Step 3: Generate Page Structure

```typescript
// app/dashboard/page.tsx
import { Button } from '@/components/ui/button';
import { Input } from '@/components/ui/input';
import { Avatar } from '@/components/ui/avatar';
import { Card } from '@/components/ui/card';
import { SearchIcon } from '@untitleduico/icons';
import { StatCard } from '@/components/custom/stat-card';
import { ActivityList } from '@/components/custom/activity-list';

export default function DashboardPage() {
  return (
    <div className="min-h-screen bg-primary">
      {/* Header */}
      <header className="border-b border-gray-800 px-8 py-4">
        <div className="flex items-center justify-between">
          <h1 className="text-2xl font-semibold">Dashboard</h1>
          <div className="flex items-center gap-4">
            <div className="relative">
              <SearchIcon className="absolute left-3 top-1/2 -translate-y-1/2 h-5 w-5 text-gray-400" />
              <Input 
                placeholder="Search..." 
                className="pl-10 w-80"
              />
            </div>
            <Avatar src="/resources/avatars/avatar-1.png" />
          </div>
        </div>
      </header>

      {/* Main Content */}
      <main className="p-8">
        <div className="grid grid-cols-1 lg:grid-cols-2 gap-6">
          {/* Left Column */}
          <div className="space-y-6">
            {/* Metrics Grid */}
            <div className="grid grid-cols-2 gap-4">
              <StatCard title="Revenue" value="$45k" change="+12%" trend="up" />
              <StatCard title="Users" value="1,234" change="+8%" trend="up" />
              <StatCard title="Orders" value="856" change="-3%" trend="down" />
              <StatCard title="Growth" value="23%" change="+5%" trend="up" />
            </div>

            {/* Activity List */}
            <Card className="p-6">
              <h2 className="text-lg font-semibold mb-4">Recent Activity</h2>
              <ActivityList />
            </Card>
          </div>

          {/* Right Column */}
          <div>
            <Card className="p-6">
              <h2 className="text-lg font-semibold mb-4">Quick Actions</h2>
              <div className="space-y-3">
                <Button className="w-full justify-start" variant="secondary">
                  View Reports
                </Button>
                <Button className="w-full justify-start" variant="secondary">
                  Export Data
                </Button>
                <Button className="w-full justify-start" variant="secondary">
                  Manage Team
                </Button>
              </div>
            </Card>
          </div>
        </div>
      </main>
    </div>
  );
}
```

### Step 4: Build Custom Components

**Only build what's not in Untitled UI:**

```typescript
// components/custom/stat-card.tsx
// (Already shown above)

// components/custom/activity-list.tsx
import { Avatar } from '@/components/ui/avatar';
import { Badge } from '@/components/ui/badge';

interface Activity {
  id: string;
  user: string;
  action: string;
  timestamp: string;
  type: 'success' | 'warning' | 'info';
}

export function ActivityList({ activities }: { activities: Activity[] }) {
  return (
    <div className="space-y-4">
      {activities.map((activity) => (
        <div key={activity.id} className="flex items-start gap-3">
          <Avatar size="sm" />
          <div className="flex-1">
            <p className="text-sm">
              <span className="font-medium">{activity.user}</span>
              {' '}{activity.action}
            </p>
            <p className="text-xs text-gray-500 mt-1">{activity.timestamp}</p>
          </div>
          <Badge variant={activity.type} size="sm">
            {activity.type}
          </Badge>
        </div>
      ))}
    </div>
  );
}
```

## Critical Design Rules

### Rule 1: Design Tokens Only

```typescript
// ❌ NEVER: Arbitrary values
<div className="bg-[#1e40af] w-[250px] p-[16px]" />

// ✅ ALWAYS: Design tokens
<div className="bg-brand-600 w-64 p-4" />
```

### Rule 2: Single Hover Level

```typescript
// ❌ NEVER: Double hover (card AND contents)
<Card className="hover:bg-gray-800">
  <div className="hover:bg-gray-700">Content</div>
</Card>

// ✅ ALWAYS: Single hover level
// Option A: Card doesn't hover, contents do
<Card>
  <div className="hover:bg-gray-800">Content</div>
</Card>

// Option B: Card hovers, contents don't
<Card className="hover:border-gray-700">
  <div>Content</div>
</Card>
```

### Rule 3: Background Color Consistency

```typescript
// ❌ NEVER: Different grays for hierarchy
<div className="bg-gray-900">        {/* Sidebar */}
  <main className="bg-gray-950">     {/* Main */}
    <Card className="bg-gray-800" /> {/* Card */}
  </main>
</div>

// ✅ ALWAYS: Same background, differentiate with borders
<div className="bg-primary">              {/* All bg-primary */}
  <main className="bg-primary">
    <Card className="border border-gray-800 hover:border-gray-700" />
  </main>
</div>
```

### Rule 4: Card Action Consistency

```typescript
// ❌ NEVER: Inconsistent patterns
<Card action={{ text: "View all", icon: <ArrowRight /> }} />
<Card action={{ text: "Open Canvas", icon: <ArrowUpRight /> }} />
<Card action={{ text: "browse", icon: null }} />

// ✅ ALWAYS: Consistent pattern
<Card action={{ text: "View Analytics", icon: <ArrowRight /> }} />
<Card action={{ text: "View Reports", icon: <ArrowRight /> }} />
<Card action={{ text: "View Settings", icon: <ArrowRight /> }} />
```

### Rule 5: Layout Balance

```typescript
// ❌ NEVER: Imbalanced columns
<div className="grid grid-cols-3">
  <div className="col-span-2">Tall content</div>
  <div className="col-span-1">Short content</div>
</div>

// ✅ ALWAYS: Balanced columns
<div className="grid grid-cols-1 lg:grid-cols-2 gap-6">
  <div>Content A</div>
  <div>Content B</div>
</div>
```

### Rule 6: Card Structure Consistency

```typescript
// ❌ NEVER: Inconsistent card structures
<Card>Header + Content</Card>           // No footer
<Card>Header + Content + Footer</Card>  // Has footer
<Card>Header + Content</Card>           // No footer

// ✅ ALWAYS: All same structure
<Card>Header + Content</Card>
<Card>Header + Content</Card>
<Card>Header + Content</Card>
```

## Pre-Flight Checklist

Before generating page:

```markdown
- [ ] Read product spec
- [ ] Read design system JSON (if custom components needed)
- [ ] List all components needed
- [ ] Check which are in Untitled UI (use those)
- [ ] Identify custom components to build
- [ ] Choose hover strategy (card OR contents)
- [ ] Verify background color plan (all bg-primary)
- [ ] Ensure card actions consistent
- [ ] Plan balanced layout (equal columns)
```

## Post-Generation Validation

After generating page:

```bash
# 1. No arbitrary values
grep -r "bg-\[#" app/ components/    # Should be empty
grep -r "w-\[" app/ components/      # Should be empty

# 2. TypeScript compiles
npm run type-check                    # Should pass

# 3. No unused imports
npm run lint                          # Should pass

# 4. Preview in browser
npm run dev                           # Check visually
```

## Common Patterns

### Dashboard Page

```typescript
// Layout: Header + Grid + Sidebar
- Header: Search + User menu (Untitled UI)
- Metric cards: Custom StatCard
- Activity list: Custom ActivityList
- Sidebar: Untitled UI Card + Button
```

### Form Page

```typescript
// Layout: Centered form
- All form inputs: Untitled UI (Input, Select, Checkbox, etc.)
- Validation: React Hook Form
- Submit: Untitled UI Button
```

### List Page

```typescript
// Layout: Header + Table + Pagination
- Header: Search + Filters (Untitled UI)
- Table: Custom DataTable (if complex) OR simple table
- Pagination: Untitled UI Pagination
```

### Detail Page

```typescript
// Layout: Header + Content + Sidebar
- Header: Breadcrumb + Actions (Untitled UI)
- Content: Mix of Untitled UI + Custom
- Sidebar: Related items (Untitled UI Card)
```

## Output Structure

```
app/
└── [route]/
    └── page.tsx              # Generated page

components/
├── ui/                       # Untitled UI (pre-installed)
└── custom/                   # Custom components
    ├── stat-card.tsx
    ├── activity-list.tsx
    └── [feature-specific].tsx
```

## Troubleshooting

**Component not found:**
```bash
# Check if Untitled UI installed
ls components/ui/button.tsx

# If missing, run init
npx untitledui@latest init untitled-ui --nextjs
```

**Import errors:**
```typescript
// Use @ alias for imports
import { Button } from '@/components/ui/button';  // ✅
import { Button } from '../components/ui/button'; // ❌
```

**Styling not working:**
```bash
# Verify Tailwind config includes app/ and components/
# Check globals.css imported in layout.tsx
```

## Notes

- Always check Untitled UI components first
- Build custom only when necessary
- Follow design rules strictly
- Keep it simple - don't over-engineer
- Test in browser before finishing