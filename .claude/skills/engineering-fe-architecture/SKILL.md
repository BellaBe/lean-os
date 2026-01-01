---
name: frontend-architecture
description: Transform product requirements into Next.js application structure. Maps PRD/user stories to routes, layouts, component hierarchy, and page organization. Triggers on: new feature planning, route structure decisions, component breakdown, page organization, layout hierarchy, server vs client component decisions, Next.js App Router architecture.
---

# Frontend Architecture

Transform product specifications into structured Next.js applications.

## Input

**Location**: `artifacts/{product}/features/{feature-slug}/v{N}/handoff.md`

### Extract for Architecture

| Handoff Section | Architecture Decision |
|-----------------|----------------------|
| **Scope → In Scope** | Routes to create |
| **Scope → Out of Scope** | Routes to exclude |
| **Scope → Constraints** | Performance budgets, tech limits |
| **Acceptance Criteria** | Component states (loading, error, empty, success) |
| **Examples** | Navigation flows, state transitions |
| **Quality Bar → Performance** | Server vs client boundaries, code splitting |
| **Quality Bar → Accessibility** | Semantic HTML, keyboard nav requirements |

### Handoff Check
```bash
HANDOFF="artifacts/{product}/features/{feature-slug}/v{N}/handoff.md"
cat "$HANDOFF"
```

**Missing handoff?** → Stop. Request product-handoff first.


## Route Extraction Process

### 1. Identify Core Entities

From requirements, extract:
- **Nouns** → Resources (users, products, orders, settings)
- **Verbs** → Actions (create, edit, view, list, delete)
- **Flows** → Multi-step processes (checkout, onboarding, wizards)

### 2. Map to Route Structure

```
Entity + Action → Route Pattern
─────────────────────────────────
list            → /[entity]
view            → /[entity]/[id]
create          → /[entity]/new
edit            → /[entity]/[id]/edit
nested resource → /[entity]/[id]/[sub-entity]
settings        → /settings/[section]
auth            → /(auth)/login, /(auth)/signup
```

### 3. Apply Route Groups

```
app/
├─ (marketing)/          # Public pages, shared marketing layout
│   ├─ page.tsx          # Landing
│   ├─ pricing/
│   └─ about/
├─ (auth)/               # Auth flow, minimal layout
│   ├─ login/
│   ├─ signup/
│   └─ forgot-password/
├─ (dashboard)/          # Authenticated, sidebar layout
│   ├─ layout.tsx        # Sidebar + header
│   ├─ page.tsx          # Dashboard home
│   ├─ projects/
│   │   ├─ page.tsx      # List
│   │   ├─ new/
│   │   └─ [id]/
│   │       ├─ page.tsx  # View
│   │       └─ edit/
│   └─ settings/
│       ├─ page.tsx
│       ├─ profile/
│       └─ billing/
└─ api/                  # API routes (if needed)
```

## Layout Hierarchy

### Layout Responsibility Matrix

| Layout Level | Responsibilities |
|-------------|------------------|
| Root (`app/layout.tsx`) | Providers, fonts, global styles, metadata |
| Route Group (`(dashboard)/layout.tsx`) | Navigation, auth guards, shared UI shell |
| Section (`settings/layout.tsx`) | Section-specific nav, breadcrumbs |
| Page (`page.tsx`) | Page content, data fetching |

### Layout Template

```tsx
// (dashboard)/layout.tsx
import { redirect } from "next/navigation";
import { getSession } from "@/lib/auth";
import { Sidebar } from "@/components/navigation/Sidebar";
import { Header } from "@/components/navigation/Header";

export default async function DashboardLayout({
  children,
}: {
  children: React.ReactNode;
}) {
  const session = await getSession();
  if (!session) redirect("/login");

  return (
    <div className="flex h-screen">
      <Sidebar user={session.user} />
      <div className="flex-1 flex flex-col">
        <Header />
        <main className="flex-1 overflow-auto p-6">{children}</main>
      </div>
    </div>
  );
}
```

## Component Hierarchy

### Decomposition Rules

```
Page → Sections → Features → UI Components
───────────────────────────────────────────
Page           Owns layout, data fetching, SEO
Section        Logical grouping (header, content, sidebar)
Feature        Business logic unit (UserTable, ProjectCard)
UI Component   Pure presentation (Button, Input, Modal)
```

### Component Location Strategy

```
src/
├─ components/
│   ├─ ui/              # Design system atoms (from untitled-ui)
│   │   ├─ Button.tsx
│   │   └─ Input.tsx
│   ├─ navigation/      # App-wide navigation
│   │   ├─ Sidebar.tsx
│   │   └─ Header.tsx
│   └─ common/          # Shared feature components
│       ├─ DataTable.tsx
│       └─ EmptyState.tsx
├─ app/
│   └─ (dashboard)/
│       └─ projects/
│           └─ _components/   # Route-specific components
│               ├─ ProjectCard.tsx
│               └─ ProjectFilters.tsx
└─ features/            # Complex feature modules (optional)
    └─ billing/
        ├─ components/
        ├─ hooks/
        └─ utils/
```

## Server vs Client Components

### Decision Matrix

| Requirement | Component Type | Rationale |
|------------|----------------|-----------|
| Data fetching | Server | Direct DB/API access, no waterfall |
| SEO content | Server | HTML in initial response |
| Static UI | Server | Smaller bundle |
| Interactivity | Client | Event handlers, state |
| Browser APIs | Client | localStorage, geolocation |
| Real-time updates | Client | WebSocket, polling |
| Form handling | Client | Controlled inputs, validation |

### Composition Pattern

```tsx
// Server component (default)
// app/(dashboard)/projects/page.tsx
import { getProjects } from "@/lib/api";
import { ProjectList } from "./_components/ProjectList";
import { ProjectFilters } from "./_components/ProjectFilters";

export default async function ProjectsPage() {
  const projects = await getProjects();
  
  return (
    <div>
      <ProjectFilters />          {/* Client: has state */}
      <ProjectList data={projects} /> {/* Server: renders list */}
    </div>
  );
}
```

```tsx
// Client component
// app/(dashboard)/projects/_components/ProjectFilters.tsx
"use client";

import { useState } from "react";
import { useRouter, useSearchParams } from "next/navigation";

export function ProjectFilters() {
  const [status, setStatus] = useState("");
  // Filter logic...
}
```

## Page Structure Template

```tsx
// Standard page structure
import { PageHeader } from "@/components/application/PageHeader";
import { SectionHeader } from "@/components/application/SectionHeader";

export default async function EntityPage() {
  // 1. Data fetching (server)
  const data = await fetchData();

  return (
    <>
      {/* 2. Page header with actions */}
      <PageHeader
        title="Projects"
        description="Manage your projects"
        actions={<CreateButton />}
      />

      {/* 3. Filters/controls (if needed) */}
      <FiltersSection />

      {/* 4. Main content */}
      <section>
        <SectionHeader title="Active Projects" />
        <ContentComponent data={data} />
      </section>

      {/* 5. Secondary content (if needed) */}
      <section>
        <SectionHeader title="Archived" />
        <ArchivedContent />
      </section>
    </>
  );
}
```

## Loading & Error States

### File Convention

```
app/(dashboard)/projects/
├─ page.tsx           # Main content
├─ loading.tsx        # Suspense fallback
├─ error.tsx          # Error boundary
└─ not-found.tsx      # 404 for this route
```

### Loading Template

```tsx
// loading.tsx
import { Skeleton } from "@/components/ui/Skeleton";

export default function Loading() {
  return (
    <div className="space-y-4">
      <Skeleton className="h-10 w-48" />  {/* Title */}
      <Skeleton className="h-64 w-full" /> {/* Content */}
    </div>
  );
}
```

### Error Template

```tsx
// error.tsx
"use client";

import { Alert } from "@/components/application/Alert";
import { Button } from "@/components/ui/Button";

export default function Error({
  error,
  reset,
}: {
  error: Error;
  reset: () => void;
}) {
  return (
    <Alert type="error" title="Something went wrong">
      <p>{error.message}</p>
      <Button onPress={reset}>Try again</Button>
    </Alert>
  );
}
```

## Output Specification

When analyzing requirements, produce:

### 1. Route Map
```
/                       → Landing (marketing)
/login                  → Auth
/dashboard              → Dashboard home
/dashboard/projects     → Project list
/dashboard/projects/new → Create project
/dashboard/projects/[id] → Project detail
/dashboard/settings     → Settings
```

### 2. Component Tree
```
DashboardLayout
├─ Sidebar
│   ├─ Logo
│   ├─ NavItems
│   └─ UserMenu
├─ Header
│   ├─ Breadcrumbs
│   └─ Actions
└─ {children}
    └─ ProjectsPage
        ├─ PageHeader
        ├─ ProjectFilters (client)
        └─ ProjectList
            └─ ProjectCard
```

### 3. Data Dependencies
```
ProjectsPage
├─ getProjects() → Server fetch
├─ filters → URL searchParams
└─ mutations → See frontend-data skill
```

## References

| File | Contents |
|------|----------|
| [patterns.md](references/patterns.md) | Advanced patterns (parallel routes, intercepting routes, middleware) |
| [app-router.md](references/app-router.md) | Server/Client components, streaming, caching, Server Actions |
| [performance.md](references/performance.md) | Images, fonts, code splitting, Core Web Vitals |
| [i18n.md](references/i18n.md) | Internationalization with next-intl |

**Integration**: Coordinates with `untitled-ui` for components, `frontend-data` for data layer