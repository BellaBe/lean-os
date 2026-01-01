# Advanced Architecture Patterns

## Parallel Routes

Use for simultaneous rendering of multiple pages in the same layout.

### Use Cases
- Dashboard with multiple independent panels
- Modal routes that preserve background content
- Split views (list + detail)

### Implementation

```
app/(dashboard)/
├─ layout.tsx
├─ page.tsx
├─ @analytics/        # Slot
│   ├─ page.tsx
│   └─ loading.tsx
└─ @notifications/    # Slot
    ├─ page.tsx
    └─ loading.tsx
```

```tsx
// layout.tsx
export default function Layout({
  children,
  analytics,
  notifications,
}: {
  children: React.ReactNode;
  analytics: React.ReactNode;
  notifications: React.ReactNode;
}) {
  return (
    <div className="grid grid-cols-3 gap-4">
      <div className="col-span-2">{children}</div>
      <aside>
        {analytics}
        {notifications}
      </aside>
    </div>
  );
}
```

## Intercepting Routes

Use for modal overlays that preserve context.

### Use Cases
- Photo galleries (click to expand, URL changes)
- Quick edit modals
- Preview panels

### Implementation

```
app/(dashboard)/projects/
├─ page.tsx                    # List view
├─ [id]/
│   └─ page.tsx               # Full detail page (direct nav)
└─ (.)projects/[id]/          # Intercepted route (soft nav)
    └─ page.tsx               # Modal view
```

```tsx
// (.)projects/[id]/page.tsx
import { Modal } from "@/components/ui/Modal";
import { ProjectDetail } from "@/features/projects/ProjectDetail";

export default function InterceptedProject({ params }: { params: { id: string } }) {
  return (
    <Modal>
      <ProjectDetail id={params.id} />
    </Modal>
  );
}
```

### Interception Conventions

| Pattern | Matches |
|---------|---------|
| `(.)` | Same level |
| `(..)` | One level up |
| `(..)(..)` | Two levels up |
| `(...)` | From root |

## Middleware Patterns

### Authentication Guard

```ts
// middleware.ts
import { NextResponse } from "next/server";
import type { NextRequest } from "next/server";

const publicPaths = ["/", "/login", "/signup", "/pricing"];
const authPaths = ["/login", "/signup"];

export function middleware(request: NextRequest) {
  const { pathname } = request.nextUrl;
  const token = request.cookies.get("auth-token");

  // Redirect authenticated users away from auth pages
  if (authPaths.includes(pathname) && token) {
    return NextResponse.redirect(new URL("/dashboard", request.url));
  }

  // Protect dashboard routes
  if (pathname.startsWith("/dashboard") && !token) {
    const loginUrl = new URL("/login", request.url);
    loginUrl.searchParams.set("callbackUrl", pathname);
    return NextResponse.redirect(loginUrl);
  }

  return NextResponse.next();
}

export const config = {
  matcher: ["/((?!api|_next/static|_next/image|favicon.ico).*)"],
};
```

### Role-Based Access

```ts
// middleware.ts
const roleRoutes: Record<string, string[]> = {
  admin: ["/admin", "/dashboard"],
  user: ["/dashboard"],
  guest: ["/"],
};

export function middleware(request: NextRequest) {
  const role = request.cookies.get("user-role")?.value || "guest";
  const { pathname } = request.nextUrl;

  const allowedPaths = roleRoutes[role] || [];
  const hasAccess = allowedPaths.some((path) => pathname.startsWith(path));

  if (!hasAccess) {
    return NextResponse.redirect(new URL("/unauthorized", request.url));
  }

  return NextResponse.next();
}
```

## Route Handlers (API Routes)

### RESTful Pattern

```
app/api/
├─ projects/
│   ├─ route.ts           # GET (list), POST (create)
│   └─ [id]/
│       └─ route.ts       # GET, PATCH, DELETE
└─ users/
    └─ me/
        └─ route.ts       # GET current user
```

```ts
// app/api/projects/route.ts
import { NextRequest, NextResponse } from "next/server";
import { getSession } from "@/lib/auth";
import { db } from "@/lib/db";

export async function GET(request: NextRequest) {
  const session = await getSession();
  if (!session) {
    return NextResponse.json({ error: "Unauthorized" }, { status: 401 });
  }

  const { searchParams } = new URL(request.url);
  const status = searchParams.get("status");

  const projects = await db.project.findMany({
    where: { userId: session.user.id, ...(status && { status }) },
  });

  return NextResponse.json(projects);
}

export async function POST(request: NextRequest) {
  const session = await getSession();
  if (!session) {
    return NextResponse.json({ error: "Unauthorized" }, { status: 401 });
  }

  const body = await request.json();
  const project = await db.project.create({
    data: { ...body, userId: session.user.id },
  });

  return NextResponse.json(project, { status: 201 });
}
```

## Dynamic Metadata

### Page-Level SEO

```tsx
// app/(dashboard)/projects/[id]/page.tsx
import type { Metadata } from "next";
import { getProject } from "@/lib/api";

type Props = {
  params: { id: string };
};

export async function generateMetadata({ params }: Props): Promise<Metadata> {
  const project = await getProject(params.id);

  return {
    title: project.name,
    description: project.description,
    openGraph: {
      title: project.name,
      images: [project.coverImage],
    },
  };
}

export default async function ProjectPage({ params }: Props) {
  const project = await getProject(params.id);
  // ...
}
```

## Feature Module Pattern

For complex features with multiple components, hooks, and utilities:

```
src/features/
└─ billing/
    ├─ components/
    │   ├─ PricingCard.tsx
    │   ├─ SubscriptionStatus.tsx
    │   └─ PaymentForm.tsx
    ├─ hooks/
    │   ├─ useSubscription.ts
    │   └─ usePaymentMethods.ts
    ├─ api/
    │   ├─ queries.ts      # React Query queries
    │   └─ mutations.ts    # React Query mutations
    ├─ types.ts
    ├─ utils.ts
    └─ index.ts            # Public exports
```

```ts
// features/billing/index.ts
export { PricingCard } from "./components/PricingCard";
export { SubscriptionStatus } from "./components/SubscriptionStatus";
export { useSubscription } from "./hooks/useSubscription";
export type { Subscription, PaymentMethod } from "./types";
```

## Colocation vs Separation

### When to Colocate (Route-Specific)

```
app/(dashboard)/projects/
└─ _components/          # Underscore = not a route
    ├─ ProjectCard.tsx   # Only used in projects
    └─ ProjectFilters.tsx
```

### When to Separate (Shared)

```
src/components/common/
├─ DataTable.tsx         # Used across multiple routes
├─ EmptyState.tsx
└─ ConfirmDialog.tsx
```

### Decision Criteria

| Criteria | Colocate | Separate |
|----------|----------|----------|
| Used in one route | ✓ | |
| Used in multiple routes | | ✓ |
| Has route-specific logic | ✓ | |
| Pure presentation | | ✓ |
| Complex with own hooks | | ✓ (feature module) |