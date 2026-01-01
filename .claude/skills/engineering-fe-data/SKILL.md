---
name: frontend-data
description: API integration and state management for Next.js applications. Handles OpenAPI type generation, data fetching patterns (React Query, Server Components), caching strategies, and state management decisions. Triggers on: API integration, data fetching, React Query setup, state management, caching, optimistic updates, type generation from OpenAPI/Swagger.
---

# Frontend Data Layer

Integrate APIs and manage application state in Next.js.

## Decision Tree

```
Data type?
│
├─ Server state (API data)
│   ├─ Static/SSR content → Server Components (fetch directly)
│   ├─ Dynamic/interactive → React Query (client-side caching)
│   └─ Real-time → WebSocket + React Query
│
├─ Client state (UI state)
│   ├─ Local to component → useState
│   ├─ Shared across components → Zustand
│   └─ Simple prop drilling → Context (sparingly)
│
├─ URL state (filters, pagination)
│   └─ nuqs or useSearchParams
│
└─ Form state
    └─ See frontend-forms skill
```

## Type Generation from OpenAPI

### Setup

```bash
npm install openapi-typescript openapi-fetch
```

### Generate Types

```bash
# From URL
npx openapi-typescript https://api.example.com/openapi.json -o src/lib/api/types.ts

# From local file
npx openapi-typescript ./openapi.yaml -o src/lib/api/types.ts
```

### Package.json Script

```json
{
  "scripts": {
    "generate:types": "openapi-typescript $API_URL/openapi.json -o src/lib/api/types.ts"
  }
}
```

### Type-Safe Client

```ts
// src/lib/api/client.ts
import createClient from "openapi-fetch";
import type { paths } from "./types";

export const api = createClient<paths>({
  baseUrl: process.env.NEXT_PUBLIC_API_URL,
});

// Usage - fully typed
const { data, error } = await api.GET("/projects/{id}", {
  params: { path: { id: "123" } },
});
```

## Server Components Data Fetching

### Direct Fetch (Preferred for SSR)

```tsx
// app/(dashboard)/projects/page.tsx
import { api } from "@/lib/api/client";

export default async function ProjectsPage() {
  const { data: projects, error } = await api.GET("/projects");

  if (error) throw new Error(error.message);

  return <ProjectList projects={projects} />;
}
```

### With Caching Control

```tsx
// Revalidate every 60 seconds
export const revalidate = 60;

// Or per-fetch
const { data } = await api.GET("/projects", {
  next: { revalidate: 60 },
});

// No cache (always fresh)
const { data } = await api.GET("/projects", {
  cache: "no-store",
});
```

### Parallel Fetching

```tsx
export default async function DashboardPage() {
  // Parallel - don't await sequentially
  const [projectsRes, statsRes, notificationsRes] = await Promise.all([
    api.GET("/projects"),
    api.GET("/stats"),
    api.GET("/notifications"),
  ]);

  return (
    <>
      <Stats data={statsRes.data} />
      <Projects data={projectsRes.data} />
      <Notifications data={notificationsRes.data} />
    </>
  );
}
```

## React Query Setup

### Provider Configuration

```tsx
// src/providers/QueryProvider.tsx
"use client";

import { QueryClient, QueryClientProvider } from "@tanstack/react-query";
import { ReactQueryDevtools } from "@tanstack/react-query-devtools";
import { useState } from "react";

export function QueryProvider({ children }: { children: React.ReactNode }) {
  const [queryClient] = useState(
    () =>
      new QueryClient({
        defaultOptions: {
          queries: {
            staleTime: 60 * 1000,        // 1 minute
            gcTime: 5 * 60 * 1000,       // 5 minutes (formerly cacheTime)
            retry: 1,
            refetchOnWindowFocus: false,
          },
        },
      })
  );

  return (
    <QueryClientProvider client={queryClient}>
      {children}
      <ReactQueryDevtools initialIsOpen={false} />
    </QueryClientProvider>
  );
}
```

```tsx
// app/layout.tsx
import { QueryProvider } from "@/providers/QueryProvider";

export default function RootLayout({ children }: { children: React.ReactNode }) {
  return (
    <html>
      <body>
        <QueryProvider>{children}</QueryProvider>
      </body>
    </html>
  );
}
```

### Query Hooks Pattern

```ts
// src/lib/api/queries/projects.ts
import { useQuery, useMutation, useQueryClient } from "@tanstack/react-query";
import { api } from "../client";
import type { components } from "../types";

type Project = components["schemas"]["Project"];
type CreateProjectInput = components["schemas"]["CreateProjectInput"];

export const projectKeys = {
  all: ["projects"] as const,
  lists: () => [...projectKeys.all, "list"] as const,
  list: (filters: Record<string, string>) => [...projectKeys.lists(), filters] as const,
  details: () => [...projectKeys.all, "detail"] as const,
  detail: (id: string) => [...projectKeys.details(), id] as const,
};

export function useProjects(filters?: Record<string, string>) {
  return useQuery({
    queryKey: projectKeys.list(filters ?? {}),
    queryFn: async () => {
      const { data, error } = await api.GET("/projects", {
        params: { query: filters },
      });
      if (error) throw error;
      return data;
    },
  });
}

export function useProject(id: string) {
  return useQuery({
    queryKey: projectKeys.detail(id),
    queryFn: async () => {
      const { data, error } = await api.GET("/projects/{id}", {
        params: { path: { id } },
      });
      if (error) throw error;
      return data;
    },
    enabled: !!id,
  });
}
```

### Mutations Pattern

```ts
// src/lib/api/mutations/projects.ts
import { useMutation, useQueryClient } from "@tanstack/react-query";
import { api } from "../client";
import { projectKeys } from "../queries/projects";

export function useCreateProject() {
  const queryClient = useQueryClient();

  return useMutation({
    mutationFn: async (input: CreateProjectInput) => {
      const { data, error } = await api.POST("/projects", {
        body: input,
      });
      if (error) throw error;
      return data;
    },
    onSuccess: () => {
      queryClient.invalidateQueries({ queryKey: projectKeys.lists() });
    },
  });
}

export function useUpdateProject() {
  const queryClient = useQueryClient();

  return useMutation({
    mutationFn: async ({ id, ...input }: { id: string } & UpdateProjectInput) => {
      const { data, error } = await api.PATCH("/projects/{id}", {
        params: { path: { id } },
        body: input,
      });
      if (error) throw error;
      return data;
    },
    onSuccess: (data) => {
      queryClient.invalidateQueries({ queryKey: projectKeys.detail(data.id) });
      queryClient.invalidateQueries({ queryKey: projectKeys.lists() });
    },
  });
}

export function useDeleteProject() {
  const queryClient = useQueryClient();

  return useMutation({
    mutationFn: async (id: string) => {
      const { error } = await api.DELETE("/projects/{id}", {
        params: { path: { id } },
      });
      if (error) throw error;
    },
    onSuccess: (_, id) => {
      queryClient.removeQueries({ queryKey: projectKeys.detail(id) });
      queryClient.invalidateQueries({ queryKey: projectKeys.lists() });
    },
  });
}
```

## Optimistic Updates

```ts
export function useUpdateProjectOptimistic() {
  const queryClient = useQueryClient();

  return useMutation({
    mutationFn: async ({ id, ...input }: { id: string } & UpdateProjectInput) => {
      const { data, error } = await api.PATCH("/projects/{id}", {
        params: { path: { id } },
        body: input,
      });
      if (error) throw error;
      return data;
    },
    onMutate: async ({ id, ...input }) => {
      // Cancel outgoing refetches
      await queryClient.cancelQueries({ queryKey: projectKeys.detail(id) });

      // Snapshot previous value
      const previous = queryClient.getQueryData(projectKeys.detail(id));

      // Optimistically update
      queryClient.setQueryData(projectKeys.detail(id), (old: Project) => ({
        ...old,
        ...input,
      }));

      return { previous };
    },
    onError: (err, { id }, context) => {
      // Rollback on error
      queryClient.setQueryData(projectKeys.detail(id), context?.previous);
    },
    onSettled: (_, __, { id }) => {
      // Refetch after settle
      queryClient.invalidateQueries({ queryKey: projectKeys.detail(id) });
    },
  });
}
```

## Client State with Zustand

### Store Definition

```ts
// src/stores/ui-store.ts
import { create } from "zustand";
import { persist } from "zustand/middleware";

interface UIState {
  sidebarOpen: boolean;
  theme: "light" | "dark" | "system";
  toggleSidebar: () => void;
  setTheme: (theme: UIState["theme"]) => void;
}

export const useUIStore = create<UIState>()(
  persist(
    (set) => ({
      sidebarOpen: true,
      theme: "system",
      toggleSidebar: () => set((state) => ({ sidebarOpen: !state.sidebarOpen })),
      setTheme: (theme) => set({ theme }),
    }),
    {
      name: "ui-storage",
    }
  )
);
```

### Usage

```tsx
"use client";

import { useUIStore } from "@/stores/ui-store";

export function Sidebar() {
  const { sidebarOpen, toggleSidebar } = useUIStore();

  if (!sidebarOpen) return null;

  return (
    <aside>
      {/* sidebar content */}
      <button onClick={toggleSidebar}>Close</button>
    </aside>
  );
}
```

## URL State with nuqs

### Setup

```bash
npm install nuqs
```

### Usage

```tsx
"use client";

import { useQueryState, parseAsString, parseAsInteger } from "nuqs";

export function ProjectFilters() {
  const [status, setStatus] = useQueryState("status", parseAsString);
  const [page, setPage] = useQueryState("page", parseAsInteger.withDefault(1));

  return (
    <div>
      <Select value={status} onValueChange={setStatus}>
        <SelectItem value="active">Active</SelectItem>
        <SelectItem value="archived">Archived</SelectItem>
      </Select>
      <Pagination page={page} onPageChange={setPage} />
    </div>
  );
}
```

## Error Handling

### API Error Wrapper

```ts
// src/lib/api/errors.ts
export class APIError extends Error {
  constructor(
    message: string,
    public status: number,
    public code?: string
  ) {
    super(message);
    this.name = "APIError";
  }
}

export function handleAPIError(error: unknown): never {
  if (error && typeof error === "object" && "message" in error) {
    const apiError = error as { message: string; status?: number; code?: string };
    throw new APIError(
      apiError.message,
      apiError.status ?? 500,
      apiError.code
    );
  }
  throw new APIError("An unexpected error occurred", 500);
}
```

### React Query Error Boundary

```tsx
// src/components/QueryErrorBoundary.tsx
"use client";

import { QueryErrorResetBoundary } from "@tanstack/react-query";
import { ErrorBoundary } from "react-error-boundary";
import { Alert } from "@/components/ui/Alert";
import { Button } from "@/components/ui/Button";

export function QueryErrorBoundary({ children }: { children: React.ReactNode }) {
  return (
    <QueryErrorResetBoundary>
      {({ reset }) => (
        <ErrorBoundary
          onReset={reset}
          fallbackRender={({ error, resetErrorBoundary }) => (
            <Alert type="error" title="Failed to load data">
              <p>{error.message}</p>
              <Button onPress={resetErrorBoundary}>Retry</Button>
            </Alert>
          )}
        >
          {children}
        </ErrorBoundary>
      )}
    </QueryErrorResetBoundary>
  );
}
```

## File Structure

```
src/lib/api/
├─ client.ts           # openapi-fetch client
├─ types.ts            # Generated from OpenAPI
├─ errors.ts           # Error handling
├─ queries/            # React Query hooks
│   ├─ projects.ts
│   ├─ users.ts
│   └─ index.ts
└─ mutations/          # Mutation hooks
    ├─ projects.ts
    └─ index.ts

src/stores/            # Zustand stores
├─ ui-store.ts
└─ index.ts

src/providers/
└─ QueryProvider.tsx
```

## References

- **Caching strategies**: See [references/caching.md](references/caching.md) for advanced caching patterns
- **Integration**: Coordinates with `frontend-architecture` for data dependencies, `frontend-forms` for form submissions