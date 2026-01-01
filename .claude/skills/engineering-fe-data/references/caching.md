# Caching Strategies

## React Query Cache Configuration

### Stale Time vs GC Time

| Setting | Purpose | Default |
|---------|---------|---------|
| `staleTime` | How long data is considered fresh | 0 |
| `gcTime` | How long inactive data stays in cache | 5 min |

```ts
// Conservative: Always fresh
{ staleTime: 0, gcTime: 5 * 60 * 1000 }

// Balanced: Fresh for 1 minute
{ staleTime: 60 * 1000, gcTime: 10 * 60 * 1000 }

// Aggressive: Fresh for 5 minutes
{ staleTime: 5 * 60 * 1000, gcTime: 30 * 60 * 1000 }
```

### Per-Query Configuration

```ts
export function useProjects() {
  return useQuery({
    queryKey: ["projects"],
    queryFn: fetchProjects,
    staleTime: 5 * 60 * 1000,  // Projects don't change often
  });
}

export function useNotifications() {
  return useQuery({
    queryKey: ["notifications"],
    queryFn: fetchNotifications,
    staleTime: 0,              // Always check for new notifications
    refetchInterval: 30 * 1000, // Poll every 30 seconds
  });
}
```

## Prefetching Strategies

### On Hover Prefetch

```tsx
"use client";

import { useQueryClient } from "@tanstack/react-query";
import { projectKeys } from "@/lib/api/queries/projects";
import { api } from "@/lib/api/client";
import Link from "next/link";

export function ProjectLink({ project }: { project: Project }) {
  const queryClient = useQueryClient();

  const prefetch = () => {
    queryClient.prefetchQuery({
      queryKey: projectKeys.detail(project.id),
      queryFn: async () => {
        const { data } = await api.GET("/projects/{id}", {
          params: { path: { id: project.id } },
        });
        return data;
      },
      staleTime: 60 * 1000,
    });
  };

  return (
    <Link
      href={`/projects/${project.id}`}
      onMouseEnter={prefetch}
      onFocus={prefetch}
    >
      {project.name}
    </Link>
  );
}
```

### Route Prefetch

```tsx
// Prefetch on page load for likely next navigation
export default function ProjectsPage() {
  const queryClient = useQueryClient();
  const { data: projects } = useProjects();

  useEffect(() => {
    // Prefetch first 3 project details
    projects?.slice(0, 3).forEach((project) => {
      queryClient.prefetchQuery({
        queryKey: projectKeys.detail(project.id),
        queryFn: () => fetchProject(project.id),
      });
    });
  }, [projects, queryClient]);

  return <ProjectList projects={projects} />;
}
```

## Infinite Queries

### Implementation

```ts
export function useInfiniteProjects(filters?: Record<string, string>) {
  return useInfiniteQuery({
    queryKey: ["projects", "infinite", filters],
    queryFn: async ({ pageParam = 1 }) => {
      const { data, error } = await api.GET("/projects", {
        params: {
          query: {
            ...filters,
            page: pageParam,
            limit: 20,
          },
        },
      });
      if (error) throw error;
      return data;
    },
    getNextPageParam: (lastPage) => {
      if (lastPage.page < lastPage.totalPages) {
        return lastPage.page + 1;
      }
      return undefined;
    },
    initialPageParam: 1,
  });
}
```

### Usage

```tsx
"use client";

import { useInfiniteProjects } from "@/lib/api/queries/projects";

export function InfiniteProjectList() {
  const {
    data,
    fetchNextPage,
    hasNextPage,
    isFetchingNextPage,
  } = useInfiniteProjects();

  const projects = data?.pages.flatMap((page) => page.items) ?? [];

  return (
    <div>
      {projects.map((project) => (
        <ProjectCard key={project.id} project={project} />
      ))}

      {hasNextPage && (
        <Button
          onPress={() => fetchNextPage()}
          isDisabled={isFetchingNextPage}
        >
          {isFetchingNextPage ? "Loading..." : "Load More"}
        </Button>
      )}
    </div>
  );
}
```

## Cache Invalidation Patterns

### Granular Invalidation

```ts
// Invalidate single item
queryClient.invalidateQueries({ queryKey: projectKeys.detail(id) });

// Invalidate all lists (keeps details cached)
queryClient.invalidateQueries({ queryKey: projectKeys.lists() });

// Invalidate everything for projects
queryClient.invalidateQueries({ queryKey: projectKeys.all });

// Remove from cache entirely
queryClient.removeQueries({ queryKey: projectKeys.detail(id) });
```

### Cascade Invalidation

```ts
export function useDeleteProject() {
  const queryClient = useQueryClient();

  return useMutation({
    mutationFn: deleteProject,
    onSuccess: (_, deletedId) => {
      // Remove the specific project
      queryClient.removeQueries({ queryKey: projectKeys.detail(deletedId) });
      
      // Invalidate lists (will refetch)
      queryClient.invalidateQueries({ queryKey: projectKeys.lists() });
      
      // Invalidate related data
      queryClient.invalidateQueries({ queryKey: ["tasks", { projectId: deletedId }] });
      queryClient.invalidateQueries({ queryKey: ["stats"] });
    },
  });
}
```

## Server Component Cache

### Next.js Fetch Cache

```tsx
// Cache for 1 hour, revalidate in background
const data = await fetch(url, {
  next: { revalidate: 3600 },
});

// Cache indefinitely until manual revalidation
const data = await fetch(url, {
  next: { tags: ["projects"] },
});

// Revalidate by tag (in Server Action or Route Handler)
import { revalidateTag } from "next/cache";
revalidateTag("projects");

// Revalidate by path
import { revalidatePath } from "next/cache";
revalidatePath("/dashboard/projects");
```

### Combining Server + Client Cache

```tsx
// Server Component - initial data with SSR cache
export default async function ProjectsPage() {
  const initialData = await fetchProjects(); // Cached by Next.js

  return (
    <HydrateClient>
      <ProjectList initialData={initialData} />
    </HydrateClient>
  );
}

// Client Component - hydrates with server data, manages updates
"use client";

export function ProjectList({ initialData }: { initialData: Project[] }) {
  const { data: projects } = useProjects({
    initialData,
    staleTime: 60 * 1000, // Don't refetch immediately
  });

  return /* render */;
}
```

## Dependent Queries

### Sequential Dependencies

```ts
export function useProjectWithTasks(projectId: string) {
  const projectQuery = useProject(projectId);

  const tasksQuery = useQuery({
    queryKey: ["tasks", { projectId }],
    queryFn: () => fetchTasks(projectId),
    enabled: !!projectQuery.data, // Only fetch when project loaded
  });

  return {
    project: projectQuery.data,
    tasks: tasksQuery.data,
    isLoading: projectQuery.isLoading || tasksQuery.isLoading,
  };
}
```

### Parallel with Dependencies

```ts
export function useDashboardData() {
  const userQuery = useCurrentUser();
  
  const results = useQueries({
    queries: [
      {
        queryKey: ["projects", { userId: userQuery.data?.id }],
        queryFn: () => fetchUserProjects(userQuery.data!.id),
        enabled: !!userQuery.data,
      },
      {
        queryKey: ["notifications", { userId: userQuery.data?.id }],
        queryFn: () => fetchUserNotifications(userQuery.data!.id),
        enabled: !!userQuery.data,
      },
    ],
  });

  return {
    user: userQuery.data,
    projects: results[0].data,
    notifications: results[1].data,
    isLoading: userQuery.isLoading || results.some((r) => r.isLoading),
  };
}
```

## Real-Time Updates

### WebSocket Integration

```ts
export function useProjectsRealtime() {
  const queryClient = useQueryClient();

  useEffect(() => {
    const ws = new WebSocket(process.env.NEXT_PUBLIC_WS_URL!);

    ws.onmessage = (event) => {
      const message = JSON.parse(event.data);

      switch (message.type) {
        case "project.created":
          queryClient.invalidateQueries({ queryKey: projectKeys.lists() });
          break;

        case "project.updated":
          queryClient.setQueryData(
            projectKeys.detail(message.payload.id),
            message.payload
          );
          break;

        case "project.deleted":
          queryClient.removeQueries({
            queryKey: projectKeys.detail(message.payload.id),
          });
          queryClient.invalidateQueries({ queryKey: projectKeys.lists() });
          break;
      }
    };

    return () => ws.close();
  }, [queryClient]);

  return useProjects();
}
```

### Server-Sent Events

```ts
export function useSSEUpdates() {
  const queryClient = useQueryClient();

  useEffect(() => {
    const eventSource = new EventSource("/api/events");

    eventSource.onmessage = (event) => {
      const data = JSON.parse(event.data);
      queryClient.invalidateQueries({ queryKey: [data.entity] });
    };

    return () => eventSource.close();
  }, [queryClient]);
}
```