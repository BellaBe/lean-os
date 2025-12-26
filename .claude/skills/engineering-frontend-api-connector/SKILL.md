---
name: frontend-api-connector
description: Connect frontend pages to backend APIs. Adds data fetching, loading states, error handling to existing pages. Use after backend APIs are ready.
allowed-tools: Read, Write, Bash
---

# Frontend API Connector Skill

Connect static pages to backend APIs with type-safe data fetching.

## Purpose

Static page → Data-connected page with loading/error states

## Inputs

**Required:**
- Page file: `app/[route]/page.tsx`
- API specification: `artifacts/backend/api-spec.yaml` or similar

**Optional:**
- Existing API client setup
- Authentication setup

## Connection Strategy

### Next.js App Router Patterns

**Server Components (Default):**
```typescript
// For pages that don't need client interactivity
// Fetches data on server, sends HTML to client
export default async function Page() {
  const data = await fetchData();
  return <div>{data}</div>;
}
```

**Client Components:**
```typescript
// For pages with interactivity (forms, real-time updates)
'use client';
import { useQuery } from '@tanstack/react-query';

export default function Page() {
  const { data, isLoading } = useQuery({...});
  return <div>{data}</div>;
}
```

## API Integration Process

### Step 1: Read API Specification

```yaml
# From artifacts/backend/api-spec.yaml

endpoints:
  - path: /api/metrics
    method: GET
    auth: required
    response:
      revenue: number
      users: number
      growth: string
      trend: 'up' | 'down'
      
  - path: /api/activity
    method: GET
    auth: required
    query:
      limit?: number
      offset?: number
    response:
      items: Activity[]
      total: number
```

### Step 2: Generate TypeScript Types

```typescript
// lib/api/types.ts

export interface Metrics {
  revenue: number;
  users: number;
  growth: string;
  trend: 'up' | 'down';
}

export interface Activity {
  id: string;
  userId: string;
  action: string;
  timestamp: string;
  type: 'success' | 'warning' | 'info';
}

export interface ActivityResponse {
  items: Activity[];
  total: number;
}

export interface ApiError {
  error: string;
  message: string;
  status: number;
}
```

### Step 3: Create API Client

```typescript
// lib/api/client.ts

const API_BASE = process.env.NEXT_PUBLIC_API_URL || 'http://localhost:3000';

class ApiError extends Error {
  constructor(
    public status: number,
    message: string,
    public data?: any
  ) {
    super(message);
    this.name = 'ApiError';
  }
}

async function fetchApi<T>(
  endpoint: string,
  options?: RequestInit
): Promise<T> {
  const response = await fetch(`${API_BASE}${endpoint}`, {
    ...options,
    headers: {
      'Content-Type': 'application/json',
      ...options?.headers,
    },
  });

  if (!response.ok) {
    const error = await response.json().catch(() => ({}));
    throw new ApiError(
      response.status,
      error.message || 'Request failed',
      error
    );
  }

  return response.json();
}

// Metrics API
export async function getMetrics(): Promise<Metrics> {
  return fetchApi<Metrics>('/api/metrics');
}

// Activity API
export async function getActivity(
  limit = 10,
  offset = 0
): Promise<ActivityResponse> {
  return fetchApi<ActivityResponse>(
    `/api/activity?limit=${limit}&offset=${offset}`
  );
}

// With authentication
export async function getMetricsAuth(token: string): Promise<Metrics> {
  return fetchApi<Metrics>('/api/metrics', {
    headers: {
      'Authorization': `Bearer ${token}`,
    },
  });
}
```

### Step 4: Connect to Page (Server Component)

```typescript
// app/dashboard/page.tsx
import { getMetrics, getActivity } from '@/lib/api/client';
import { StatCard } from '@/components/custom/stat-card';
import { ActivityList } from '@/components/custom/activity-list';

export default async function DashboardPage() {
  // Fetch data on server
  const [metrics, activity] = await Promise.all([
    getMetrics(),
    getActivity(10, 0)
  ]);

  return (
    <div className="p-8">
      <div className="grid grid-cols-2 gap-4 mb-6">
        <StatCard 
          title="Revenue" 
          value={`$${metrics.revenue}`}
          change={metrics.growth}
          trend={metrics.trend}
        />
        <StatCard 
          title="Users" 
          value={metrics.users.toString()}
        />
      </div>

      <ActivityList activities={activity.items} />
    </div>
  );
}

// Loading state (automatic with Next.js)
// Create: app/dashboard/loading.tsx
export default function Loading() {
  return <div>Loading...</div>;
}

// Error handling (automatic with Next.js)
// Create: app/dashboard/error.tsx
'use client';

export default function Error({
  error,
  reset,
}: {
  error: Error;
  reset: () => void;
}) {
  return (
    <div className="p-8">
      <h2>Something went wrong!</h2>
      <p>{error.message}</p>
      <button onClick={reset}>Try again</button>
    </div>
  );
}
```

### Step 5: Connect to Page (Client Component)

**For interactive/real-time data:**

```typescript
// app/dashboard/page.tsx
'use client';

import { useQuery } from '@tanstack/react-query';
import { getMetrics, getActivity } from '@/lib/api/client';
import { StatCard } from '@/components/custom/stat-card';
import { ActivityList } from '@/components/custom/activity-list';
import { Skeleton } from '@/components/ui/skeleton';
import { Alert } from '@/components/ui/alert';
import { Button } from '@/components/ui/button';

export default function DashboardPage() {
  // Fetch metrics
  const {
    data: metrics,
    isLoading: metricsLoading,
    error: metricsError,
    refetch: refetchMetrics
  } = useQuery({
    queryKey: ['metrics'],
    queryFn: getMetrics,
    refetchInterval: 30000, // Refetch every 30s
  });

  // Fetch activity
  const {
    data: activity,
    isLoading: activityLoading,
    error: activityError
  } = useQuery({
    queryKey: ['activity'],
    queryFn: () => getActivity(10, 0),
  });

  // Loading state
  if (metricsLoading || activityLoading) {
    return (
      <div className="p-8">
        <div className="grid grid-cols-2 gap-4 mb-6">
          <Skeleton className="h-32" />
          <Skeleton className="h-32" />
        </div>
        <Skeleton className="h-64" />
      </div>
    );
  }

  // Error state
  if (metricsError || activityError) {
    return (
      <div className="p-8">
        <Alert variant="error">
          <p>Failed to load dashboard data</p>
          <Button onClick={() => {
            refetchMetrics();
          }} size="sm" className="mt-2">
            Retry
          </Button>
        </Alert>
      </div>
    );
  }

  // Success state
  return (
    <div className="p-8">
      <div className="grid grid-cols-2 gap-4 mb-6">
        <StatCard 
          title="Revenue" 
          value={`$${metrics!.revenue}`}
          change={metrics!.growth}
          trend={metrics!.trend}
        />
        <StatCard 
          title="Users" 
          value={metrics!.users.toString()}
        />
      </div>

      <ActivityList activities={activity!.items} />
    </div>
  );
}
```

### Step 6: Setup React Query (If Using Client Components)

```typescript
// app/providers.tsx
'use client';

import { QueryClient, QueryClientProvider } from '@tanstack/react-query';
import { useState } from 'react';

export function Providers({ children }: { children: React.ReactNode }) {
  const [queryClient] = useState(() => new QueryClient({
    defaultOptions: {
      queries: {
        staleTime: 60 * 1000, // 1 minute
        retry: 1,
      },
    },
  }));

  return (
    <QueryClientProvider client={queryClient}>
      {children}
    </QueryClientProvider>
  );
}

// app/layout.tsx
import { Providers } from './providers';

export default function RootLayout({ children }) {
  return (
    <html>
      <body>
        <Providers>
          {children}
        </Providers>
      </body>
    </html>
  );
}
```

## Authentication Patterns

### With Session (Cookies)

```typescript
// lib/api/client.ts
export async function fetchWithAuth<T>(
  endpoint: string,
  options?: RequestInit
): Promise<T> {
  return fetchApi<T>(endpoint, {
    ...options,
    credentials: 'include', // Include cookies
  });
}
```

### With Token (Bearer)

```typescript
// lib/auth.ts
export function getAuthToken(): string | null {
  return localStorage.getItem('auth_token');
}

// lib/api/client.ts
export async function fetchWithToken<T>(
  endpoint: string,
  options?: RequestInit
): Promise<T> {
  const token = getAuthToken();
  
  if (!token) {
    throw new Error('Not authenticated');
  }

  return fetchApi<T>(endpoint, {
    ...options,
    headers: {
      ...options?.headers,
      'Authorization': `Bearer ${token}`,
    },
  });
}
```

## Advanced Patterns

### Mutations (POST/PUT/DELETE)

```typescript
// lib/api/client.ts
export async function createActivity(
  data: Omit<Activity, 'id' | 'timestamp'>
): Promise<Activity> {
  return fetchApi<Activity>('/api/activity', {
    method: 'POST',
    body: JSON.stringify(data),
  });
}

// In component
import { useMutation, useQueryClient } from '@tanstack/react-query';

function CreateActivityForm() {
  const queryClient = useQueryClient();
  
  const mutation = useMutation({
    mutationFn: createActivity,
    onSuccess: () => {
      // Invalidate and refetch
      queryClient.invalidateQueries({ queryKey: ['activity'] });
    },
  });

  const handleSubmit = (data) => {
    mutation.mutate(data);
  };

  return (
    <form onSubmit={handleSubmit}>
      {/* Form fields */}
      <Button 
        type="submit" 
        disabled={mutation.isPending}
      >
        {mutation.isPending ? 'Saving...' : 'Save'}
      </Button>
    </form>
  );
}
```

### Optimistic Updates

```typescript
const mutation = useMutation({
  mutationFn: updateActivity,
  onMutate: async (newActivity) => {
    // Cancel outgoing refetches
    await queryClient.cancelQueries({ queryKey: ['activity'] });

    // Snapshot previous value
    const previous = queryClient.getQueryData(['activity']);

    // Optimistically update
    queryClient.setQueryData(['activity'], (old) => ({
      ...old,
      items: old.items.map(item =>
        item.id === newActivity.id ? newActivity : item
      ),
    }));

    return { previous };
  },
  onError: (err, variables, context) => {
    // Rollback on error
    queryClient.setQueryData(['activity'], context.previous);
  },
});
```

### Pagination

```typescript
export function useActivity(page: number, pageSize: number) {
  return useQuery({
    queryKey: ['activity', page],
    queryFn: () => getActivity(pageSize, page * pageSize),
    keepPreviousData: true, // Smooth pagination
  });
}
```

### Infinite Scroll

```typescript
import { useInfiniteQuery } from '@tanstack/react-query';

export function useInfiniteActivity() {
  return useInfiniteQuery({
    queryKey: ['activity'],
    queryFn: ({ pageParam = 0 }) => getActivity(10, pageParam),
    getNextPageParam: (lastPage, pages) => {
      if (lastPage.items.length < 10) return undefined;
      return pages.length * 10;
    },
  });
}
```

## Error Handling Best Practices

```typescript
// lib/api/client.ts
export class ApiError extends Error {
  constructor(
    public status: number,
    message: string,
    public code?: string
  ) {
    super(message);
    this.name = 'ApiError';
  }

  static isAuthError(error: unknown): error is ApiError {
    return error instanceof ApiError && error.status === 401;
  }

  static isNotFoundError(error: unknown): error is ApiError {
    return error instanceof ApiError && error.status === 404;
  }
}

// In component
if (error) {
  if (ApiError.isAuthError(error)) {
    // Redirect to login
    router.push('/login');
  } else if (ApiError.isNotFoundError(error)) {
    // Show 404 page
    return <NotFound />;
  } else {
    // Show generic error
    return <ErrorState error={error} />;
  }
}
```

## Testing API Integration

```typescript
// __tests__/api/client.test.ts
import { getMetrics } from '@/lib/api/client';

global.fetch = jest.fn();

describe('API Client', () => {
  beforeEach(() => {
    (fetch as jest.Mock).mockClear();
  });

  it('fetches metrics successfully', async () => {
    const mockData = { revenue: 45000, users: 1234 };
    
    (fetch as jest.Mock).mockResolvedValueOnce({
      ok: true,
      json: async () => mockData,
    });

    const data = await getMetrics();
    
    expect(data).toEqual(mockData);
    expect(fetch).toHaveBeenCalledWith(
      expect.stringContaining('/api/metrics'),
      expect.any(Object)
    );
  });

  it('handles errors correctly', async () => {
    (fetch as jest.Mock).mockResolvedValueOnce({
      ok: false,
      status: 500,
      json: async () => ({ error: 'Server error' }),
    });

    await expect(getMetrics()).rejects.toThrow('Server error');
  });
});
```

## Output Structure

```
lib/
├── api/
│   ├── client.ts       # API functions
│   └── types.ts        # TypeScript types
├── auth.ts             # Auth helpers (if needed)
└── hooks/              # Custom hooks (if needed)
    └── use-activity.ts

app/
├── providers.tsx       # React Query provider
└── [route]/
    ├── page.tsx        # Connected page
    ├── loading.tsx     # Loading state
    └── error.tsx       # Error boundary
```

## Checklist

After connecting APIs:

```markdown
- [ ] Types generated from API spec
- [ ] API client functions created
- [ ] Loading states implemented
- [ ] Error handling implemented
- [ ] Authentication configured (if needed)
- [ ] React Query setup (if client component)
- [ ] TypeScript compiles with no errors
- [ ] Data displays correctly in browser
- [ ] Error scenarios tested (network failure, 404, 401)
```

## Common Issues

**CORS errors:**
```typescript
// Backend needs to allow frontend origin
// Or use Next.js API routes as proxy
```

**Type mismatches:**
```bash
# Regenerate types from updated API spec
# Update components to match new types
```

**Stale data:**
```typescript
// Configure refetch intervals
refetchInterval: 30000, // 30 seconds

// Or manual refetch
queryClient.invalidateQueries({ queryKey: ['metrics'] });
```

## Notes

- Prefer server components when possible (better performance)
- Use client components for interactivity
- Handle all error states explicitly
- Type everything - no `any` types
- Test error scenarios, not just happy path