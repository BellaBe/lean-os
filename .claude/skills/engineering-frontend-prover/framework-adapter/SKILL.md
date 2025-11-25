---
name: framework-adapter
description: Generate framework-specific API client and bindings ({Platform} Remix, React, Vue, vanilla). Uses TypeScript types from typescript-generator. Handles authentication, state management, error handling. Sub-skill of frontend-prover.
version: 1.0.0
allowed-tools: bash_tool, create_file
model: claude-sonnet-4-20250514
license: Proprietary - LeanOS Engineering Layer
---

# framework-adapter: Types → Framework Bindings

## Purpose

Generate framework-specific API client and bindings using TypeScript types.

**Input:**
- TypeScript types (from typescript-generator)
- Framework choice ({platform}-remix, react, vue, vanilla)
- OpenAPI AST (for endpoint details)

**Output:** Framework-specific client + bindings

---

## Supported Frameworks

1. **{Platform} Remix** - Loaders, actions, {Platform} App Bridge
2. **React** - Hooks, context, custom hooks
3. **Vue** - Composition API, composables, stores
4. **Vanilla** - Pure fetch API, no framework

---

## Common Layer: API Client

**All frameworks share base API client:**

```typescript
// artifacts/engineering/code/frontend/client/api-client.ts

/**
 * Base API client (framework-agnostic)
 * 
 * Handles:
 * - HTTP requests
 * - Authentication
 * - Error handling
 * - Request/response transformation
 */

import type {
  Entity,
  EntityList,
  GetEntitiesRequest,
  GetEntitiesResponse,
  CreateEntityRequest,
  CreateEntityResponse,
  ApiError
} from '../types/api';

export class ApiClient {
  private baseUrl: string;
  private authToken?: string;
  
  constructor(config: { baseUrl: string; authToken?: string }) {
    this.baseUrl = config.baseUrl;
    this.authToken = config.authToken;
  }
  
  /**
   * Set authentication token
   */
  setAuthToken(token: string) {
    this.authToken = token;
  }
  
  /**
   * Make authenticated request
   */
  private async request<T>(
    method: string,
    path: string,
    body?: unknown
  ): Promise<T> {
    const headers: Record<string, string> = {
      'Content-Type': 'application/json'
    };
    
    if (this.authToken) {
      headers['Authorization'] = `Bearer ${this.authToken}`;
    }
    
    const response = await fetch(`${this.baseUrl}${path}`, {
      method,
      headers,
      body: body ? JSON.stringify(body) : undefined
    });
    
    if (!response.ok) {
      const error: ApiError = await response.json();
      throw new ApiClientError(error);
    }
    
    return response.json();
  }
  
  // ========================================================================
  // Entities API
  // ========================================================================

  async getEntities(params?: GetEntitiesRequest): Promise<GetEntitiesResponse> {
    const query = params ? `?${new URLSearchParams(params as any)}` : '';
    return this.request<GetEntitiesResponse>('GET', `/entities${query}`);
  }

  async createEntity(data: CreateEntityRequest): Promise<CreateEntityResponse> {
    return this.request<CreateEntityResponse>('POST', '/entities', data);
  }

  async getEntityById(id: string): Promise<Entity> {
    return this.request<Entity>('GET', `/entities/${id}`);
  }

  async updateEntity(id: string, data: Partial<CreateEntityRequest>): Promise<Entity> {
    return this.request<Entity>('PUT', `/entities/${id}`, data);
  }

  async deleteEntity(id: string): Promise<void> {
    await this.request<void>('DELETE', `/entities/${id}`);
  }
}

export class ApiClientError extends Error {
  public error: ApiError;
  
  constructor(error: ApiError) {
    super(error.error);
    this.error = error;
    this.name = 'ApiClientError';
  }
}
```

---

## Framework 1: {Platform} Remix

**Output:** Loaders, actions, {Platform} App Bridge integration

```typescript
// artifacts/engineering/code/frontend/framework/{platform}-remix/entities.tsx

import { json, type LoaderFunctionArgs, type ActionFunctionArgs } from "@remix-run/node";
import { useLoaderData, useSubmit, useActionData } from "@remix-run/react";
import { authenticate } from "../{platform}.server";
import { ApiClient } from "../../client/api-client";
import type { EntityList, Entity, CreateEntityRequest } from "../../types/api";

/**
 * Loader: Fetch entities list
 */
export async function loader({ request }: LoaderFunctionArgs) {
  const { session } = await authenticate.admin(request);

  const client = new ApiClient({
    baseUrl: process.env.API_BASE_URL!,
    authToken: session.accessToken
  });

  const url = new URL(request.url);
  const page = url.searchParams.get('page');
  const limit = url.searchParams.get('limit');

  const entities = await client.getEntities({
    page: page ? parseInt(page) : undefined,
    limit: limit ? parseInt(limit) : undefined
  });

  return json({ entities });
}

/**
 * Action: Create or update entity
 */
export async function action({ request }: ActionFunctionArgs) {
  const { session } = await authenticate.admin(request);

  const client = new ApiClient({
    baseUrl: process.env.API_BASE_URL!,
    authToken: session.accessToken
  });

  const formData = await request.formData();
  const intent = formData.get('intent');

  if (intent === 'create') {
    const data: CreateEntityRequest = {
      name: formData.get('name') as string,
      value: parseFloat(formData.get('value') as string),
      status: formData.get('status') as any
    };

    const entity = await client.createEntity(data);
    return json({ success: true, entity });
  }

  if (intent === 'delete') {
    const id = formData.get('id') as string;
    await client.deleteEntity(id);
    return json({ success: true });
  }

  return json({ success: false, error: 'Unknown intent' });
}

/**
 * Component: Entities page
 */
export default function Entities() {
  const { entities } = useLoaderData<typeof loader>();
  const actionData = useActionData<typeof action>();
  const submit = useSubmit();

  return (
    <div>
      <h1>Entities</h1>

      {actionData?.success && (
        <div>Action successful!</div>
      )}

      <table>
        <thead>
          <tr>
            <th>Name</th>
            <th>Value</th>
            <th>Status</th>
            <th>Actions</th>
          </tr>
        </thead>
        <tbody>
          {entities.items.map((entity: Entity) => (
            <tr key={entity.id}>
              <td>{entity.name}</td>
              <td>${entity.value}</td>
              <td>{entity.status}</td>
              <td>
                <button
                  onClick={() => {
                    submit(
                      { intent: 'delete', id: entity.id },
                      { method: 'post' }
                    );
                  }}
                >
                  Delete
                </button>
              </td>
            </tr>
          ))}
        </tbody>
      </table>
    </div>
  );
}
```

---

## Framework 2: React

**Output:** Hooks, context, custom hooks

```typescript
// artifacts/engineering/code/frontend/framework/react/hooks/useEntities.ts

import { useState, useEffect } from 'react';
import { useApiClient } from '../context/ApiContext';
import type { Entity, EntityList, GetEntitiesRequest } from '../../../types/api';

/**
 * Hook for fetching entities list
 */
export function useEntities(params?: GetEntitiesRequest) {
  const client = useApiClient();
  const [data, setData] = useState<EntityList | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<Error | null>(null);

  useEffect(() => {
    async function fetchEntities() {
      try {
        setLoading(true);
        const entities = await client.getEntities(params);
        setData(entities);
        setError(null);
      } catch (err) {
        setError(err as Error);
      } finally {
        setLoading(false);
      }
    }

    fetchEntities();
  }, [client, params?.page, params?.limit]);

  return { data, loading, error };
}

/**
 * Hook for creating entity
 */
export function useCreateEntity() {
  const client = useApiClient();
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<Error | null>(null);

  const createEntity = async (data: CreateEntityRequest) => {
    try {
      setLoading(true);
      const entity = await client.createEntity(data);
      setError(null);
      return entity;
    } catch (err) {
      setError(err as Error);
      throw err;
    } finally {
      setLoading(false);
    }
  };

  return { createEntity, loading, error };
}

// artifacts/engineering/code/frontend/framework/react/context/ApiContext.tsx

import React, { createContext, useContext, useMemo } from 'react';
import { ApiClient } from '../../../client/api-client';

const ApiContext = createContext<ApiClient | null>(null);

export function ApiProvider({
  children,
  baseUrl,
  authToken
}: {
  children: React.ReactNode;
  baseUrl: string;
  authToken?: string;
}) {
  const client = useMemo(
    () => new ApiClient({ baseUrl, authToken }),
    [baseUrl, authToken]
  );
  
  return (
    <ApiContext.Provider value={client}>
      {children}
    </ApiContext.Provider>
  );
}

export function useApiClient() {
  const client = useContext(ApiContext);
  if (!client) {
    throw new Error('useApiClient must be used within ApiProvider');
  }
  return client;
}

// Usage example component
export function EntitiesPage() {
  const { data, loading, error } = useEntities({ page: 1, limit: 10 });
  const { createEntity, loading: creating } = useCreateEntity();

  if (loading) return <div>Loading...</div>;
  if (error) return <div>Error: {error.message}</div>;

  return (
    <div>
      <h1>Entities ({data?.total})</h1>
      <ul>
        {data?.items.map(entity => (
          <li key={entity.id}>
            {entity.name} - ${entity.value}
          </li>
        ))}
      </ul>
    </div>
  );
}
```

---

## Framework 3: Vue

**Output:** Composition API, composables, stores

```typescript
// artifacts/engineering/code/frontend/framework/vue/composables/useEntities.ts

import { ref, computed } from 'vue';
import { useApiClient } from './useApiClient';
import type { Entity, EntityList, GetEntitiesRequest } from '../../../types/api';

/**
 * Composable for entities list
 */
export function useEntities(params?: GetEntitiesRequest) {
  const client = useApiClient();
  const data = ref<EntityList | null>(null);
  const loading = ref(false);
  const error = ref<Error | null>(null);

  const entities = computed(() => data.value?.items || []);
  const total = computed(() => data.value?.total || 0);

  async function fetch() {
    try {
      loading.value = true;
      error.value = null;
      data.value = await client.getEntities(params);
    } catch (err) {
      error.value = err as Error;
    } finally {
      loading.value = false;
    }
  }

  async function createEntity(entityData: CreateEntityRequest) {
    try {
      loading.value = true;
      error.value = null;
      const entity = await client.createEntity(entityData);

      // Optimistic update
      if (data.value) {
        data.value.items.push(entity);
        data.value.total += 1;
      }

      return entity;
    } catch (err) {
      error.value = err as Error;
      throw err;
    } finally {
      loading.value = false;
    }
  }

  return {
    data,
    entities,
    total,
    loading,
    error,
    fetch,
    createEntity
  };
}

// artifacts/engineering/code/frontend/framework/vue/composables/useApiClient.ts

import { inject } from 'vue';
import type { ApiClient } from '../../../client/api-client';

const API_CLIENT_KEY = Symbol('apiClient');

export function provideApiClient(client: ApiClient) {
  provide(API_CLIENT_KEY, client);
}

export function useApiClient(): ApiClient {
  const client = inject<ApiClient>(API_CLIENT_KEY);
  if (!client) {
    throw new Error('API client not provided');
  }
  return client;
}
```

---

## Framework 4: Vanilla (Framework-free)

**Output:** Pure functions, no framework dependencies

```typescript
// artifacts/engineering/code/frontend/framework/vanilla/entities.ts

import { ApiClient } from '../../client/api-client';
import type { Entity, EntityList } from '../../types/api';

/**
 * Initialize API client
 */
export function initApiClient(baseUrl: string, authToken?: string) {
  return new ApiClient({ baseUrl, authToken });
}

/**
 * Fetch and render entities
 */
export async function fetchAndRenderEntities(
  client: ApiClient,
  container: HTMLElement,
  options?: { page?: number; limit?: number }
) {
  // Show loading
  container.innerHTML = '<div>Loading...</div>';

  try {
    // Fetch entities
    const entities = await client.getEntities(options);

    // Render entities
    container.innerHTML = `
      <h1>Entities (${entities.total})</h1>
      <ul>
        ${entities.items.map(entity => `
          <li data-entity-id="${entity.id}">
            <strong>${entity.name}</strong> - $${entity.value}
            <span class="status">${entity.status}</span>
          </li>
        `).join('')}
      </ul>
    `;
  } catch (error) {
    container.innerHTML = `<div class="error">Error: ${error.message}</div>`;
  }
}

/**
 * Create entity form handler
 */
export function setupCreateEntityForm(
  client: ApiClient,
  formElement: HTMLFormElement,
  onSuccess?: (entity: Entity) => void
) {
  formElement.addEventListener('submit', async (e) => {
    e.preventDefault();

    const formData = new FormData(formElement);

    try {
      const entity = await client.createEntity({
        name: formData.get('name') as string,
        value: parseFloat(formData.get('value') as string),
        status: formData.get('status') as any
      });

      formElement.reset();
      onSuccess?.(entity);
    } catch (error) {
      alert(`Error: ${error.message}`);
    }
  });
}

// Usage example
const client = initApiClient('http://localhost:8000', 'token');
const container = document.getElementById('entities-container')!;

fetchAndRenderEntities(client, container, { page: 1, limit: 10 });
```

---

## Output Structure

```
artifacts/engineering/code/frontend/
├── types/
│   └── api.ts                       # Framework-agnostic types
│
├── client/
│   └── api-client.ts                # Base HTTP client
│
└── framework/
    ├── {platform}-remix/
    │   ├── entities.tsx             # Loader + action + component
    │   ├── transactions.tsx
    │   └── auth.tsx
    │
    ├── react/
    │   ├── hooks/
    │   │   ├── useEntities.ts
    │   │   ├── useCreateEntity.ts
    │   │   └── useTransactions.ts
    │   └── context/
    │       └── ApiContext.tsx
    │
    ├── vue/
    │   ├── composables/
    │   │   ├── useEntities.ts
    │   │   ├── useTransactions.ts
    │   │   └── useApiClient.ts
    │   └── stores/
    │       └── api.ts
    │
    └── vanilla/
        ├── entities.ts
        ├── transactions.ts
        └── auth.ts
```

---

## Success Criteria

✓ API client generated (framework-agnostic)
✓ Framework bindings generated (framework-specific)
✓ Authentication handled
✓ Error handling included
✓ State management (if requested)
✓ Type-safe (uses TypeScript types)

---

## Key Insights

1. **API client is shared** - All frameworks use same HTTP layer
2. **Framework layer is thin** - Types do heavy lifting
3. **Type safety maintained** - All framework code uses TypeScript types
4. **Authentication abstracted** - Handled in API client
5. **Error handling consistent** - ApiClientError across frameworks

**Next:** type-correspondence-prover verifies types match OpenAPI schema
