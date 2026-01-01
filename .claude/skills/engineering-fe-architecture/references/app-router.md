# Next.js App Router Patterns

## Server vs Client Components

### Decision Tree

```
Does component need...
│
├─ Browser APIs (window, localStorage, navigator)?
│   └─ "use client"
│
├─ Event handlers (onClick, onChange, onSubmit)?
│   └─ "use client"
│
├─ React hooks (useState, useEffect, useContext)?
│   └─ "use client"
│
├─ Only data fetching + rendering?
│   └─ Server Component (default)
│
└─ Third-party library without RSC support?
    └─ "use client" wrapper
```

### Component Boundaries

```tsx
// ❌ BAD: Entire page is client
"use client";
export default function ProductPage({ params }: { params: { id: string } }) {
  const [product, setProduct] = useState(null);
  useEffect(() => { fetchProduct(params.id).then(setProduct); }, []);
  return <ProductDetails product={product} />;
}

// ✅ GOOD: Server component with client islands
// app/products/[id]/page.tsx (Server Component - no directive)
export default async function ProductPage({ params }: { params: { id: string } }) {
  const product = await getProduct(params.id);  // Direct DB/API call
  
  return (
    <div>
      <ProductHeader product={product} />           {/* Server */}
      <ProductGallery images={product.images} />    {/* Server */}
      <AddToCartButton productId={product.id} />    {/* Client */}
      <ProductReviews productId={product.id} />     {/* Server + streaming */}
    </div>
  );
}

// components/AddToCartButton.tsx
"use client";
export function AddToCartButton({ productId }: { productId: string }) {
  const [pending, setPending] = useState(false);
  // Interactive logic here
}
```

### Composition Pattern

Pass Server Components as children to Client Components:

```tsx
// ClientWrapper.tsx
"use client";
export function ClientWrapper({ children }: { children: React.ReactNode }) {
  const [isOpen, setIsOpen] = useState(false);
  return (
    <Dialog open={isOpen} onOpenChange={setIsOpen}>
      {children}  {/* Server Component content */}
    </Dialog>
  );
}

// page.tsx (Server)
export default async function Page() {
  const data = await fetchData();  // Server-side fetch
  return (
    <ClientWrapper>
      <ServerContent data={data} />  {/* Stays on server */}
    </ClientWrapper>
  );
}
```

## Data Fetching

### Fetching Locations

| Location | Use Case | Caching |
|----------|----------|---------|
| Server Component | Initial page data | Configurable |
| Route Handler | API endpoints, webhooks | Manual |
| Server Action | Mutations from forms | None |
| Client (SWR/Query) | Real-time, user-specific | Client-side |

### Server Component Fetch

```tsx
// Automatic request deduplication
async function ProductPage({ params }: { params: { id: string } }) {
  // These are deduped if same URL + options
  const product = await fetch(`/api/products/${params.id}`);
  const reviews = await fetch(`/api/products/${params.id}/reviews`);
  
  return <div>...</div>;
}
```

### Parallel Data Fetching

```tsx
// ❌ SLOW: Sequential (waterfall)
async function Page() {
  const user = await getUser();
  const posts = await getPosts();  // Waits for user
  const comments = await getComments();  // Waits for posts
}

// ✅ FAST: Parallel
async function Page() {
  const [user, posts, comments] = await Promise.all([
    getUser(),
    getPosts(),
    getComments(),
  ]);
}

// ✅ BEST: Parallel with streaming (show content as it loads)
async function Page() {
  const userPromise = getUser();
  const postsPromise = getPosts();
  
  return (
    <div>
      <Suspense fallback={<UserSkeleton />}>
        <UserSection userPromise={userPromise} />
      </Suspense>
      <Suspense fallback={<PostsSkeleton />}>
        <PostsSection postsPromise={postsPromise} />
      </Suspense>
    </div>
  );
}

// Component that awaits the promise
async function UserSection({ userPromise }: { userPromise: Promise<User> }) {
  const user = await userPromise;
  return <UserCard user={user} />;
}
```

## Streaming & Suspense

### Loading States

```tsx
// app/dashboard/loading.tsx - Automatic loading UI
export default function Loading() {
  return <DashboardSkeleton />;
}

// Or granular with Suspense
export default async function Dashboard() {
  return (
    <div>
      <h1>Dashboard</h1>
      
      {/* Shows immediately */}
      <QuickStats />
      
      {/* Streams in when ready */}
      <Suspense fallback={<ChartSkeleton />}>
        <SlowAnalyticsChart />
      </Suspense>
      
      <Suspense fallback={<TableSkeleton />}>
        <SlowDataTable />
      </Suspense>
    </div>
  );
}
```

### Nested Suspense

```tsx
// Progressively reveal UI
<Suspense fallback={<PageSkeleton />}>
  <Header />
  <Suspense fallback={<SidebarSkeleton />}>
    <Sidebar />
  </Suspense>
  <main>
    <Suspense fallback={<ContentSkeleton />}>
      <Content />
    </Suspense>
  </main>
</Suspense>
```

## Caching & Revalidation

### Fetch Cache Options

```tsx
// Default: cached indefinitely (static)
fetch('/api/data');

// Revalidate every 60 seconds
fetch('/api/data', { next: { revalidate: 60 } });

// Never cache (dynamic)
fetch('/api/data', { cache: 'no-store' });

// Cache with tags for on-demand revalidation
fetch('/api/products', { next: { tags: ['products'] } });
```

### Route Segment Config

```tsx
// app/dashboard/page.tsx

// Force dynamic rendering
export const dynamic = 'force-dynamic';

// Or force static
export const dynamic = 'force-static';

// Revalidate entire route
export const revalidate = 60;  // seconds
```

### On-Demand Revalidation

```tsx
// app/api/revalidate/route.ts
import { revalidateTag, revalidatePath } from 'next/cache';

export async function POST(request: Request) {
  const { tag, path } = await request.json();
  
  if (tag) {
    revalidateTag(tag);  // Revalidate all fetches with this tag
  }
  
  if (path) {
    revalidatePath(path);  // Revalidate specific path
  }
  
  return Response.json({ revalidated: true });
}

// Usage after mutation
async function updateProduct(id: string, data: ProductData) {
  await db.product.update({ where: { id }, data });
  revalidateTag('products');
  revalidatePath(`/products/${id}`);
}
```

## Server Actions

### Form Mutations

```tsx
// app/products/[id]/page.tsx
import { revalidatePath } from 'next/cache';

async function updateProduct(formData: FormData) {
  "use server";
  
  const id = formData.get('id') as string;
  const title = formData.get('title') as string;
  
  await db.product.update({
    where: { id },
    data: { title },
  });
  
  revalidatePath(`/products/${id}`);
}

export default function ProductPage({ product }: { product: Product }) {
  return (
    <form action={updateProduct}>
      <input type="hidden" name="id" value={product.id} />
      <input name="title" defaultValue={product.title} />
      <button type="submit">Save</button>
    </form>
  );
}
```

### With useActionState (React 19)

```tsx
"use client";
import { useActionState } from 'react';
import { updateProduct } from './actions';

export function ProductForm({ product }: { product: Product }) {
  const [state, action, pending] = useActionState(updateProduct, null);
  
  return (
    <form action={action}>
      <input name="title" defaultValue={product.title} />
      {state?.error && <p className="error">{state.error}</p>}
      <button disabled={pending}>
        {pending ? 'Saving...' : 'Save'}
      </button>
    </form>
  );
}
```

### Optimistic Updates

```tsx
"use client";
import { useOptimistic } from 'react';

export function TodoList({ todos }: { todos: Todo[] }) {
  const [optimisticTodos, addOptimisticTodo] = useOptimistic(
    todos,
    (state, newTodo: Todo) => [...state, newTodo]
  );
  
  async function addTodo(formData: FormData) {
    const title = formData.get('title') as string;
    
    // Optimistically add
    addOptimisticTodo({ id: 'temp', title, completed: false });
    
    // Actually create
    await createTodo(title);
  }
  
  return (
    <form action={addTodo}>
      <input name="title" />
      <ul>
        {optimisticTodos.map(todo => (
          <li key={todo.id}>{todo.title}</li>
        ))}
      </ul>
    </form>
  );
}
```

## Route Patterns

### Parallel Routes

```
app/
├─ @modal/
│   ├─ default.tsx        # Fallback when no modal
│   └─ (.)products/[id]/
│       └─ page.tsx       # Intercepted modal
├─ layout.tsx
└─ page.tsx
```

```tsx
// app/layout.tsx
export default function Layout({
  children,
  modal,
}: {
  children: React.ReactNode;
  modal: React.ReactNode;
}) {
  return (
    <html>
      <body>
        {children}
        {modal}
      </body>
    </html>
  );
}
```

### Intercepting Routes

| Convention | Intercepts |
|------------|------------|
| `(.)` | Same level |
| `(..)` | One level up |
| `(..)(..)` | Two levels up |
| `(...)` | From root |

```tsx
// app/@modal/(.)products/[id]/page.tsx
// Intercepts /products/[id] and shows as modal

export default function ProductModal({ params }: { params: { id: string } }) {
  return (
    <Dialog>
      <ProductDetails id={params.id} />
    </Dialog>
  );
}
```

### Route Groups

```
app/
├─ (marketing)/
│   ├─ layout.tsx         # Marketing layout
│   ├─ page.tsx           # /
│   └─ about/page.tsx     # /about
├─ (shop)/
│   ├─ layout.tsx         # Shop layout
│   └─ products/page.tsx  # /products
└─ (auth)/
    ├─ layout.tsx         # Auth layout
    └─ login/page.tsx     # /login
```

## Error Handling

### Error Boundaries

```tsx
// app/dashboard/error.tsx
"use client";

export default function Error({
  error,
  reset,
}: {
  error: Error & { digest?: string };
  reset: () => void;
}) {
  return (
    <div>
      <h2>Something went wrong!</h2>
      <p>{error.message}</p>
      <button onClick={() => reset()}>Try again</button>
    </div>
  );
}
```

### Not Found

```tsx
// app/products/[id]/page.tsx
import { notFound } from 'next/navigation';

export default async function ProductPage({ params }: { params: { id: string } }) {
  const product = await getProduct(params.id);
  
  if (!product) {
    notFound();  // Shows not-found.tsx
  }
  
  return <ProductDetails product={product} />;
}

// app/products/[id]/not-found.tsx
export default function NotFound() {
  return <div>Product not found</div>;
}
```

## Metadata

### Static Metadata

```tsx
// app/products/page.tsx
import type { Metadata } from 'next';

export const metadata: Metadata = {
  title: 'Products',
  description: 'Browse our products',
};
```

### Dynamic Metadata

```tsx
// app/products/[id]/page.tsx
import type { Metadata } from 'next';

export async function generateMetadata({ 
  params 
}: { 
  params: { id: string } 
}): Promise<Metadata> {
  const product = await getProduct(params.id);
  
  return {
    title: product.title,
    description: product.description,
    openGraph: {
      images: [product.image],
    },
  };
}
```