# Frontend Performance Patterns

## Core Web Vitals

| Metric | Target | What It Measures |
|--------|--------|------------------|
| **LCP** (Largest Contentful Paint) | < 2.5s | Loading performance |
| **INP** (Interaction to Next Paint) | < 200ms | Interactivity |
| **CLS** (Cumulative Layout Shift) | < 0.1 | Visual stability |

## Image Optimization

### Next.js Image Component

```tsx
import Image from 'next/image';

// ✅ Local images (automatic optimization)
import productImage from './product.jpg';

export function ProductCard() {
  return (
    <Image
      src={productImage}
      alt="Product"
      placeholder="blur"  // Automatic blur placeholder
      priority={false}    // Lazy load by default
    />
  );
}

// ✅ Remote images
export function UserAvatar({ user }: { user: User }) {
  return (
    <Image
      src={user.avatarUrl}
      alt={user.name}
      width={48}
      height={48}
      className="rounded-full"
    />
  );
}

// ✅ Fill container (responsive)
export function HeroImage() {
  return (
    <div className="relative h-[400px] w-full">
      <Image
        src="/hero.jpg"
        alt="Hero"
        fill
        sizes="100vw"
        className="object-cover"
        priority  // Above the fold - load immediately
      />
    </div>
  );
}
```

### Configure Remote Patterns

```ts
// next.config.ts
const nextConfig = {
  images: {
    remotePatterns: [
      {
        protocol: 'https',
        hostname: 'cdn.shopify.com',
      },
      {
        protocol: 'https',
        hostname: '*.cloudinary.com',
      },
    ],
  },
};
```

### Sizes Attribute

```tsx
// Tell browser what size image to fetch
<Image
  src="/product.jpg"
  alt="Product"
  fill
  sizes="
    (max-width: 640px) 100vw,
    (max-width: 1024px) 50vw,
    33vw
  "
/>
```

### Prevent CLS

```tsx
// ❌ BAD: No dimensions causes layout shift
<img src="/product.jpg" alt="Product" />

// ✅ GOOD: Explicit dimensions
<Image src="/product.jpg" alt="Product" width={400} height={300} />

// ✅ GOOD: Aspect ratio container
<div className="aspect-video relative">
  <Image src="/video-thumb.jpg" alt="Video" fill />
</div>
```

## Code Splitting

### Dynamic Imports

```tsx
import dynamic from 'next/dynamic';

// ❌ BAD: Heavy component loaded immediately
import HeavyChart from '@/components/HeavyChart';

// ✅ GOOD: Load only when needed
const HeavyChart = dynamic(() => import('@/components/HeavyChart'), {
  loading: () => <ChartSkeleton />,
  ssr: false,  // Client-only component
});

// ✅ Named exports
const Modal = dynamic(
  () => import('@/components/modals').then(mod => mod.ConfirmModal)
);
```

### Conditional Loading

```tsx
"use client";
import dynamic from 'next/dynamic';
import { useState } from 'react';

const Editor = dynamic(() => import('@/components/RichTextEditor'), {
  loading: () => <p>Loading editor...</p>,
});

export function PostForm() {
  const [showEditor, setShowEditor] = useState(false);
  
  return (
    <div>
      <button onClick={() => setShowEditor(true)}>
        Write Post
      </button>
      {showEditor && <Editor />}  {/* Only loads when clicked */}
    </div>
  );
}
```

### Route-Based Splitting

Next.js automatically code-splits by route. Keep routes focused:

```
app/
├─ (marketing)/     # Marketing bundle
├─ (dashboard)/     # Dashboard bundle  
└─ (auth)/          # Auth bundle
```

## Lazy Loading

### Below-the-Fold Content

```tsx
"use client";
import { useInView } from 'react-intersection-observer';
import dynamic from 'next/dynamic';

const Comments = dynamic(() => import('./Comments'));

export function Article({ article }: { article: Article }) {
  const { ref, inView } = useInView({
    triggerOnce: true,
    rootMargin: '200px',  // Start loading 200px before visible
  });
  
  return (
    <article>
      <h1>{article.title}</h1>
      <p>{article.content}</p>
      
      <div ref={ref}>
        {inView && <Comments articleId={article.id} />}
      </div>
    </article>
  );
}
```

### Infinite Scroll

```tsx
"use client";
import { useInView } from 'react-intersection-observer';
import { useEffect } from 'react';

export function ProductGrid({ 
  initialProducts,
  loadMore,
}: { 
  initialProducts: Product[];
  loadMore: () => Promise<Product[]>;
}) {
  const [products, setProducts] = useState(initialProducts);
  const [loading, setLoading] = useState(false);
  const { ref, inView } = useInView();
  
  useEffect(() => {
    if (inView && !loading) {
      setLoading(true);
      loadMore().then(newProducts => {
        setProducts(prev => [...prev, ...newProducts]);
        setLoading(false);
      });
    }
  }, [inView]);
  
  return (
    <>
      <div className="grid grid-cols-3 gap-4">
        {products.map(product => (
          <ProductCard key={product.id} product={product} />
        ))}
      </div>
      <div ref={ref}>
        {loading && <Spinner />}
      </div>
    </>
  );
}
```

## Font Optimization

### Next.js Font

```tsx
// app/layout.tsx
import { Inter, Roboto_Mono } from 'next/font/google';

const inter = Inter({
  subsets: ['latin'],
  display: 'swap',
  variable: '--font-inter',
});

const robotoMono = Roboto_Mono({
  subsets: ['latin'],
  display: 'swap',
  variable: '--font-roboto-mono',
});

export default function RootLayout({ children }: { children: React.ReactNode }) {
  return (
    <html lang="en" className={`${inter.variable} ${robotoMono.variable}`}>
      <body className="font-sans">{children}</body>
    </html>
  );
}
```

```css
/* tailwind.config.ts */
theme: {
  fontFamily: {
    sans: ['var(--font-inter)', 'system-ui', 'sans-serif'],
    mono: ['var(--font-roboto-mono)', 'monospace'],
  },
}
```

### Local Fonts

```tsx
import localFont from 'next/font/local';

const customFont = localFont({
  src: [
    { path: './fonts/Custom-Regular.woff2', weight: '400' },
    { path: './fonts/Custom-Bold.woff2', weight: '700' },
  ],
  display: 'swap',
});
```

## Bundle Analysis

### Setup

```bash
npm install @next/bundle-analyzer
```

```ts
// next.config.ts
import bundleAnalyzer from '@next/bundle-analyzer';

const withBundleAnalyzer = bundleAnalyzer({
  enabled: process.env.ANALYZE === 'true',
});

export default withBundleAnalyzer(nextConfig);
```

```bash
ANALYZE=true npm run build
```

### Common Issues

| Issue | Solution |
|-------|----------|
| Large moment.js | Use date-fns or dayjs |
| Full lodash import | Import specific functions: `lodash/debounce` |
| Unused dependencies | Remove or dynamically import |
| Large icons library | Import individual icons |

```tsx
// ❌ BAD: Imports entire library
import { debounce } from 'lodash';
import { FaHome } from 'react-icons/fa';

// ✅ GOOD: Tree-shakeable
import debounce from 'lodash/debounce';
import { Home } from 'lucide-react';
```

## Prefetching

### Link Prefetching

```tsx
import Link from 'next/link';

// ✅ Prefetches by default (in viewport)
<Link href="/products">Products</Link>

// Disable for low-priority links
<Link href="/terms" prefetch={false}>Terms</Link>
```

### Programmatic Prefetching

```tsx
"use client";
import { useRouter } from 'next/navigation';

export function ProductCard({ product }: { product: Product }) {
  const router = useRouter();
  
  return (
    <div
      onMouseEnter={() => router.prefetch(`/products/${product.id}`)}
      onClick={() => router.push(`/products/${product.id}`)}
    >
      {product.title}
    </div>
  );
}
```

## Caching Strategies

### Static Generation

```tsx
// Fully static page
export default async function AboutPage() {
  return <div>About Us</div>;
}

// Static with revalidation (ISR)
export const revalidate = 3600;  // Revalidate every hour

export default async function ProductsPage() {
  const products = await getProducts();
  return <ProductGrid products={products} />;
}
```

### Static Params

```tsx
// Generate all product pages at build time
export async function generateStaticParams() {
  const products = await getProducts();
  return products.map(product => ({ id: product.id }));
}

export default async function ProductPage({ params }: { params: { id: string } }) {
  const product = await getProduct(params.id);
  return <ProductDetails product={product} />;
}
```

## Monitoring

### Web Vitals Reporting

```tsx
// app/layout.tsx
import { SpeedInsights } from '@vercel/speed-insights/next';

export default function RootLayout({ children }: { children: React.ReactNode }) {
  return (
    <html>
      <body>
        {children}
        <SpeedInsights />
      </body>
    </html>
  );
}
```

### Custom Reporting

```tsx
// app/components/WebVitals.tsx
"use client";
import { useReportWebVitals } from 'next/web-vitals';

export function WebVitals() {
  useReportWebVitals(metric => {
    // Send to analytics
    console.log(metric);
    
    // Example: Send to custom endpoint
    fetch('/api/vitals', {
      method: 'POST',
      body: JSON.stringify(metric),
    });
  });
  
  return null;
}
```

## Performance Checklist

### Images
- [ ] Use `next/image` for all images
- [ ] Set explicit `width`/`height` or use `fill` with container
- [ ] Add `priority` to above-the-fold images
- [ ] Configure proper `sizes` for responsive images
- [ ] Use WebP/AVIF formats (automatic with next/image)

### JavaScript
- [ ] Dynamic import heavy components
- [ ] Lazy load below-the-fold content
- [ ] Avoid importing entire libraries
- [ ] Use route groups for bundle splitting
- [ ] Analyze bundle size regularly

### Fonts
- [ ] Use `next/font` for automatic optimization
- [ ] Set `display: 'swap'` for FOUT prevention
- [ ] Subset fonts to needed characters
- [ ] Preload critical fonts

### Data
- [ ] Fetch data in Server Components
- [ ] Use parallel fetching with `Promise.all`
- [ ] Implement proper caching strategies
- [ ] Stream slow data with Suspense

### General
- [ ] Enable gzip/brotli compression
- [ ] Use CDN for static assets
- [ ] Monitor Core Web Vitals in production
- [ ] Test on slow connections (Chrome DevTools)