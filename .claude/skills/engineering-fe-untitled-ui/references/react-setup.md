# React Setup Reference

Essential setup for Untitled UI + Next.js.

## Option 1: Official Starter Kit (Recommended)

```bash
git clone https://github.com/untitleduico/untitledui-nextjs-starter-kit.git my-app
cd my-app
npm install
npm run dev
```

Already configured:
- Next.js 15 + React 19.1
- Tailwind CSS 4.1
- TypeScript 5.8
- React Aria components
- `theme.css` with all design tokens
- `cx()` utility
- ThemeProvider (next-themes)
- Folder structure: `src/components/`, `src/lib/`, `src/styles/`

## Option 2: CLI Init

```bash
npx untitledui@latest init --nextjs
```

## Option 3: Manual Setup

```bash
npm install @untitledui/icons react-aria-components tailwindcss-react-aria-components tailwind-merge tailwindcss-animate next-themes
```

## globals.css

```css
@import "tailwindcss";
@import "./theme.css";
```

## lib/utils.ts

```ts
import { twMerge } from "tailwind-merge";

export function cx(...classes: (string | undefined | null | false)[]) {
  return twMerge(classes.filter(Boolean).join(" "));
}
```

## ThemeProvider (layout.tsx)

```tsx
import { ThemeProvider } from "next-themes";

export default function RootLayout({ children }: { children: React.ReactNode }) {
  return (
    <html lang="en" suppressHydrationWarning>
      <body>
        <ThemeProvider
          attribute="class"
          defaultTheme="system"
          classNames={{ light: "light-mode", dark: "dark-mode" }}
        >
          {children}
        </ThemeProvider>
      </body>
    </html>
  );
}
```

## Theme Toggle

```tsx
"use client";
import { useTheme } from "next-themes";
import { Moon01, Sun } from "@untitledui/icons";

export function ThemeToggle() {
  const { theme, setTheme } = useTheme();
  return (
    <button onClick={() => setTheme(theme === "dark" ? "light" : "dark")}>
      {theme === "dark" ? <Sun className="size-5" /> : <Moon01 className="size-5" />}
    </button>
  );
}
```

## Icons

```tsx
import { Home01, Settings01, ChevronRight } from "@untitledui/icons";

<Home01 className="size-5" />
<Settings01 className="size-5 text-fg-quinary" />
<ChevronRight className="size-4" strokeWidth={2} aria-hidden="true" />
```

## Server vs Client Components

```tsx
// Server: Static, data fetching
// Client: Interactive, hooks, React Aria

"use client"; // Required for:
// - onClick, onChange handlers
// - useState, useEffect
// - React Aria components
// - next-themes useTheme
```

## Project Structure (Starter Kit)

```
src/
├── app/
│   ├── layout.tsx          # ThemeProvider
│   ├── globals.css         # Tailwind + theme import
│   └── page.tsx
├── components/
│   ├── base/               # npx untitledui add -t base
│   ├── application/        # npx untitledui add -t application
│   └── marketing/          # npx untitledui add -t marketing
├── lib/
│   └── utils.ts            # cx() helper
└── styles/
    └── theme.css           # Design tokens (auto-generated)
```