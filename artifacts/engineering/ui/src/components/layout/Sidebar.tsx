'use client';

import Link from 'next/link';
import { usePathname } from 'next/navigation';
import {
  LayoutDashboard,
  Target,
  Grid3X3,
  GitBranch,
  Zap,
  FolderOpen,
  BookOpen,
  Search,
} from 'lucide-react';
import { cx } from '@/lib/utils/cx';

const navItems = [
  { href: '/', label: 'Dashboard', icon: LayoutDashboard },
  { href: '/goals', label: 'Goals', icon: Target },
  { href: '/canvas', label: 'Canvas', icon: Grid3X3 },
  { href: '/threads', label: 'Threads', icon: GitBranch },
  { href: '/skills', label: 'Skills', icon: Zap },
  { href: '/artifacts', label: 'Artifacts', icon: FolderOpen },
  { href: '/research', label: 'Research', icon: BookOpen },
];

export function Sidebar() {
  const pathname = usePathname();

  return (
    <aside className="w-56 border-r border-secondary bg-bg-primary flex flex-col">
      {/* Logo Section */}
      <div className="p-4">
        <Link href="/" className="flex items-center gap-3">
          <div className="w-8 h-8 rounded-md bg-fg-brand-primary flex items-center justify-center shadow-xs">
            <span className="text-white font-bold text-sm">L</span>
          </div>
          <span className="font-semibold text-lg text-primary">LeanOS</span>
        </Link>
      </div>

      {/* Search */}
      <div className="px-3 pb-3">
        <div className="relative">
          <Search className="absolute left-3 top-1/2 -translate-y-1/2 w-4 h-4 text-quaternary" />
          <input
            type="text"
            placeholder="Search"
            className="w-full h-9 pl-9 pr-3 rounded-md border border-primary bg-bg-primary text-sm text-primary placeholder:text-placeholder focus:outline-none focus:ring-1 focus:ring-brand-primary"
          />
        </div>
      </div>

      {/* Navigation */}
      <nav className="flex-1 px-3">
        <ul className="space-y-0.5">
          {navItems.map((item) => {
            const Icon = item.icon;
            const isActive = pathname === item.href ||
              (item.href !== '/' && pathname.startsWith(item.href));

            return (
              <li key={item.href}>
                <Link
                  href={item.href}
                  className={cx(
                    'flex items-center gap-3 px-3 py-2 rounded-md text-sm font-medium transition-all',
                    isActive
                      ? 'bg-active text-primary'
                      : 'text-tertiary hover:bg-bg-primary_hover hover:text-secondary'
                  )}
                >
                  <Icon className="w-5 h-5" />
                  {item.label}
                </Link>
              </li>
            );
          })}
        </ul>
      </nav>

      {/* Footer */}
      <div className="p-4 border-t border-secondary">
        <p className="text-xs text-quaternary">
          LeanOS UI v1.0
        </p>
      </div>
    </aside>
  );
}
