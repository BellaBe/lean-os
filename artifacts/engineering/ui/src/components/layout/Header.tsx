'use client';

import { usePathname } from 'next/navigation';

interface HeaderProps {
  mode?: 'VENTURE' | 'BOOTSTRAP' | 'HYBRID';
}

const modeConfig = {
  VENTURE: {
    label: 'Venture Mode',
    className: 'bg-utility-blue-50 text-utility-blue-700'
  },
  BOOTSTRAP: {
    label: 'Bootstrap Mode',
    className: 'bg-utility-success-50 text-utility-success-700'
  },
  HYBRID: {
    label: 'Hybrid Mode',
    className: 'bg-utility-brand-50 text-utility-brand-700'
  },
};

export function Header({ mode = 'VENTURE' }: HeaderProps) {
  const pathname = usePathname();

  // Get page title from pathname
  const segments = pathname.split('/').filter(Boolean);
  const pageTitle = segments.length > 0
    ? segments[segments.length - 1].charAt(0).toUpperCase() + segments[segments.length - 1].slice(1)
    : 'Dashboard';

  const { label, className } = modeConfig[mode];

  return (
    <header className="h-14 bg-bg-primary flex items-center justify-between px-6 border-b border-border-secondary">
      {/* Page Title */}
      <h1 className="text-lg font-semibold text-text-primary">{pageTitle}</h1>

      {/* Mode Badge */}
      <span className={`inline-flex items-center px-2.5 py-1 text-xs font-medium rounded-full ${className}`}>
        {label}
      </span>
    </header>
  );
}
