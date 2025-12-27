"use client";

import { usePathname } from "next/navigation";
import Link from "next/link";
import { cx } from "@/utils/cx";
import { LeanOSLogo } from "./logo";
import { mainNavItems, footerNavItems } from "@/lib/navigation";
import type { NavItemType } from "@/components/application/app-navigation/config";
import { Badge } from "@/components/base/badges/badges";

interface SidebarProps {
  mode?: string;
}

function NavItem({ item, isActive }: { item: NavItemType; isActive: boolean }) {
  const Icon = item.icon;

  return (
    <Link
      href={item.href || "#"}
      className={cx(
        "flex items-center gap-3 px-3 py-2 rounded-md text-sm font-medium transition-colors",
        isActive
          ? "bg-brand-primary text-brand-primary"
          : "text-secondary hover:bg-primary_hover hover:text-primary"
      )}
    >
      {Icon && <Icon className="h-5 w-5 flex-shrink-0" />}
      <span>{item.label}</span>
      {item.badge}
    </Link>
  );
}

export function Sidebar({ mode = "BOOTSTRAP" }: SidebarProps) {
  const pathname = usePathname();

  return (
    <aside className="fixed inset-y-0 left-0 z-50 hidden w-64 flex-col border-r border-secondary bg-primary lg:flex">
      {/* Logo */}
      <div className="flex h-16 items-center gap-2 px-4 border-b border-secondary">
        <LeanOSLogo />
      </div>

      {/* Mode badge */}
      <div className="px-4 py-3">
        <Badge
          size="sm"
          color={mode === "VENTURE" ? "purple" : "blue"}
        >
          {mode} mode
        </Badge>
      </div>

      {/* Main nav */}
      <nav className="flex-1 overflow-y-auto px-3 py-2">
        <ul className="space-y-1">
          {mainNavItems.map((item) => (
            <li key={item.label}>
              <NavItem
                item={item}
                isActive={
                  item.href === "/"
                    ? pathname === "/"
                    : pathname.startsWith(item.href || "")
                }
              />
            </li>
          ))}
        </ul>
      </nav>

      {/* Footer nav */}
      <div className="border-t border-secondary px-3 py-4">
        <ul className="space-y-1">
          {footerNavItems.map((item) => (
            <li key={item.label}>
              <NavItem
                item={item}
                isActive={pathname.startsWith(item.href || "")}
              />
            </li>
          ))}
        </ul>
      </div>
    </aside>
  );
}
