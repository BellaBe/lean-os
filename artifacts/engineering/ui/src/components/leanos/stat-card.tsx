"use client";

import { cx } from "@/utils/cx";
import type { FC, ReactNode } from "react";
import Link from "next/link";

interface StatCardProps {
  title: string;
  value: string | number;
  subtitle?: string;
  icon?: FC<{ className?: string }>;
  trend?: {
    value: number;
    label: string;
  };
  color?: "default" | "brand" | "success" | "warning" | "error";
  href?: string;
  action?: {
    label: string;
    onClick?: () => void;
  };
}

export function StatCard({
  title,
  value,
  subtitle,
  icon: Icon,
  trend,
  color = "default",
  href,
  action,
}: StatCardProps) {
  const colorStyles = {
    default: {
      iconBg: "bg-gray-100",
      iconText: "text-gray-600",
      border: "border-gray-200",
      hoverBorder: "hover:border-gray-300",
    },
    brand: {
      iconBg: "bg-brand-50",
      iconText: "text-brand-600",
      border: "border-gray-200",
      hoverBorder: "hover:border-brand-300",
    },
    success: {
      iconBg: "bg-success-50",
      iconText: "text-success-600",
      border: "border-gray-200",
      hoverBorder: "hover:border-success-300",
    },
    warning: {
      iconBg: "bg-warning-50",
      iconText: "text-warning-600",
      border: "border-gray-200",
      hoverBorder: "hover:border-warning-300",
    },
    error: {
      iconBg: "bg-error-50",
      iconText: "text-error-600",
      border: "border-gray-200",
      hoverBorder: "hover:border-error-300",
    },
  };

  const styles = colorStyles[color];

  const CardWrapper = ({ children }: { children: ReactNode }) => {
    if (href) {
      return (
        <Link href={href} className="block">
          {children}
        </Link>
      );
    }
    return <>{children}</>;
  };

  return (
    <CardWrapper>
      <div
        className={cx(
          "group rounded-xl border-2 bg-white p-6 transition-all duration-200",
          styles.border,
          href && styles.hoverBorder,
          href && "cursor-pointer hover:shadow-md hover:-translate-y-0.5"
        )}
      >
        <div className="flex items-start justify-between">
          <div className="flex-1">
            <p className="text-sm font-medium text-gray-600">{title}</p>
            <p className="mt-2 text-3xl font-bold text-gray-900">{value}</p>
            {subtitle && (
              <p className="mt-1 text-sm font-medium text-gray-500">{subtitle}</p>
            )}
            {trend && (
              <div className="mt-2 flex items-center gap-1">
                <span
                  className={cx(
                    "text-sm font-semibold",
                    trend.value >= 0 ? "text-success-600" : "text-error-600"
                  )}
                >
                  {trend.value >= 0 ? "+" : ""}
                  {trend.value}%
                </span>
                <span className="text-sm text-gray-500">{trend.label}</span>
              </div>
            )}
            {action && (
              <button
                onClick={action.onClick}
                className="mt-3 text-sm font-semibold text-brand-600 hover:text-brand-700"
              >
                {action.label} →
              </button>
            )}
          </div>
          {Icon && (
            <div
              className={cx(
                "flex h-12 w-12 items-center justify-center rounded-xl transition-transform",
                styles.iconBg,
                href && "group-hover:scale-110"
              )}
            >
              <Icon className={cx("h-6 w-6", styles.iconText)} />
            </div>
          )}
        </div>
      </div>
    </CardWrapper>
  );
}

// Empty state card with CTA
interface EmptyStateCardProps {
  title: string;
  description: string;
  icon?: FC<{ className?: string }>;
  action?: {
    label: string;
    href?: string;
    onClick?: () => void;
  };
}

export function EmptyStateCard({
  title,
  description,
  icon: Icon,
  action,
}: EmptyStateCardProps) {
  return (
    <div className="rounded-xl border-2 border-dashed border-gray-300 bg-gray-50 p-8 text-center">
      {Icon && (
        <div className="mx-auto mb-4 flex h-12 w-12 items-center justify-center rounded-full bg-gray-100">
          <Icon className="h-6 w-6 text-gray-400" />
        </div>
      )}
      <h3 className="text-base font-semibold text-gray-900">{title}</h3>
      <p className="mt-1 text-sm text-gray-500">{description}</p>
      {action && (
        <div className="mt-4">
          {action.href ? (
            <Link
              href={action.href}
              className="inline-flex items-center rounded-lg bg-brand-600 px-4 py-2 text-sm font-semibold text-white hover:bg-brand-700 transition-colors"
            >
              {action.label}
            </Link>
          ) : (
            <button
              onClick={action.onClick}
              className="inline-flex items-center rounded-lg bg-brand-600 px-4 py-2 text-sm font-semibold text-white hover:bg-brand-700 transition-colors"
            >
              {action.label}
            </button>
          )}
        </div>
      )}
    </div>
  );
}
