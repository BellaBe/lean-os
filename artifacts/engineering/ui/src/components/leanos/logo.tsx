"use client";

import { cx } from "@/utils/cx";

interface LeanOSLogoProps {
  className?: string;
  showText?: boolean;
}

export function LeanOSLogo({ className, showText = true }: LeanOSLogoProps) {
  return (
    <div className={cx("flex items-center gap-2", className)}>
      {/* Logo mark */}
      <div className="relative h-8 w-8 flex items-center justify-center">
        <div className="absolute inset-0 bg-brand-solid rounded-lg" />
        <span className="relative text-white font-bold text-sm">L</span>
      </div>
      {showText && (
        <span className="text-xl font-semibold text-primary">
          Lean<span className="text-brand-primary">OS</span>
        </span>
      )}
    </div>
  );
}
