"use client";

import { cx } from "@/utils/cx";
import type { CanvasSection } from "@/lib/types";
import { CheckCircle, Circle, AlertCircle } from "@untitledui/icons";
import { Tooltip, TooltipTrigger } from "@/components/base/tooltip/tooltip";

interface CanvasGridProps {
  sections: CanvasSection[];
  compact?: boolean;
}

export function CanvasGrid({ sections, compact = false }: CanvasGridProps) {
  // Sort sections by number
  const sortedSections = [...sections].sort(
    (a, b) => parseInt(a.number) - parseInt(b.number)
  );

  const statusIcon = (status: CanvasSection["status"]) => {
    switch (status) {
      case "complete":
        return <CheckCircle className="h-4 w-4 text-success-600" />;
      case "draft":
        return <AlertCircle className="h-4 w-4 text-warning-600" />;
      default:
        return <Circle className="h-4 w-4 text-gray-400" />;
    }
  };

  const getStatusStyles = (status: CanvasSection["status"]) => {
    switch (status) {
      case "complete":
        return {
          bg: "bg-success-50",
          border: "border-success-200",
          hoverBorder: "hover:border-success-400",
          label: "Complete",
        };
      case "draft":
        return {
          bg: "bg-warning-50",
          border: "border-warning-200",
          hoverBorder: "hover:border-warning-400",
          label: "Draft",
        };
      default:
        return {
          bg: "bg-gray-50",
          border: "border-gray-200",
          hoverBorder: "hover:border-gray-400",
          label: "Missing",
        };
    }
  };

  if (compact) {
    return (
      <div className="grid grid-cols-5 gap-1.5">
        {sortedSections.map((section) => {
          const styles = getStatusStyles(section.status);
          return (
            <Tooltip
              key={section.slug}
              title={`${section.number}. ${section.name}`}
              description={styles.label}
              arrow
            >
              <TooltipTrigger>
                <div
                  className={cx(
                    "relative h-8 rounded-md border-2 transition-all duration-200 cursor-pointer",
                    "flex items-center justify-center",
                    styles.bg,
                    styles.border,
                    styles.hoverBorder,
                    "hover:shadow-sm hover:scale-105"
                  )}
                >
                  <span className="text-[10px] font-semibold text-gray-600">
                    {section.number}
                  </span>
                </div>
              </TooltipTrigger>
            </Tooltip>
          );
        })}
      </div>
    );
  }

  return (
    <div className="grid grid-cols-3 gap-3 sm:grid-cols-5">
      {sortedSections.map((section) => {
        const styles = getStatusStyles(section.status);
        return (
          <div
            key={section.slug}
            className={cx(
              "group flex flex-col items-center justify-center rounded-xl border-2 p-4 transition-all duration-200 cursor-pointer",
              styles.bg,
              styles.border,
              styles.hoverBorder,
              "hover:shadow-md hover:-translate-y-0.5"
            )}
          >
            <div className="mb-2 transition-transform group-hover:scale-110">
              {statusIcon(section.status)}
            </div>
            <span className="text-center text-sm font-semibold text-gray-900">
              {section.number}
            </span>
            <span className="mt-0.5 text-center text-xs font-medium text-gray-600 line-clamp-1">
              {section.name}
            </span>
            <span
              className={cx(
                "mt-2 text-[10px] font-medium uppercase tracking-wide",
                section.status === "complete" && "text-success-600",
                section.status === "draft" && "text-warning-600",
                section.status === "missing" && "text-gray-400"
              )}
            >
              {styles.label}
            </span>
          </div>
        );
      })}
    </div>
  );
}
