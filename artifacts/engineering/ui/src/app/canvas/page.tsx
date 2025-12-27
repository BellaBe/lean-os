"use client";

import { useLeanOSData } from "@/providers/data-provider";
import { CanvasGrid } from "@/components/leanos/canvas-grid";
import { CheckCircle, Circle, AlertCircle, ArrowRight, Terminal } from "@untitledui/icons";
import { cx } from "@/utils/cx";

export default function CanvasPage() {
  const data = useLeanOSData();
  const { canvas } = data;

  // Sort sections by number
  const sortedSections = [...canvas.sections].sort(
    (a, b) => parseInt(a.number) - parseInt(b.number)
  );

  const completeCount = sortedSections.filter((s) => s.status === "complete").length;
  const draftCount = sortedSections.filter((s) => s.status === "draft").length;
  const missingCount = sortedSections.filter((s) => s.status === "missing").length;

  const getStatusLabel = (status: string) => {
    switch (status) {
      case "complete":
        return { text: "Complete", bg: "bg-success-50", text_color: "text-success-700", border: "border-success-200" };
      case "draft":
        return { text: "In Progress", bg: "bg-warning-50", text_color: "text-warning-700", border: "border-warning-200" };
      default:
        return { text: "Needs Attention", bg: "bg-gray-50", text_color: "text-gray-600", border: "border-gray-200" };
    }
  };

  return (
    <div className="p-6 lg:p-8 bg-gray-50 min-h-screen">
      {/* Header */}
      <div className="mb-8">
        <h1 className="text-2xl font-bold text-gray-900">
          Strategy Canvas
        </h1>
        <p className="mt-1 text-sm font-medium text-gray-500">
          Your 15-section strategic foundation for building and scaling your venture
        </p>
      </div>

      {/* Health Overview */}
      <div className="mb-8 rounded-xl border-2 border-gray-200 bg-white p-6">
        <div className="flex flex-col sm:flex-row sm:items-center justify-between gap-4 mb-6">
          <div>
            <h2 className="text-lg font-bold text-gray-900">
              Canvas Health
            </h2>
            <p className="text-sm text-gray-500">
              Track your strategic foundation completeness
            </p>
          </div>
          <div className="flex items-center gap-2">
            <span className={cx(
              "text-4xl font-bold",
              canvas.health === 100 ? "text-success-600" : canvas.health > 50 ? "text-brand-600" : "text-warning-600"
            )}>
              {canvas.health}%
            </span>
            <span className="text-sm font-medium text-gray-500">complete</span>
          </div>
        </div>

        {/* Progress bar */}
        <div className="h-3 rounded-full bg-gray-100 overflow-hidden mb-6">
          <div
            className={cx(
              "h-full rounded-full transition-all duration-500",
              canvas.health === 100 ? "bg-success-500" : canvas.health > 50 ? "bg-brand-600" : "bg-warning-500"
            )}
            style={{ width: `${Math.max(canvas.health, 2)}%` }}
          />
        </div>

        {/* Stats */}
        <div className="grid grid-cols-3 gap-4">
          <div className="rounded-lg bg-success-50 border border-success-200 p-4 text-center">
            <div className="flex items-center justify-center gap-2 mb-1">
              <CheckCircle className="h-5 w-5 text-success-600" />
              <span className="text-2xl font-bold text-success-700">{completeCount}</span>
            </div>
            <span className="text-xs font-medium text-success-600">Complete</span>
          </div>
          <div className="rounded-lg bg-warning-50 border border-warning-200 p-4 text-center">
            <div className="flex items-center justify-center gap-2 mb-1">
              <AlertCircle className="h-5 w-5 text-warning-600" />
              <span className="text-2xl font-bold text-warning-700">{draftCount}</span>
            </div>
            <span className="text-xs font-medium text-warning-600">In Progress</span>
          </div>
          <div className="rounded-lg bg-gray-50 border border-gray-200 p-4 text-center">
            <div className="flex items-center justify-center gap-2 mb-1">
              <Circle className="h-5 w-5 text-gray-400" />
              <span className="text-2xl font-bold text-gray-600">{missingCount}</span>
            </div>
            <span className="text-xs font-medium text-gray-500">Need Content</span>
          </div>
        </div>

        {/* CTA for empty or low health canvas */}
        {canvas.health < 50 && (
          <div className="mt-6 rounded-lg bg-brand-50 border border-brand-200 p-4">
            <div className="flex items-start gap-3">
              <Terminal className="h-5 w-5 text-brand-600 mt-0.5" />
              <div>
                <p className="text-sm font-semibold text-brand-800">
                  Populate your Canvas to unlock LeanOS capabilities
                </p>
                <p className="mt-1 text-sm text-brand-700">
                  Run <code className="bg-brand-100 px-1.5 py-0.5 rounded font-mono text-xs">foundations-builder</code> in Claude Code to get started with guided setup.
                </p>
              </div>
            </div>
          </div>
        )}
      </div>

      {/* Canvas Grid */}
      <div className="rounded-xl border-2 border-gray-200 bg-white p-6 mb-8">
        <h2 className="text-lg font-bold text-gray-900 mb-4">
          Quick Overview
        </h2>
        <CanvasGrid sections={sortedSections} />
      </div>

      {/* Section Details */}
      <div>
        <div className="flex items-center justify-between mb-4">
          <h2 className="text-lg font-bold text-gray-900">Section Details</h2>
          <span className="text-sm text-gray-500">{sortedSections.length} sections</span>
        </div>
        <div className="grid gap-4 md:grid-cols-2 lg:grid-cols-3">
          {sortedSections.map((section) => {
            const statusStyle = getStatusLabel(section.status);
            return (
              <div
                key={section.slug}
                className={cx(
                  "group rounded-xl border-2 bg-white p-5 transition-all duration-200 cursor-pointer",
                  "hover:shadow-md hover:-translate-y-0.5",
                  section.status === "complete" ? "border-success-200 hover:border-success-400" :
                  section.status === "draft" ? "border-warning-200 hover:border-warning-400" :
                  "border-gray-200 hover:border-brand-300"
                )}
              >
                <div className="flex items-start justify-between mb-3">
                  <div className="flex items-center gap-2">
                    <span className="flex h-6 w-6 items-center justify-center rounded-md bg-gray-100 text-xs font-bold text-gray-600">
                      {section.number}
                    </span>
                    <h3 className="text-sm font-semibold text-gray-900 group-hover:text-brand-700">
                      {section.name}
                    </h3>
                  </div>
                  {section.status === "complete" ? (
                    <CheckCircle className="h-5 w-5 text-success-600 flex-shrink-0" />
                  ) : section.status === "draft" ? (
                    <AlertCircle className="h-5 w-5 text-warning-600 flex-shrink-0" />
                  ) : (
                    <Circle className="h-5 w-5 text-gray-300 flex-shrink-0" />
                  )}
                </div>

                {section.summary ? (
                  <p className="text-sm text-gray-600 leading-relaxed">
                    {section.summary}
                  </p>
                ) : (
                  <div className={cx(
                    "rounded-lg p-3",
                    statusStyle.bg,
                    statusStyle.border,
                    "border"
                  )}>
                    <p className={cx("text-xs font-medium", statusStyle.text_color)}>
                      {section.status === "missing"
                        ? "Run foundations-builder to populate this section"
                        : "Content being developed"
                      }
                    </p>
                  </div>
                )}

                {/* Status badge */}
                <div className="mt-3 pt-3 border-t border-gray-100 flex items-center justify-between">
                  <span className={cx(
                    "inline-flex items-center rounded-full px-2.5 py-1 text-xs font-semibold",
                    statusStyle.bg,
                    statusStyle.text_color
                  )}>
                    {statusStyle.text}
                  </span>
                  <ArrowRight className="h-4 w-4 text-gray-300 group-hover:text-brand-600 transition-colors" />
                </div>
              </div>
            );
          })}
        </div>
      </div>
    </div>
  );
}
