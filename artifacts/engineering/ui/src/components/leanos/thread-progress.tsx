"use client";

import { cx } from "@/utils/cx";
import type { Thread, ThreadStage } from "@/lib/types";
import { Check } from "@untitledui/icons";
import { Tooltip, TooltipTrigger } from "@/components/base/tooltip/tooltip";

interface ThreadProgressProps {
  thread: Thread;
  showLabels?: boolean;
  size?: "sm" | "md";
}

const STAGE_NAMES = ["Input", "Hypothesis", "Implication", "Decision", "Actions", "Learning"];

export function ThreadProgress({ thread, showLabels = false, size = "sm" }: ThreadProgressProps) {
  const getStageState = (stage: ThreadStage, index: number) => {
    if (stage.status === "completed") return "completed";
    if (index + 1 === thread.currentStage) return "active";
    return "pending";
  };

  const indicatorSize = size === "sm" ? "h-6 w-6" : "h-8 w-8";
  const fontSize = size === "sm" ? "text-xs" : "text-sm";
  const connectorWidth = size === "sm" ? "w-6" : "w-8";

  return (
    <div className="flex items-center" role="list" aria-label="Thread progress">
      {thread.stages.map((stage, index) => {
        const state = getStageState(stage, index);
        const isLast = index === thread.stages.length - 1;

        return (
          <div key={stage.number} className="flex items-center">
            {/* Step indicator */}
            <Tooltip
              title={stage.name}
              description={state === "completed" ? "Completed" : state === "active" ? "In Progress" : "Pending"}
              arrow
            >
              <TooltipTrigger>
                <div
                  className={cx(
                    "flex items-center justify-center rounded-full transition-all duration-200",
                    indicatorSize,
                    // Completed state - solid brand
                    state === "completed" && "bg-brand-600 border-2 border-brand-600",
                    // Active state - brand ring
                    state === "active" && "bg-brand-600 border-2 border-brand-600 ring-4 ring-brand-100",
                    // Pending state - gray
                    state === "pending" && "bg-gray-100 border-2 border-gray-200"
                  )}
                  aria-current={state === "active" ? "step" : undefined}
                >
                  {state === "completed" ? (
                    <Check className="h-3.5 w-3.5 text-white" />
                  ) : (
                    <span
                      className={cx(
                        "font-semibold",
                        fontSize,
                        state === "active" ? "text-white" : "text-gray-500"
                      )}
                    >
                      {stage.number}
                    </span>
                  )}
                </div>
              </TooltipTrigger>
            </Tooltip>

            {/* Connector line */}
            {!isLast && (
              <div
                className={cx(
                  "h-0.5 mx-1 transition-colors duration-200",
                  connectorWidth,
                  state === "completed" ? "bg-brand-600" : "bg-gray-200"
                )}
              />
            )}
          </div>
        );
      })}

      {/* Labels underneath (optional) */}
      {showLabels && (
        <div className="flex items-center mt-2">
          {thread.stages.map((stage, index) => {
            const state = getStageState(stage, index);
            const isLast = index === thread.stages.length - 1;

            return (
              <div key={`label-${stage.number}`} className="flex items-center">
                <span
                  className={cx(
                    "text-xs font-medium text-center",
                    indicatorSize.replace("h-", "w-"),
                    state === "active" && "text-brand-700",
                    state === "completed" && "text-gray-700",
                    state === "pending" && "text-gray-500"
                  )}
                >
                  {stage.name}
                </span>
                {!isLast && <div className={cx("mx-1", connectorWidth)} />}
              </div>
            );
          })}
        </div>
      )}
    </div>
  );
}

interface ThreadCardProps {
  thread: Thread;
}

export function ThreadCard({ thread }: ThreadCardProps) {
  const completedStages = thread.stages.filter(
    (s) => s.status === "completed"
  ).length;
  const isComplete = completedStages === 6;
  const progressPercent = Math.round((completedStages / 6) * 100);

  const typeColors: Record<string, { bg: string; text: string; border: string }> = {
    sales: { bg: "bg-blue-50", text: "text-blue-700", border: "border-blue-200" },
    marketing: { bg: "bg-purple-50", text: "text-purple-700", border: "border-purple-200" },
    operations: { bg: "bg-orange-50", text: "text-orange-700", border: "border-orange-200" },
  };

  const colors = typeColors[thread.type] || typeColors.operations;

  return (
    <div
      className={cx(
        "group rounded-xl border-2 bg-white p-5 transition-all duration-200 cursor-pointer",
        "border-gray-200 hover:border-brand-300 hover:shadow-md hover:-translate-y-0.5"
      )}
    >
      <div className="flex items-start justify-between gap-4">
        <div className="flex-1 min-w-0">
          <div className="flex items-center gap-2 flex-wrap">
            <span
              className={cx(
                "inline-flex items-center rounded-md px-2.5 py-1 text-xs font-bold uppercase border",
                colors.bg,
                colors.text,
                colors.border
              )}
            >
              {thread.type}
            </span>
            {isComplete && (
              <span className="inline-flex items-center gap-1 rounded-full bg-success-50 border border-success-200 px-2.5 py-1 text-xs font-bold text-success-700">
                <Check className="h-3.5 w-3.5" />
                Complete
              </span>
            )}
            {!isComplete && (
              <span className="inline-flex items-center rounded-full bg-brand-50 border border-brand-200 px-2.5 py-1 text-xs font-bold text-brand-700">
                Stage {thread.currentStage}/6
              </span>
            )}
          </div>
          <h3 className="mt-3 text-base font-bold text-gray-900 group-hover:text-brand-700 transition-colors">
            {thread.name}
          </h3>
          <div className="mt-1.5 inline-flex items-center gap-1.5 rounded-md bg-gray-100 px-2 py-1 hover:bg-gray-200 transition-colors cursor-pointer group/path">
            <span className="text-xs text-gray-400 font-medium">threads/</span>
            <span className="text-xs text-gray-700 font-mono group-hover/path:text-brand-700 transition-colors">
              {thread.path.replace('threads/', '')}
            </span>
          </div>
        </div>
        <div className="text-right flex-shrink-0">
          <div className="flex items-baseline gap-1">
            <span className="text-3xl font-bold text-gray-900">
              {completedStages}
            </span>
            <span className="text-lg font-medium text-gray-400">/6</span>
          </div>
          <p className="text-xs font-medium text-gray-500">{progressPercent}% complete</p>
        </div>
      </div>

      {/* Progress bar */}
      <div className="mt-4 h-2 w-full rounded-full bg-gray-100 overflow-hidden">
        <div
          className={cx(
            "h-full rounded-full transition-all duration-500",
            isComplete ? "bg-success-500" : "bg-brand-600"
          )}
          style={{ width: `${Math.max(progressPercent, 2)}%` }}
        />
      </div>

      {/* Step indicators */}
      <div className="mt-4">
        <ThreadProgress thread={thread} />
      </div>

      {/* Current stage label */}
      {!isComplete && (
        <div className="mt-4 pt-3 border-t border-gray-100 flex items-center justify-between">
          <p className="text-sm text-gray-600">
            <span className="font-semibold text-brand-700">Current:</span>{" "}
            {STAGE_NAMES[thread.currentStage - 1] || "Input"}
          </p>
          <span className="text-xs text-gray-400 group-hover:text-brand-600 transition-colors">
            Click to view details →
          </span>
        </div>
      )}
    </div>
  );
}
