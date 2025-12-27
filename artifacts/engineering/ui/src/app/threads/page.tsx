"use client";

import { useState } from "react";
import { useLeanOSData } from "@/providers/data-provider";
import { ThreadCard } from "@/components/leanos/thread-progress";
import { getThreadTypes } from "@/lib/data";
import { cx } from "@/utils/cx";
import { Route, Terminal, ArrowRight } from "@untitledui/icons";

const STAGE_DESCRIPTIONS = [
  { name: "Input", desc: "Factual observation" },
  { name: "Hypothesis", desc: "Assumption tested" },
  { name: "Implication", desc: "Impact analyzed" },
  { name: "Decision", desc: "Commitment made" },
  { name: "Actions", desc: "Tasks executed" },
  { name: "Learning", desc: "Outcome validated" },
];

const TYPE_COLORS: Record<string, { bg: string; text: string; border: string; activeBg: string }> = {
  sales: { bg: "bg-blue-50", text: "text-blue-700", border: "border-blue-200", activeBg: "bg-blue-600" },
  marketing: { bg: "bg-purple-50", text: "text-purple-700", border: "border-purple-200", activeBg: "bg-purple-600" },
  operations: { bg: "bg-orange-50", text: "text-orange-700", border: "border-orange-200", activeBg: "bg-orange-600" },
};

export default function ThreadsPage() {
  const data = useLeanOSData();
  const types = getThreadTypes(data.threads);
  const [activeType, setActiveType] = useState<string | null>(null);

  const filteredThreads = activeType
    ? data.threads.filter((t) => t.type === activeType)
    : data.threads;

  const completedCount = data.threads.filter((t) => t.currentStage >= 6).length;
  const activeCount = data.threads.filter((t) => t.currentStage < 6).length;

  return (
    <div className="p-6 lg:p-8 bg-gray-50 min-h-screen">
      {/* Header */}
      <div className="mb-8">
        <h1 className="text-2xl font-bold text-gray-900">Threads</h1>
        <p className="mt-1 text-sm font-medium text-gray-500">
          Execution threads following the 6-stage causal flow
        </p>
      </div>

      {/* Stats */}
      <div className="mb-6 grid gap-4 sm:grid-cols-3">
        <div className="rounded-xl border-2 border-gray-200 bg-white p-5 hover:border-brand-300 transition-colors">
          <p className="text-3xl font-bold text-gray-900">
            {data.threads.length}
          </p>
          <p className="mt-1 text-sm font-medium text-gray-500">Total threads</p>
        </div>
        <div className="rounded-xl border-2 border-brand-200 bg-brand-50 p-5">
          <p className="text-3xl font-bold text-brand-700">
            {activeCount}
          </p>
          <p className="mt-1 text-sm font-medium text-brand-600">In progress</p>
        </div>
        <div className="rounded-xl border-2 border-success-200 bg-success-50 p-5">
          <p className="text-3xl font-bold text-success-700">
            {completedCount}
          </p>
          <p className="mt-1 text-sm font-medium text-success-600">Completed</p>
        </div>
      </div>

      {/* Filter Tabs */}
      <div className="mb-6 flex items-center gap-2 overflow-x-auto pb-1">
        <button
          onClick={() => setActiveType(null)}
          className={cx(
            "rounded-full px-4 py-2 text-sm font-semibold transition-all duration-200",
            activeType === null
              ? "bg-brand-600 text-white shadow-sm"
              : "bg-white border-2 border-gray-200 text-gray-700 hover:border-brand-300 hover:bg-brand-50"
          )}
        >
          All ({data.threads.length})
        </button>
        {types.map((type) => {
          const count = data.threads.filter((t) => t.type === type).length;
          const colors = TYPE_COLORS[type] || TYPE_COLORS.operations;
          return (
            <button
              key={type}
              onClick={() => setActiveType(type)}
              className={cx(
                "rounded-full px-4 py-2 text-sm font-semibold capitalize transition-all duration-200",
                activeType === type
                  ? `${colors.activeBg} text-white shadow-sm`
                  : `${colors.bg} ${colors.text} border-2 ${colors.border} hover:opacity-80`
              )}
            >
              {type} ({count})
            </button>
          );
        })}
      </div>

      {/* Stage Legend */}
      <div className="mb-6 rounded-xl border-2 border-gray-200 bg-white p-5">
        <h3 className="text-sm font-bold text-gray-900 mb-4">
          6-Stage Causal Flow
        </h3>
        <div className="grid grid-cols-2 sm:grid-cols-3 lg:grid-cols-6 gap-3">
          {STAGE_DESCRIPTIONS.map((stage, i) => (
            <div key={stage.name} className="flex items-start gap-2.5">
              <span className="flex h-6 w-6 items-center justify-center rounded-full bg-brand-100 text-xs font-bold text-brand-700 flex-shrink-0">
                {i + 1}
              </span>
              <div>
                <p className="text-sm font-semibold text-gray-900">{stage.name}</p>
                <p className="text-xs text-gray-500">{stage.desc}</p>
              </div>
            </div>
          ))}
        </div>
      </div>

      {/* Thread List */}
      {filteredThreads.length > 0 ? (
        <div className="space-y-4">
          {filteredThreads.map((thread) => (
            <ThreadCard key={thread.path} thread={thread} />
          ))}
        </div>
      ) : (
        <div className="text-center py-16 rounded-xl border-2 border-dashed border-gray-300 bg-white">
          <div className="mx-auto mb-4 flex h-14 w-14 items-center justify-center rounded-full bg-gray-100">
            <Route className="h-7 w-7 text-gray-400" />
          </div>
          <h3 className="text-lg font-semibold text-gray-900">
            {activeType ? `No ${activeType} threads` : "No threads yet"}
          </h3>
          <p className="mt-2 text-sm text-gray-500 max-w-md mx-auto">
            {activeType
              ? `No ${activeType} threads have been created. Switch to "All" to see other thread types.`
              : "Threads are created when you execute workflows like sales outreach, marketing campaigns, or operations."}
          </p>

          {!activeType && (
            <div className="mt-6 rounded-lg bg-brand-50 border border-brand-200 p-4 max-w-md mx-auto">
              <div className="flex items-start gap-3 text-left">
                <Terminal className="h-5 w-5 text-brand-600 mt-0.5 flex-shrink-0" />
                <div>
                  <p className="text-sm font-semibold text-brand-800">
                    Start a thread with a skill
                  </p>
                  <p className="mt-1 text-xs text-brand-700">
                    Invoke <code className="bg-brand-100 px-1 py-0.5 rounded font-mono">sales-execution</code> or <code className="bg-brand-100 px-1 py-0.5 rounded font-mono">marketing-execution</code> to create your first thread.
                  </p>
                </div>
              </div>
            </div>
          )}

          {activeType && (
            <button
              onClick={() => setActiveType(null)}
              className="mt-4 inline-flex items-center gap-1 rounded-lg bg-brand-600 px-4 py-2 text-sm font-semibold text-white hover:bg-brand-700 transition-colors"
            >
              View all threads
              <ArrowRight className="h-4 w-4" />
            </button>
          )}
        </div>
      )}
    </div>
  );
}
