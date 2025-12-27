"use client";

import { useLeanOSData } from "@/providers/data-provider";
import { Target04, Terminal, Route, CheckCircle, Clock, AlertCircle } from "@untitledui/icons";
import { cx } from "@/utils/cx";

const STATUS_STYLES: Record<string, { bg: string; text: string; border: string; icon: typeof CheckCircle }> = {
  active: { bg: "bg-brand-50", text: "text-brand-700", border: "border-brand-200", icon: Clock },
  completed: { bg: "bg-success-50", text: "text-success-700", border: "border-success-200", icon: CheckCircle },
  blocked: { bg: "bg-error-50", text: "text-error-700", border: "border-error-200", icon: AlertCircle },
};

const EXAMPLE_GOAL = {
  title: "Launch MVP to First 10 Customers",
  objective: "Validate product-market fit by acquiring and retaining 10 paying customers within Q1",
  status: "active",
  linkedThreads: 3,
  progress: 40,
};

export default function GoalsPage() {
  const data = useLeanOSData();

  const activeGoals = data.goals.filter(g => g.status === "active").length;
  const completedGoals = data.goals.filter(g => g.status === "completed").length;

  return (
    <div className="p-6 lg:p-8 bg-gray-50 min-h-screen">
      {/* Header */}
      <div className="mb-8">
        <h1 className="text-2xl font-bold text-gray-900">Goals</h1>
        <p className="mt-1 text-sm font-medium text-gray-500">
          Strategic objectives with linked execution threads
        </p>
      </div>

      {data.goals.length > 0 ? (
        <>
          {/* Stats */}
          <div className="mb-6 grid gap-4 sm:grid-cols-3">
            <div className="rounded-xl border-2 border-gray-200 bg-white p-5 hover:border-brand-300 transition-colors">
              <p className="text-3xl font-bold text-gray-900">{data.goals.length}</p>
              <p className="mt-1 text-sm font-medium text-gray-500">Total goals</p>
            </div>
            <div className="rounded-xl border-2 border-brand-200 bg-brand-50 p-5">
              <p className="text-3xl font-bold text-brand-700">{activeGoals}</p>
              <p className="mt-1 text-sm font-medium text-brand-600">Active</p>
            </div>
            <div className="rounded-xl border-2 border-success-200 bg-success-50 p-5">
              <p className="text-3xl font-bold text-success-700">{completedGoals}</p>
              <p className="mt-1 text-sm font-medium text-success-600">Completed</p>
            </div>
          </div>

          {/* Goals list */}
          <div className="space-y-4">
            {data.goals.map((goal) => {
              const statusStyle = STATUS_STYLES[goal.status] || STATUS_STYLES.active;
              const StatusIcon = statusStyle.icon;
              return (
                <div
                  key={goal.id}
                  className="group rounded-xl border-2 border-gray-200 bg-white p-5 hover:border-brand-300 hover:shadow-md hover:-translate-y-0.5 transition-all duration-200 cursor-pointer"
                >
                  <div className="flex items-start justify-between gap-4">
                    <div className="flex items-start gap-4 flex-1">
                      <div className="flex h-12 w-12 items-center justify-center rounded-xl bg-brand-50 flex-shrink-0">
                        <Target04 className="h-6 w-6 text-brand-600" />
                      </div>
                      <div className="flex-1 min-w-0">
                        <h3 className="text-base font-bold text-gray-900 group-hover:text-brand-700 transition-colors">
                          {goal.title}
                        </h3>
                        <p className="mt-1 text-sm text-gray-600">{goal.objective}</p>
                      </div>
                    </div>
                    <span className={cx(
                      "inline-flex items-center gap-1.5 rounded-full px-3 py-1.5 text-xs font-bold capitalize border",
                      statusStyle.bg,
                      statusStyle.text,
                      statusStyle.border
                    )}>
                      <StatusIcon className="h-3.5 w-3.5" />
                      {goal.status}
                    </span>
                  </div>
                </div>
              );
            })}
          </div>
        </>
      ) : (
        <div className="space-y-6">
          {/* Example Goal Card */}
          <div className="rounded-xl border-2 border-dashed border-brand-300 bg-white p-6">
            <div className="flex items-center gap-2 mb-4">
              <span className="rounded-full bg-brand-100 px-2.5 py-1 text-xs font-bold text-brand-700">
                EXAMPLE
              </span>
              <span className="text-xs text-gray-500">This shows how a goal looks</span>
            </div>

            <div className="flex items-start gap-4">
              <div className="flex h-12 w-12 items-center justify-center rounded-xl bg-brand-50 flex-shrink-0">
                <Target04 className="h-6 w-6 text-brand-600" />
              </div>
              <div className="flex-1">
                <h3 className="text-base font-bold text-gray-900">{EXAMPLE_GOAL.title}</h3>
                <p className="mt-1 text-sm text-gray-600">{EXAMPLE_GOAL.objective}</p>

                <div className="mt-4 flex items-center gap-4">
                  <div className="flex items-center gap-2">
                    <Route className="h-4 w-4 text-gray-400" />
                    <span className="text-sm text-gray-600">
                      <span className="font-semibold text-brand-700">{EXAMPLE_GOAL.linkedThreads}</span> linked threads
                    </span>
                  </div>
                  <div className="flex items-center gap-2">
                    <div className="h-2 w-24 rounded-full bg-gray-100 overflow-hidden">
                      <div className="h-full bg-brand-600 rounded-full" style={{ width: `${EXAMPLE_GOAL.progress}%` }} />
                    </div>
                    <span className="text-sm font-medium text-gray-600">{EXAMPLE_GOAL.progress}%</span>
                  </div>
                </div>
              </div>
              <span className="inline-flex items-center gap-1.5 rounded-full bg-brand-50 border border-brand-200 px-3 py-1.5 text-xs font-bold text-brand-700 capitalize">
                <Clock className="h-3.5 w-3.5" />
                {EXAMPLE_GOAL.status}
              </span>
            </div>
          </div>

          {/* Empty State CTA */}
          <div className="text-center py-12 rounded-xl border-2 border-dashed border-gray-300 bg-white">
            <div className="mx-auto mb-4 flex h-14 w-14 items-center justify-center rounded-full bg-gray-100">
              <Target04 className="h-7 w-7 text-gray-400" />
            </div>
            <h3 className="text-lg font-semibold text-gray-900">Create Your First Goal</h3>
            <p className="mt-2 text-sm text-gray-500 max-w-md mx-auto">
              Goals provide direction for LeanOS. They link to execution threads so you can track progress toward strategic objectives.
            </p>

            <div className="mt-6 rounded-lg bg-brand-50 border border-brand-200 p-4 max-w-md mx-auto">
              <div className="flex items-start gap-3 text-left">
                <Terminal className="h-5 w-5 text-brand-600 mt-0.5 flex-shrink-0" />
                <div>
                  <p className="text-sm font-semibold text-brand-800">
                    Create a goal with goal-setter
                  </p>
                  <p className="mt-1 text-sm text-brand-700">
                    Run <code className="bg-brand-100 px-1.5 py-0.5 rounded font-mono text-xs">goal-setter</code> in Claude Code to define your objective and success criteria.
                  </p>
                </div>
              </div>
            </div>

            <div className="mt-6 pt-6 border-t border-gray-200 max-w-md mx-auto">
              <p className="text-xs text-gray-500">
                <span className="font-medium">How goals work:</span> Define an objective → LeanOS creates execution threads → Track progress automatically as threads complete stages
              </p>
            </div>
          </div>
        </div>
      )}
    </div>
  );
}
