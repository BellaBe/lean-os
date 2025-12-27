"use client";

import { useLeanOSData } from "@/providers/data-provider";
import { computeStats } from "@/lib/data";
import { StatCard, EmptyStateCard } from "@/components/leanos/stat-card";
import { CanvasGrid } from "@/components/leanos/canvas-grid";
import { ThreadCard } from "@/components/leanos/thread-progress";
import { Target04, Grid01, Route, Zap, Users01, ArrowRight, CheckCircle, AlertCircle, Circle } from "@untitledui/icons";
import Link from "next/link";
import { cx } from "@/utils/cx";

export default function DashboardPage() {
  const data = useLeanOSData();
  const stats = computeStats(data);

  const activeThreads = data.threads.filter((t) => t.currentStage < 6);
  const hasNoGoals = stats.goals.total === 0;
  const hasEmptyCanvas = stats.canvas.health === 0;

  return (
    <div className="p-6 lg:p-8 bg-gray-50 min-h-screen">
      {/* Header */}
      <div className="mb-8">
        <h1 className="text-2xl font-bold text-gray-900">Dashboard</h1>
        <p className="mt-1 text-sm font-medium text-gray-500">
          Overview of your LeanOS system state
        </p>
      </div>

      {/* Stats Grid */}
      <div className="grid gap-4 sm:grid-cols-2 lg:grid-cols-4 mb-8">
        <StatCard
          title="Goals"
          value={stats.goals.total}
          subtitle={
            stats.goals.active > 0
              ? `${stats.goals.active} active`
              : "No active goals"
          }
          icon={Target04}
          color="brand"
          href="/goals"
          action={hasNoGoals ? { label: "Create your first goal" } : undefined}
        />
        <StatCard
          title="Canvas Health"
          value={`${stats.canvas.health}%`}
          subtitle={`${stats.canvas.populated}/${stats.canvas.total} sections`}
          icon={Grid01}
          color={stats.canvas.health > 50 ? "success" : "warning"}
          href="/canvas"
          action={hasEmptyCanvas ? { label: "Set up Canvas" } : undefined}
        />
        <StatCard
          title="Threads"
          value={stats.threads.total}
          subtitle={`${stats.threads.completed} completed`}
          icon={Route}
          color="default"
          href="/threads"
        />
        <StatCard
          title="Skills"
          value={stats.skills.total}
          subtitle={`${stats.agents.total} agents`}
          icon={Zap}
          color="brand"
          href="/skills"
        />
      </div>

      {/* Two Column Layout */}
      <div className="grid gap-6 lg:grid-cols-2">
        {/* Canvas Health */}
        <div className="rounded-xl border-2 border-gray-200 bg-white p-6">
          <div className="flex items-center justify-between mb-4">
            <div>
              <h2 className="text-lg font-bold text-gray-900">
                Canvas Health
              </h2>
              <p className="text-sm text-gray-500">
                Your 15-section strategic foundation
              </p>
            </div>
            <Link
              href="/canvas"
              className="inline-flex items-center gap-1 text-sm font-semibold text-brand-600 hover:text-brand-700"
            >
              View all
              <ArrowRight className="h-4 w-4" />
            </Link>
          </div>

          {/* Progress bar */}
          <div className="mb-6">
            <div className="flex items-center justify-between text-sm mb-2">
              <span className="font-medium text-gray-600">Progress</span>
              <span className="font-bold text-gray-900">
                {stats.canvas.health}%
              </span>
            </div>
            <div className="h-2.5 rounded-full bg-gray-100 overflow-hidden">
              <div
                className={cx(
                  "h-full rounded-full transition-all duration-500",
                  stats.canvas.health > 50 ? "bg-success-500" : stats.canvas.health > 0 ? "bg-brand-600" : "bg-gray-300"
                )}
                style={{ width: `${Math.max(stats.canvas.health, 2)}%` }}
              />
            </div>
          </div>

          {/* Canvas Grid */}
          <CanvasGrid sections={data.canvas.sections} compact />

          {/* Legend */}
          <div className="mt-4 flex items-center justify-center gap-4 text-xs">
            <div className="flex items-center gap-1.5">
              <div className="h-3 w-3 rounded bg-success-100 border border-success-300" />
              <span className="text-gray-600">Complete</span>
            </div>
            <div className="flex items-center gap-1.5">
              <div className="h-3 w-3 rounded bg-warning-100 border border-warning-300" />
              <span className="text-gray-600">Draft</span>
            </div>
            <div className="flex items-center gap-1.5">
              <div className="h-3 w-3 rounded bg-gray-100 border border-gray-300" />
              <span className="text-gray-600">Missing</span>
            </div>
          </div>

          {/* CTA for empty canvas */}
          {hasEmptyCanvas && (
            <div className="mt-6 rounded-lg bg-brand-50 border border-brand-200 p-4">
              <p className="text-sm font-medium text-brand-800">
                Your Canvas is empty. Populate it to define your strategic foundation.
              </p>
              <p className="mt-1 text-xs text-brand-600">
                Run <code className="bg-brand-100 px-1 py-0.5 rounded">foundations-builder</code> to get started.
              </p>
            </div>
          )}
        </div>

        {/* Active Threads */}
        <div className="rounded-xl border-2 border-gray-200 bg-white p-6">
          <div className="flex items-center justify-between mb-4">
            <div>
              <h2 className="text-lg font-bold text-gray-900">
                Active Threads
              </h2>
              <p className="text-sm text-gray-500">
                Execution threads in progress
              </p>
            </div>
            <Link
              href="/threads"
              className="inline-flex items-center gap-1 text-sm font-semibold text-brand-600 hover:text-brand-700"
            >
              View all
              <ArrowRight className="h-4 w-4" />
            </Link>
          </div>

          {activeThreads.length > 0 ? (
            <div className="space-y-4">
              {activeThreads.slice(0, 3).map((thread) => (
                <ThreadCard key={thread.path} thread={thread} />
              ))}
              {activeThreads.length > 3 && (
                <Link
                  href="/threads"
                  className="block text-center text-sm font-medium text-brand-600 hover:text-brand-700 py-2"
                >
                  +{activeThreads.length - 3} more threads
                </Link>
              )}
            </div>
          ) : (
            <EmptyStateCard
              title="No active threads"
              description="Threads track execution through the 6-stage causal flow: Input → Hypothesis → Implication → Decision → Actions → Learning"
              icon={Route}
              action={{
                label: "View all threads",
                href: "/threads",
              }}
            />
          )}
        </div>
      </div>

      {/* Quick Reference Cards */}
      <div className="mt-8">
        <h2 className="text-lg font-bold text-gray-900 mb-4">Quick Reference</h2>
        <div className="grid gap-4 sm:grid-cols-3">
          <Link
            href="/agents"
            className="group rounded-xl border-2 border-brand-200 bg-brand-50/50 p-5 hover:border-brand-400 hover:bg-brand-50 hover:shadow-md transition-all duration-200"
          >
            <div className="flex items-center gap-4">
              <div className="flex h-14 w-14 items-center justify-center rounded-xl bg-brand-100 group-hover:scale-110 transition-transform">
                <Users01 className="h-7 w-7 text-brand-600" />
              </div>
              <div>
                <p className="text-3xl font-bold text-gray-900">
                  {stats.agents.total}
                </p>
                <p className="text-sm font-semibold text-brand-700">Agents</p>
              </div>
            </div>
            <p className="mt-3 text-sm text-gray-600">
              Orchestrator agents that route skills for domain-specific tasks
            </p>
            <div className="mt-3 flex items-center gap-1 text-xs font-semibold text-brand-600">
              View agents <ArrowRight className="h-3.5 w-3.5" />
            </div>
          </Link>

          <Link
            href="/skills"
            className="group rounded-xl border-2 border-purple-200 bg-purple-50/50 p-5 hover:border-purple-400 hover:bg-purple-50 hover:shadow-md transition-all duration-200"
          >
            <div className="flex items-center gap-4">
              <div className="flex h-14 w-14 items-center justify-center rounded-xl bg-purple-100 group-hover:scale-110 transition-transform">
                <Zap className="h-7 w-7 text-purple-600" />
              </div>
              <div>
                <p className="text-3xl font-bold text-gray-900">
                  {Object.keys(stats.skills.byCategory).length}
                </p>
                <p className="text-sm font-semibold text-purple-700">Skill Categories</p>
              </div>
            </div>
            <p className="mt-3 text-sm text-gray-600">
              AI capabilities organized by domain: engineering, marketing, sales
            </p>
            <div className="mt-3 flex items-center gap-1 text-xs font-semibold text-purple-600">
              Browse skills <ArrowRight className="h-3.5 w-3.5" />
            </div>
          </Link>

          <Link
            href="/threads"
            className="group rounded-xl border-2 border-orange-200 bg-orange-50/50 p-5 hover:border-orange-400 hover:bg-orange-50 hover:shadow-md transition-all duration-200"
          >
            <div className="flex items-center gap-4">
              <div className="flex h-14 w-14 items-center justify-center rounded-xl bg-orange-100 group-hover:scale-110 transition-transform">
                <Route className="h-7 w-7 text-orange-600" />
              </div>
              <div>
                <p className="text-3xl font-bold text-gray-900">
                  {Object.keys(stats.threads.byType).length}
                </p>
                <p className="text-sm font-semibold text-orange-700">Thread Types</p>
              </div>
            </div>
            <p className="mt-3 text-sm text-gray-600">
              Execution tracks: sales, marketing, operations workflows
            </p>
            <div className="mt-3 flex items-center gap-1 text-xs font-semibold text-orange-600">
              View threads <ArrowRight className="h-3.5 w-3.5" />
            </div>
          </Link>
        </div>
      </div>
    </div>
  );
}
