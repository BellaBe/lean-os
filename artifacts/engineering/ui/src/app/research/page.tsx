"use client";

import { useLeanOSData } from "@/providers/data-provider";
import { BookOpen01, Terminal, Link01, File01, Lightbulb02, ArrowRight } from "@untitledui/icons";
import { cx } from "@/utils/cx";

const EXAMPLE_SOURCES = [
  { type: "URL", name: "Stripe Atlas Startup Guide", desc: "Company formation best practices" },
  { type: "PDF", name: "Market Research Report", desc: "Industry analysis and trends" },
  { type: "Note", name: "Customer Interview Notes", desc: "Insights from 12 discovery calls" },
];

const EXAMPLE_PLAYBOOKS = [
  { name: "Market Validation", desc: "Step-by-step process to validate market opportunity" },
  { name: "Customer Discovery", desc: "Interview framework for understanding pain points" },
  { name: "Competitive Analysis", desc: "Framework for analyzing competitor landscape" },
];

export default function ResearchPage() {
  const data = useLeanOSData();

  const hasSources = data.research.sources.length > 0;
  const hasPlaybooks = data.research.playbooks.length > 0;
  const isEmpty = !hasSources && !hasPlaybooks;

  return (
    <div className="p-6 lg:p-8 bg-gray-50 min-h-screen">
      {/* Header */}
      <div className="mb-8">
        <h1 className="text-2xl font-bold text-gray-900">Research</h1>
        <p className="mt-1 text-sm font-medium text-gray-500">
          Knowledge sources and research playbooks that inform your strategy
        </p>
      </div>

      {/* Info banner */}
      <div className="mb-6 rounded-xl bg-purple-50 border border-purple-200 p-4">
        <div className="flex items-start gap-3">
          <Lightbulb02 className="h-5 w-5 text-purple-600 mt-0.5 flex-shrink-0" />
          <div>
            <p className="text-sm font-semibold text-purple-800">
              Research powers better decisions
            </p>
            <p className="mt-1 text-sm text-purple-700">
              Sources are external references LeanOS can cite. Playbooks are reusable research frameworks for market analysis, customer discovery, and more.
            </p>
          </div>
        </div>
      </div>

      {isEmpty ? (
        <div className="space-y-6">
          {/* Example Cards */}
          <div className="grid gap-6 lg:grid-cols-2">
            {/* Example Sources */}
            <div className="rounded-xl border-2 border-dashed border-purple-300 bg-white p-6">
              <div className="flex items-center gap-2 mb-4">
                <span className="rounded-full bg-purple-100 px-2.5 py-1 text-xs font-bold text-purple-700">
                  EXAMPLE
                </span>
                <span className="text-xs text-gray-500">Sources</span>
              </div>

              <div className="space-y-3">
                {EXAMPLE_SOURCES.map((source, i) => (
                  <div
                    key={i}
                    className="flex items-start gap-3 rounded-lg border border-gray-200 bg-gray-50 p-3"
                  >
                    <div className="flex h-8 w-8 items-center justify-center rounded-lg bg-purple-100 flex-shrink-0">
                      {source.type === "URL" ? <Link01 className="h-4 w-4 text-purple-600" /> :
                       source.type === "PDF" ? <File01 className="h-4 w-4 text-purple-600" /> :
                       <BookOpen01 className="h-4 w-4 text-purple-600" />}
                    </div>
                    <div>
                      <p className="text-sm font-medium text-gray-900">{source.name}</p>
                      <p className="text-xs text-gray-500">{source.desc}</p>
                    </div>
                  </div>
                ))}
              </div>
            </div>

            {/* Example Playbooks */}
            <div className="rounded-xl border-2 border-dashed border-orange-300 bg-white p-6">
              <div className="flex items-center gap-2 mb-4">
                <span className="rounded-full bg-orange-100 px-2.5 py-1 text-xs font-bold text-orange-700">
                  EXAMPLE
                </span>
                <span className="text-xs text-gray-500">Playbooks</span>
              </div>

              <div className="space-y-3">
                {EXAMPLE_PLAYBOOKS.map((playbook, i) => (
                  <div
                    key={i}
                    className="rounded-lg border border-gray-200 bg-gray-50 p-3 hover:bg-gray-100 transition-colors cursor-pointer"
                  >
                    <p className="text-sm font-medium text-gray-900">{playbook.name}</p>
                    <p className="text-xs text-gray-500 mt-0.5">{playbook.desc}</p>
                  </div>
                ))}
              </div>
            </div>
          </div>

          {/* Empty State CTA */}
          <div className="text-center py-12 rounded-xl border-2 border-dashed border-gray-300 bg-white">
            <div className="mx-auto mb-4 flex h-14 w-14 items-center justify-center rounded-full bg-gray-100">
              <BookOpen01 className="h-7 w-7 text-gray-400" />
            </div>
            <h3 className="text-lg font-semibold text-gray-900">Build Your Knowledge Base</h3>
            <p className="mt-2 text-sm text-gray-500 max-w-md mx-auto">
              Add sources and playbooks to give LeanOS context for better research and decision-making.
            </p>

            <div className="mt-6 grid gap-4 max-w-lg mx-auto sm:grid-cols-2">
              <div className="rounded-lg bg-purple-50 border border-purple-200 p-4 text-left">
                <div className="flex items-start gap-3">
                  <Terminal className="h-5 w-5 text-purple-600 mt-0.5 flex-shrink-0" />
                  <div>
                    <p className="text-sm font-semibold text-purple-800">Add sources</p>
                    <p className="mt-1 text-xs text-purple-700">
                      Run <code className="bg-purple-100 px-1 py-0.5 rounded font-mono">knowledge-builder</code> to add research sources
                    </p>
                  </div>
                </div>
              </div>

              <div className="rounded-lg bg-orange-50 border border-orange-200 p-4 text-left">
                <div className="flex items-start gap-3">
                  <Terminal className="h-5 w-5 text-orange-600 mt-0.5 flex-shrink-0" />
                  <div>
                    <p className="text-sm font-semibold text-orange-800">Run research</p>
                    <p className="mt-1 text-xs text-orange-700">
                      Run <code className="bg-orange-100 px-1 py-0.5 rounded font-mono">market-research</code> to start research
                    </p>
                  </div>
                </div>
              </div>
            </div>
          </div>
        </div>
      ) : (
        <div className="grid gap-6 lg:grid-cols-2">
          {/* Sources */}
          <div className="rounded-xl border-2 border-gray-200 bg-white p-6">
            <div className="flex items-center justify-between mb-4">
              <h2 className="text-lg font-bold text-gray-900">Sources</h2>
              <span className="rounded-full bg-purple-100 px-2.5 py-1 text-xs font-bold text-purple-700">
                {data.research.sources.length}
              </span>
            </div>
            {hasSources ? (
              <div className="space-y-3">
                {data.research.sources.map((source, i) => (
                  <div
                    key={i}
                    className="group flex items-start gap-3 rounded-lg border-2 border-gray-200 p-3 hover:border-purple-300 hover:bg-purple-50 transition-all cursor-pointer"
                  >
                    <div className="flex h-8 w-8 items-center justify-center rounded-lg bg-purple-100 flex-shrink-0">
                      <Link01 className="h-4 w-4 text-purple-600" />
                    </div>
                    <div className="flex-1">
                      <p className="text-sm font-medium text-gray-900 group-hover:text-purple-700">{String(source)}</p>
                    </div>
                    <ArrowRight className="h-4 w-4 text-gray-300 group-hover:text-purple-600 flex-shrink-0" />
                  </div>
                ))}
              </div>
            ) : (
              <div className="text-center py-8 rounded-lg border-2 border-dashed border-gray-200">
                <BookOpen01 className="h-8 w-8 mx-auto mb-2 text-gray-400" />
                <p className="text-sm font-medium text-gray-600">No sources yet</p>
                <p className="mt-1 text-xs text-gray-500">Run knowledge-builder to add sources</p>
              </div>
            )}
          </div>

          {/* Playbooks */}
          <div className="rounded-xl border-2 border-gray-200 bg-white p-6">
            <div className="flex items-center justify-between mb-4">
              <h2 className="text-lg font-bold text-gray-900">Playbooks</h2>
              <span className="rounded-full bg-orange-100 px-2.5 py-1 text-xs font-bold text-orange-700">
                {data.research.playbooks.length}
              </span>
            </div>
            {hasPlaybooks ? (
              <div className="space-y-3">
                {data.research.playbooks.map((playbook, i) => (
                  <div
                    key={i}
                    className="group rounded-lg border-2 border-gray-200 p-3 hover:border-orange-300 hover:bg-orange-50 transition-all cursor-pointer"
                  >
                    <div className="flex items-center justify-between">
                      <p className="text-sm font-medium text-gray-900 group-hover:text-orange-700">{String(playbook)}</p>
                      <ArrowRight className="h-4 w-4 text-gray-300 group-hover:text-orange-600 flex-shrink-0" />
                    </div>
                  </div>
                ))}
              </div>
            ) : (
              <div className="text-center py-8 rounded-lg border-2 border-dashed border-gray-200">
                <BookOpen01 className="h-8 w-8 mx-auto mb-2 text-gray-400" />
                <p className="text-sm font-medium text-gray-600">No playbooks yet</p>
                <p className="mt-1 text-xs text-gray-500">Run market-research to create playbooks</p>
              </div>
            )}
          </div>
        </div>
      )}
    </div>
  );
}
