"use client";

import { useState } from "react";
import { useLeanOSData } from "@/providers/data-provider";
import { Users01, ChevronDown, ChevronUp, Zap } from "@untitledui/icons";
import { cx } from "@/utils/cx";
import Link from "next/link";

function AgentCard({ agent }: { agent: { name: string; purpose: string; skills: string[] } }) {
  const [isExpanded, setIsExpanded] = useState(false);
  const hasLongDescription = agent.purpose && agent.purpose.length > 80;
  const hasMoreSkills = agent.skills.length > 4;
  const needsExpansion = hasLongDescription || hasMoreSkills;

  return (
    <div
      className={cx(
        "group rounded-xl border-2 bg-white p-5 transition-all duration-200",
        "border-gray-200 hover:border-brand-300 hover:shadow-md hover:-translate-y-0.5"
      )}
    >
      <div className="flex items-start gap-4">
        <div className="flex h-12 w-12 items-center justify-center rounded-xl bg-brand-50 shrink-0 group-hover:scale-105 transition-transform">
          <Users01 className="h-6 w-6 text-brand-600" />
        </div>
        <div className="min-w-0 flex-1">
          <h3 className="text-base font-bold text-gray-900">
            {agent.name}
          </h3>
          {agent.purpose && (
            <p className={cx(
              "mt-1.5 text-sm text-gray-600 leading-relaxed",
              !isExpanded && hasLongDescription && "line-clamp-2"
            )}>
              {agent.purpose}
            </p>
          )}
        </div>
      </div>

      {/* Skills section */}
      {agent.skills.length > 0 && (
        <div className="mt-4 pt-4 border-t border-gray-100">
          <div className="flex items-center gap-2 mb-2">
            <Zap className="h-3.5 w-3.5 text-gray-400" />
            <span className="text-xs font-medium text-gray-500">Available Skills</span>
          </div>
          <div className="flex flex-wrap gap-1.5">
            {agent.skills.slice(0, isExpanded ? undefined : 4).map((skill) => (
              <span
                key={skill}
                className="rounded-md bg-gray-100 px-2 py-1 text-xs font-medium text-gray-700"
              >
                {skill}
              </span>
            ))}
            {hasMoreSkills && !isExpanded && (
              <span className="rounded-md bg-gray-50 px-2 py-1 text-xs font-medium text-gray-500">
                +{agent.skills.length - 4}
              </span>
            )}
          </div>
        </div>
      )}

      {/* Expand/Collapse button */}
      {needsExpansion && (
        <div className="mt-4 pt-3 border-t border-gray-100">
          <button
            onClick={() => setIsExpanded(!isExpanded)}
            className={cx(
              "w-full inline-flex items-center justify-center gap-1.5 rounded-lg px-3 py-2 text-xs font-semibold transition-all",
              isExpanded
                ? "bg-gray-100 text-gray-700 hover:bg-gray-200"
                : "bg-brand-50 text-brand-700 hover:bg-brand-100 border border-brand-200"
            )}
          >
            {isExpanded ? (
              <>Collapse <ChevronUp className="h-3.5 w-3.5" /></>
            ) : (
              <>View full details <ChevronDown className="h-3.5 w-3.5" /></>
            )}
          </button>
        </div>
      )}
    </div>
  );
}

export default function AgentsPage() {
  const data = useLeanOSData();

  return (
    <div className="p-6 lg:p-8 bg-gray-50 min-h-screen">
      {/* Header */}
      <div className="mb-8">
        <h1 className="text-2xl font-bold text-gray-900">Agents</h1>
        <p className="mt-1 text-sm font-medium text-gray-500">
          {data.agents.length} orchestrator agents that coordinate skills for complex workflows
        </p>
      </div>

      {/* Info banner */}
      <div className="mb-6 rounded-xl bg-brand-50 border border-brand-200 p-4">
        <p className="text-sm text-brand-800">
          <span className="font-semibold">Agents</span> are specialized orchestrators that route multiple skills to handle domain-specific tasks.
          Each agent can access a curated set of skills for its domain.
        </p>
      </div>

      {data.agents.length > 0 ? (
        <div className="grid gap-4 md:grid-cols-2 lg:grid-cols-3">
          {data.agents.map((agent) => (
            <AgentCard key={agent.name} agent={agent} />
          ))}
        </div>
      ) : (
        <div className="text-center py-16 rounded-xl border-2 border-dashed border-gray-300 bg-white">
          <div className="mx-auto mb-4 flex h-14 w-14 items-center justify-center rounded-full bg-gray-100">
            <Users01 className="h-7 w-7 text-gray-400" />
          </div>
          <h3 className="text-lg font-semibold text-gray-900">No agents configured</h3>
          <p className="mt-2 text-sm text-gray-500 max-w-md mx-auto">
            Agents are defined in <code className="bg-gray-100 px-1.5 py-0.5 rounded text-xs">.claude/agents/</code> directory.
            They orchestrate skills for specific domains like sales, marketing, or engineering.
          </p>
          <div className="mt-6 flex items-center justify-center gap-3">
            <Link
              href="/skills"
              className="inline-flex items-center rounded-lg bg-brand-600 px-4 py-2 text-sm font-semibold text-white hover:bg-brand-700 transition-colors"
            >
              Browse Skills Instead
            </Link>
          </div>
        </div>
      )}
    </div>
  );
}
