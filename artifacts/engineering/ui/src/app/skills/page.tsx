"use client";

import { useState } from "react";
import { useLeanOSData } from "@/providers/data-provider";
import { getSkillCategories } from "@/lib/data";
import { cx } from "@/utils/cx";
import { Zap, SearchLg, ChevronDown, ChevronUp } from "@untitledui/icons";

function SkillCard({ skill }: { skill: { name: string; purpose: string; category: string } }) {
  const [isExpanded, setIsExpanded] = useState(false);
  const hasLongDescription = skill.purpose && skill.purpose.length > 80;

  return (
    <div
      className={cx(
        "group rounded-xl border-2 bg-white p-4 transition-all duration-200",
        "border-gray-200 hover:border-brand-300 hover:shadow-md hover:-translate-y-0.5",
        hasLongDescription && "cursor-pointer"
      )}
      onClick={() => hasLongDescription && setIsExpanded(!isExpanded)}
    >
      <div className="flex items-start gap-3">
        <div className="flex h-10 w-10 items-center justify-center rounded-xl bg-purple-50 shrink-0 transition-transform group-hover:scale-105">
          <Zap className="h-5 w-5 text-purple-600" />
        </div>
        <div className="min-w-0 flex-1">
          <h3 className="text-sm font-semibold text-gray-900">
            {skill.name}
          </h3>
          {skill.purpose && (
            <p className={cx(
              "mt-1.5 text-sm text-gray-600 leading-relaxed",
              !isExpanded && hasLongDescription && "line-clamp-2"
            )}>
              {skill.purpose}
            </p>
          )}
          {hasLongDescription && (
            <button
              className={cx(
                "mt-3 inline-flex items-center gap-1.5 rounded-lg px-3 py-1.5 text-xs font-semibold transition-all",
                isExpanded
                  ? "bg-gray-100 text-gray-700 hover:bg-gray-200"
                  : "bg-brand-50 text-brand-700 hover:bg-brand-100 border border-brand-200"
              )}
              onClick={(e) => {
                e.stopPropagation();
                setIsExpanded(!isExpanded);
              }}
            >
              {isExpanded ? (
                <>Show less <ChevronUp className="h-3.5 w-3.5" /></>
              ) : (
                <>Show more <ChevronDown className="h-3.5 w-3.5" /></>
              )}
            </button>
          )}
        </div>
      </div>
    </div>
  );
}

export default function SkillsPage() {
  const data = useLeanOSData();
  const categories = getSkillCategories(data.skills);
  const [activeCategory, setActiveCategory] = useState<string | null>(null);
  const [searchQuery, setSearchQuery] = useState("");

  const filteredSkills = data.skills.filter((skill) => {
    const matchesCategory = !activeCategory || skill.category === activeCategory;
    const matchesSearch =
      !searchQuery ||
      skill.name.toLowerCase().includes(searchQuery.toLowerCase()) ||
      skill.purpose.toLowerCase().includes(searchQuery.toLowerCase());
    return matchesCategory && matchesSearch;
  });

  // Group skills by category for display
  const groupedSkills = filteredSkills.reduce((acc, skill) => {
    if (!acc[skill.category]) {
      acc[skill.category] = [];
    }
    acc[skill.category].push(skill);
    return acc;
  }, {} as Record<string, typeof data.skills>);

  return (
    <div className="p-6 lg:p-8 bg-gray-50 min-h-screen">
      {/* Header */}
      <div className="mb-8">
        <h1 className="text-2xl font-bold text-gray-900">Skills</h1>
        <p className="mt-1 text-sm font-medium text-gray-500">
          {data.skills.length} AI-powered capabilities across{" "}
          {categories.length} categories
        </p>
      </div>

      {/* Search */}
      <div className="mb-6">
        <div className="relative">
          <SearchLg className="absolute left-3 top-1/2 -translate-y-1/2 h-5 w-5 text-gray-400" />
          <input
            type="text"
            placeholder="Search skills by name or description..."
            value={searchQuery}
            onChange={(e) => setSearchQuery(e.target.value)}
            className="w-full rounded-xl border-2 border-gray-200 bg-white pl-10 pr-4 py-3 text-sm text-gray-900 placeholder:text-gray-400 focus:border-brand-500 focus:outline-none focus:ring-2 focus:ring-brand-100 transition-all"
          />
        </div>
      </div>

      {/* Category Filter */}
      <div className="mb-6 flex flex-wrap items-center gap-2">
        <button
          onClick={() => setActiveCategory(null)}
          className={cx(
            "rounded-full px-4 py-2 text-sm font-semibold transition-all duration-200",
            activeCategory === null
              ? "bg-brand-600 text-white shadow-sm"
              : "bg-white border-2 border-gray-200 text-gray-700 hover:border-brand-300 hover:bg-brand-50"
          )}
        >
          All ({data.skills.length})
        </button>
        {categories.map((category) => {
          const count = data.skills.filter((s) => s.category === category).length;
          return (
            <button
              key={category}
              onClick={() => setActiveCategory(category)}
              className={cx(
                "rounded-full px-4 py-2 text-sm font-semibold transition-all duration-200 capitalize",
                activeCategory === category
                  ? "bg-brand-600 text-white shadow-sm"
                  : "bg-white border-2 border-gray-200 text-gray-700 hover:border-brand-300 hover:bg-brand-50"
              )}
            >
              {category} ({count})
            </button>
          );
        })}
      </div>

      {/* Skills Grid */}
      {Object.keys(groupedSkills).length > 0 ? (
        <div className="space-y-8">
          {Object.entries(groupedSkills)
            .sort(([a], [b]) => a.localeCompare(b))
            .map(([category, skills]) => (
              <div key={category}>
                <div className="flex items-center gap-3 mb-4">
                  <h2 className="text-lg font-bold text-gray-900 capitalize">
                    {category}
                  </h2>
                  <span className="rounded-full bg-gray-100 px-2.5 py-1 text-xs font-semibold text-gray-600">
                    {skills.length}
                  </span>
                </div>
                <div className="grid gap-4 md:grid-cols-2 lg:grid-cols-3">
                  {skills.map((skill) => (
                    <SkillCard key={skill.name} skill={skill} />
                  ))}
                </div>
              </div>
            ))}
        </div>
      ) : (
        <div className="text-center py-16 rounded-xl border-2 border-dashed border-gray-300 bg-white">
          <div className="mx-auto mb-4 flex h-14 w-14 items-center justify-center rounded-full bg-gray-100">
            <SearchLg className="h-7 w-7 text-gray-400" />
          </div>
          <h3 className="text-lg font-semibold text-gray-900">
            No skills match "{searchQuery || activeCategory}"
          </h3>
          <p className="mt-2 text-sm text-gray-500 max-w-md mx-auto">
            {searchQuery
              ? "Try different keywords or check your spelling."
              : `No skills in the "${activeCategory}" category.`}
          </p>

          {/* Suggestions */}
          <div className="mt-6 p-4 bg-gray-50 rounded-lg max-w-md mx-auto">
            <p className="text-xs font-medium text-gray-600 mb-3">Try searching for:</p>
            <div className="flex flex-wrap justify-center gap-2">
              {["marketing", "sales", "product", "research", "engineering"].map((term) => (
                <button
                  key={term}
                  onClick={() => {
                    setSearchQuery(term);
                    setActiveCategory(null);
                  }}
                  className="rounded-full bg-white border border-gray-200 px-3 py-1 text-xs font-medium text-gray-700 hover:border-brand-300 hover:bg-brand-50 transition-colors"
                >
                  {term}
                </button>
              ))}
            </div>
          </div>

          <div className="mt-4 flex items-center justify-center gap-3">
            {searchQuery && (
              <button
                onClick={() => setSearchQuery("")}
                className="inline-flex items-center rounded-lg bg-brand-600 px-4 py-2 text-sm font-semibold text-white hover:bg-brand-700 transition-colors"
              >
                Clear search
              </button>
            )}
            {activeCategory && (
              <button
                onClick={() => setActiveCategory(null)}
                className="inline-flex items-center rounded-lg bg-gray-100 px-4 py-2 text-sm font-semibold text-gray-700 hover:bg-gray-200 transition-colors"
              >
                View all skills
              </button>
            )}
          </div>
        </div>
      )}
    </div>
  );
}
