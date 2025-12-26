import {
  Card,
  CardContent,
  CardHeader,
  CardTitle,
} from "@/components/ui/card";
import { Badge } from "@/components/base/badges/badges";
import { ProgressBarBase } from "@/components/base/progress-indicators/progress-indicators";
import {
  Target,
  Grid3X3,
  GitBranch,
  Zap,
  Sparkles,
} from "lucide-react";
import Link from "next/link";
import fs from "fs";
import path from "path";

// Canvas phases for logical grouping
const CANVAS_PHASES = [
  { id: "discovery", name: "Discovery", sections: ["01", "02", "03"], color: "blue" },
  { id: "problem", name: "Problem & Market", sections: ["04", "05", "06"], color: "purple" },
  { id: "solution", name: "Solution & Value", sections: ["07", "08", "09"], color: "brand" },
  { id: "validation", name: "Validation", sections: ["10"], color: "warning" },
  { id: "business", name: "Business Model", sections: ["11", "12", "13", "14", "15"], color: "success" },
] as const;

type CanvasSection = {
  number: string;
  name: string;
  status: string;
};

function getSectionsForPhase(sections: CanvasSection[], phaseId: string) {
  const phase = CANVAS_PHASES.find((p) => p.id === phaseId);
  if (!phase) return [];
  return sections
    .filter((s) => (phase.sections as readonly string[]).includes(s.number))
    .sort((a, b) => parseInt(a.number) - parseInt(b.number));
}

interface LeanOSData {
  goals: Array<{
    id: string;
    title: string;
    status: string;
    progress: number;
  }>;
  canvas: {
    mode: string;
    sections: Array<{
      number: string;
      name: string;
      status: string;
    }>;
    health: number;
  };
  threads: Array<{
    type: string;
    name: string;
    currentStage: number;
    goalId?: string;
  }>;
  skills: Array<{
    name: string;
    category: string;
  }>;
  agents: Array<{
    name: string;
  }>;
  meta: {
    lastBuilt: string;
  };
}

async function getData(): Promise<LeanOSData> {
  const dataPath = path.join(process.cwd(), "public/data/leanos.json");
  try {
    const data = fs.readFileSync(dataPath, "utf-8");
    return JSON.parse(data);
  } catch {
    return {
      goals: [],
      canvas: { mode: "VENTURE", sections: [], health: 0 },
      threads: [],
      skills: [],
      agents: [],
      meta: { lastBuilt: new Date().toISOString() },
    };
  }
}

// Stage names for better context
const STAGE_NAMES = ["Trigger", "Context", "Analysis", "Options", "Decision", "Outcome"];

// Get relative time string
function getRelativeTime(date: Date): string {
  const now = new Date();
  const diff = now.getTime() - date.getTime();
  const minutes = Math.floor(diff / 60000);
  const hours = Math.floor(diff / 3600000);
  const days = Math.floor(diff / 86400000);

  if (minutes < 1) return "just now";
  if (minutes < 60) return `${minutes}m ago`;
  if (hours < 24) return `${hours}h ago`;
  return `${days}d ago`;
}

export default async function Dashboard() {
  const data = await getData();

  const activeGoals = data.goals.filter((g) => g.status === "active");
  const activeThreads = data.threads.filter((t) => t.currentStage < 6);
  const completeSections = data.canvas.sections.filter(
    (s) => s.status === "complete"
  );
  const draftSections = data.canvas.sections.filter(
    (s) => s.status === "draft"
  );

  // Group skills by category with counts
  const skillsByCategory = data.skills.reduce((acc, skill) => {
    acc[skill.category] = (acc[skill.category] || 0) + 1;
    return acc;
  }, {} as Record<string, number>);

  const sortedCategories = Object.entries(skillsByCategory)
    .sort((a, b) => b[1] - a[1]);

  // Calculate health status
  const healthStatus = data.canvas.health >= 80 ? "healthy" : data.canvas.health >= 50 ? "warning" : "critical";

  // Check if this is a fresh/empty state
  const isEmpty = data.goals.length === 0 && data.threads.length === 0 && completeSections.length === 0;

  return (
    <div className="min-h-screen">
      {/* Page Header */}
      <header className="mb-8">
        <div className="flex items-start justify-between">
          <div className="space-y-1">
            <h1 className="text-2xl font-semibold text-text-primary">
              Dashboard
            </h1>
            <p className="text-text-tertiary text-sm">
              Your operating system at a glance
            </p>
          </div>
          <div className="flex items-center gap-4">
            <span className="text-xs text-text-tertiary">
              Updated {getRelativeTime(new Date(data.meta.lastBuilt))}
            </span>
            <Badge type="modern" size="lg">
              {data.canvas.mode} Mode
            </Badge>
          </div>
        </div>
      </header>

      {/* Empty State - Onboarding */}
      {isEmpty ? (
        <EmptyDashboard />
      ) : (
        <>
          {/* Metrics */}
          <section className="mb-8">
            <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-4 gap-4">
              <MetricCard
                href="/goals"
                icon={Target}
                label="Active Goals"
                value={activeGoals.length}
                subtext={`${data.goals.length} total`}
                accentColor="brand"
              />
              <MetricCard
                href="/canvas"
                icon={Grid3X3}
                label="Canvas Health"
                value={`${data.canvas.health}%`}
                subtext={`${completeSections.length} complete, ${draftSections.length} draft`}
                accentColor="success"
              />
              <MetricCard
                href="/threads"
                icon={GitBranch}
                label="Active Threads"
                value={activeThreads.length}
                subtext={`${data.threads.length} total`}
                accentColor="blue"
              />
              <MetricCard
                href="/skills"
                icon={Zap}
                label="Capabilities"
                value={data.skills.length}
                subtext={`${data.agents.length} agents`}
                accentColor="purple"
              />
            </div>
          </section>

          {/* Main Content Grid - Equal columns */}
          <div className="grid grid-cols-1 lg:grid-cols-2 gap-6">
            {/* Left Column */}
            <div className="space-y-6">
              {/* Active Threads */}
              <Card>
                <CardHeader className="border-b border-border-secondary pb-4">
                  <div className="flex items-center justify-between">
                    <CardTitle className="text-base font-semibold">Active Threads</CardTitle>
                    <Link
                      href="/threads"
                      className="text-sm text-text-tertiary hover:text-text-primary transition-colors"
                    >
                      View all
                    </Link>
                  </div>
                </CardHeader>
                <CardContent className="pt-4">
                  {activeThreads.length === 0 ? (
                    <EmptyThreadsState />
                  ) : (
                    <div className="space-y-1">
                      {activeThreads.slice(0, 5).map((thread, index) => (
                        <ThreadItem
                          key={`${thread.type}/${thread.name}`}
                          thread={thread}
                          isFirst={index === 0}
                        />
                      ))}
                    </div>
                  )}
                </CardContent>
              </Card>

              {/* Canvas Status */}
              <Card>
                <CardHeader className="border-b border-border-secondary pb-4">
                  <div className="flex items-center justify-between">
                    <CardTitle className="text-base font-semibold">Canvas Status</CardTitle>
                    <Link
                      href="/canvas"
                      className="text-sm text-text-tertiary hover:text-text-primary transition-colors"
                    >
                      View all
                    </Link>
                  </div>
                </CardHeader>
                <CardContent className="pt-4">
                  {data.canvas.sections.length === 0 ? (
                    <EmptyCanvasState />
                  ) : (
                    <div className="space-y-3">
                      {CANVAS_PHASES.map((phase) => {
                        const phaseSections = getSectionsForPhase(data.canvas.sections, phase.id);
                        const complete = phaseSections.filter((s) => s.status === "complete").length;
                        const total = phaseSections.length;

                        return (
                          <div key={phase.id} className="flex items-center gap-4">
                            <span className="text-sm text-text-primary w-32 truncate">
                              {phase.name}
                            </span>
                            <div className="flex-1 flex gap-1">
                              {phaseSections.map((section) => (
                                <div
                                  key={section.number}
                                  className={`flex-1 h-2 rounded-full ${
                                    section.status === "complete"
                                      ? "bg-fg-success-primary"
                                      : section.status === "draft"
                                      ? "bg-fg-warning-primary"
                                      : "bg-bg-quaternary"
                                  }`}
                                  title={`${section.number}. ${section.name}`}
                                />
                              ))}
                            </div>
                            <span className="text-xs text-text-tertiary tabular-nums w-8 text-right">
                              {complete}/{total}
                            </span>
                          </div>
                        );
                      })}
                    </div>
                  )}
                </CardContent>
              </Card>
            </div>

            {/* Right Column */}
            <div className="space-y-6">
              {/* Goals */}
              <Card>
                <CardHeader className="border-b border-border-secondary pb-4">
                  <div className="flex items-center justify-between">
                    <CardTitle className="text-base font-semibold">Goals</CardTitle>
                    <Link
                      href="/goals"
                      className="text-sm text-text-tertiary hover:text-text-primary transition-colors"
                    >
                      View all
                    </Link>
                  </div>
                </CardHeader>
                <CardContent className="pt-4">
                  {activeGoals.length === 0 ? (
                    <EmptyGoalsState />
                  ) : (
                    <div className="space-y-1">
                      {activeGoals.slice(0, 4).map((goal) => (
                        <div
                          key={goal.id}
                          className="flex items-center justify-between px-4 py-3 -mx-4 rounded-lg hover:bg-bg-primary_hover transition-colors cursor-pointer"
                        >
                          <span className="text-sm text-text-primary truncate flex-1 mr-3">
                            {goal.title}
                          </span>
                          <div className="flex items-center gap-3">
                            <div className="w-16">
                              <ProgressBarBase value={goal.progress} className="h-1.5" />
                            </div>
                            <span className="text-xs text-text-tertiary tabular-nums w-8">
                              {goal.progress}%
                            </span>
                          </div>
                        </div>
                      ))}
                    </div>
                  )}
                </CardContent>
              </Card>

              {/* Skills */}
              <Card>
                <CardHeader className="border-b border-border-secondary pb-4">
                  <div className="flex items-center justify-between">
                    <CardTitle className="text-base font-semibold">Skills</CardTitle>
                    <Link
                      href="/skills"
                      className="text-sm text-text-tertiary hover:text-text-primary transition-colors"
                    >
                      View all
                    </Link>
                  </div>
                </CardHeader>
                <CardContent className="pt-4">
                  {sortedCategories.length === 0 ? (
                    <EmptySkillsState />
                  ) : (
                    <div className="space-y-1">
                      {sortedCategories.slice(0, 6).map(([category, count]) => (
                        <div
                          key={category}
                          className="flex items-center justify-between px-4 py-2.5 -mx-4 rounded-lg hover:bg-bg-primary_hover transition-colors cursor-pointer"
                        >
                          <span className="text-sm text-text-primary capitalize">
                            {category.replace(/-/g, " ")}
                          </span>
                          <span className="text-xs text-text-tertiary tabular-nums">
                            {count}
                          </span>
                        </div>
                      ))}
                    </div>
                  )}
                </CardContent>
              </Card>

              {/* Agents */}
              <Card>
                <CardHeader className="border-b border-border-secondary pb-4">
                  <CardTitle className="text-base font-semibold">Agents</CardTitle>
                </CardHeader>
                <CardContent className="pt-4">
                  {data.agents.length === 0 ? (
                    <EmptyAgentsState />
                  ) : (
                    <div className="flex flex-wrap gap-2">
                      {data.agents.map((agent) => (
                        <Badge key={agent.name} type="modern" size="sm">
                          {agent.name}
                        </Badge>
                      ))}
                    </div>
                  )}
                </CardContent>
              </Card>
            </div>
          </div>
        </>
      )}
    </div>
  );
}

// ============================================================================
// COMPONENT: MetricCard
// ============================================================================
interface MetricCardProps {
  href: string;
  icon: React.ElementType;
  label: string;
  value: string | number;
  subtext: string;
  accentColor: "brand" | "success" | "warning" | "error" | "blue" | "purple";
}

function MetricCard({ href, icon: Icon, label, value, subtext, accentColor }: MetricCardProps) {
  const colorMap = {
    brand: "var(--color-brand-500)",
    success: "var(--color-success-500)",
    warning: "var(--color-warning-500)",
    error: "var(--color-error-500)",
    blue: "var(--color-blue-500)",
    purple: "var(--color-brand-500)",
  };

  return (
    <Link href={href}>
      <Card hover>
        <CardContent className="p-5">
          <div className="flex items-start justify-between">
            <div className="space-y-1">
              <p className="text-sm text-text-tertiary">{label}</p>
              <p className="text-2xl font-semibold tabular-nums">{value}</p>
              <p className="text-xs text-text-tertiary">{subtext}</p>
            </div>
            <div
              className="p-2 rounded-lg"
              style={{
                backgroundColor: `color-mix(in srgb, ${colorMap[accentColor]} 15%, transparent)`,
              }}
            >
              <Icon
                className="w-5 h-5"
                style={{ color: colorMap[accentColor] }}
              />
            </div>
          </div>
        </CardContent>
      </Card>
    </Link>
  );
}

// ============================================================================
// COMPONENT: ThreadItem
// ============================================================================
interface ThreadItemProps {
  thread: {
    type: string;
    name: string;
    currentStage: number;
    goalId?: string;
  };
  isFirst: boolean;
}

function ThreadItem({ thread, isFirst }: ThreadItemProps) {
  const currentStageName = STAGE_NAMES[thread.currentStage - 1] || "Starting";
  const progressPercent = ((thread.currentStage) / 6) * 100;

  return (
    <div className="flex items-center justify-between px-4 py-3 -mx-4 rounded-lg hover:bg-bg-primary_hover transition-colors cursor-pointer">
      <div className="flex-1 min-w-0">
        <div className="flex items-center gap-2 mb-1">
          <span className="text-sm font-medium text-text-primary truncate">
            {thread.name}
          </span>
          {isFirst && (
            <Badge color="brand" size="sm">
              Current
            </Badge>
          )}
        </div>
        <div className="flex items-center gap-2 text-xs text-text-tertiary">
          <span className="capitalize">{thread.type}</span>
          <span>•</span>
          <span>Stage {thread.currentStage}: {currentStageName}</span>
        </div>
      </div>
      <div className="flex items-center gap-3">
        <div className="w-16">
          <ProgressBarBase value={progressPercent} className="h-1.5" />
        </div>
        <span className="text-xs text-text-tertiary tabular-nums w-8">
          {thread.currentStage}/6
        </span>
      </div>
    </div>
  );
}

// ============================================================================
// EMPTY STATES
// ============================================================================

function EmptyDashboard() {
  return (
    <div className="flex flex-col items-center justify-center py-16 px-4">
      <div className="w-16 h-16 rounded-2xl bg-bg-brand-secondary flex items-center justify-center mb-6">
        <Sparkles className="w-8 h-8 text-fg-brand-primary" />
      </div>
      <h2 className="text-xl font-semibold text-text-primary mb-2">
        Welcome to LeanOS
      </h2>
      <p className="text-text-tertiary text-center max-w-md mb-8">
        Your operating system is ready. Start by defining your business context and creating your first goal.
      </p>
      <div className="flex flex-col sm:flex-row gap-3">
        <Link
          href="/canvas"
          className="inline-flex items-center justify-center gap-2 px-4 py-2.5 text-sm font-medium rounded-lg bg-primary text-primary-foreground hover:bg-primary/90 transition-colors"
        >
          <Grid3X3 className="w-4 h-4" />
          Set up Canvas
        </Link>
        <Link
          href="/goals/new"
          className="inline-flex items-center justify-center gap-2 px-4 py-2.5 text-sm font-medium rounded-lg border border-border-secondary hover:bg-bg-primary_hover transition-colors"
        >
          <Target className="w-4 h-4" />
          Create a Goal
        </Link>
      </div>
    </div>
  );
}

function EmptyThreadsState() {
  return (
    <div className="flex flex-col items-center justify-center py-8 text-center">
      <div className="w-12 h-12 rounded-xl bg-bg-secondary flex items-center justify-center mb-4">
        <GitBranch className="w-6 h-6 text-text-tertiary" />
      </div>
      <p className="text-sm font-medium text-text-primary mb-1">No active threads</p>
      <p className="text-xs text-text-tertiary max-w-xs">
        Threads are created automatically when you start working on goals. Create a goal to get started.
      </p>
    </div>
  );
}

function EmptyCanvasState() {
  return (
    <div className="flex flex-col items-center justify-center py-8 text-center">
      <div className="w-12 h-12 rounded-xl bg-bg-secondary flex items-center justify-center mb-4">
        <Grid3X3 className="w-6 h-6 text-text-tertiary" />
      </div>
      <p className="text-sm font-medium text-text-primary mb-1">Canvas not configured</p>
      <p className="text-xs text-text-tertiary max-w-xs mb-4">
        Set up your strategy canvas to define your business context, problems, and solutions.
      </p>
      <Link
        href="/canvas"
        className="text-sm text-primary hover:text-primary/80 font-medium transition-colors"
      >
        Configure Canvas
      </Link>
    </div>
  );
}

function EmptyGoalsState() {
  return (
    <div className="flex flex-col items-center justify-center py-6 text-center">
      <div className="w-10 h-10 rounded-lg bg-bg-secondary flex items-center justify-center mb-3">
        <Target className="w-5 h-5 text-text-tertiary" />
      </div>
      <p className="text-sm font-medium text-text-primary mb-1">No active goals</p>
      <p className="text-xs text-text-tertiary mb-3">
        Goals drive your work forward.
      </p>
      <Link
        href="/goals/new"
        className="text-xs text-primary hover:text-primary/80 font-medium transition-colors"
      >
        Create your first goal
      </Link>
    </div>
  );
}

function EmptySkillsState() {
  return (
    <div className="flex flex-col items-center justify-center py-6 text-center">
      <div className="w-10 h-10 rounded-lg bg-bg-secondary flex items-center justify-center mb-3">
        <Zap className="w-5 h-5 text-text-tertiary" />
      </div>
      <p className="text-sm text-text-tertiary">
        No skills configured
      </p>
    </div>
  );
}

function EmptyAgentsState() {
  return (
    <div className="flex flex-col items-center justify-center py-6 text-center">
      <div className="w-10 h-10 rounded-lg bg-bg-secondary flex items-center justify-center mb-3">
        <Sparkles className="w-5 h-5 text-text-tertiary" />
      </div>
      <p className="text-sm text-text-tertiary">
        No agents available
      </p>
    </div>
  );
}
