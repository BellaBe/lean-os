"use client";

import { Announcement01, ArrowRight, Code02, File01, Folder, Package, ShoppingCart01, Terminal } from "@untitledui/icons";
import { useLeanOSData } from "@/providers/data-provider";
import { cx } from "@/utils/cx";

const ARTIFACT_CATEGORIES = [
    {
        name: "Sales",
        icon: ShoppingCart01,
        color: "blue",
        description: "Sales materials, proposals, and outreach templates",
        skill: "sales-execution",
    },
    {
        name: "Marketing",
        icon: Announcement01,
        color: "purple",
        description: "Content, campaigns, and brand assets",
        skill: "marketing-execution",
    },
    {
        name: "Engineering",
        icon: Code02,
        color: "green",
        description: "Technical specs, code, and documentation",
        skill: "product-builder",
    },
];

const COLOR_STYLES: Record<string, { bg: string; iconBg: string; text: string; border: string }> = {
    blue: { bg: "bg-blue-50", iconBg: "bg-blue-100", text: "text-blue-700", border: "border-blue-200" },
    purple: { bg: "bg-purple-50", iconBg: "bg-purple-100", text: "text-purple-700", border: "border-purple-200" },
    green: { bg: "bg-success-50", iconBg: "bg-success-100", text: "text-success-700", border: "border-success-200" },
};

export default function ArtifactsPage() {
    const data = useLeanOSData();

    return (
        <div className="min-h-screen bg-gray-50 p-6 lg:p-8">
            {/* Header */}
            <div className="mb-8">
                <h1 className="text-2xl font-bold text-gray-900">Artifacts</h1>
                <p className="mt-1 text-sm font-medium text-gray-500">Generated deliverables and outputs from LeanOS workflows</p>
            </div>

            {data.artifacts.length > 0 ? (
                <>
                    {/* Stats */}
                    <div className="mb-6 rounded-xl border-2 border-gray-200 bg-white p-5">
                        <div className="flex items-center gap-4">
                            <div className="flex h-12 w-12 items-center justify-center rounded-xl bg-brand-50">
                                <Package className="h-6 w-6 text-brand-600" />
                            </div>
                            <div>
                                <p className="text-2xl font-bold text-gray-900">{data.artifacts.length}</p>
                                <p className="text-sm font-medium text-gray-500">Total artifacts generated</p>
                            </div>
                        </div>
                    </div>

                    {/* Artifacts grid */}
                    <div className="grid gap-4 md:grid-cols-2 lg:grid-cols-3">
                        {data.artifacts.map((artifact, i) => (
                            <div
                                key={i}
                                className="group cursor-pointer rounded-xl border-2 border-gray-200 bg-white p-4 transition-all duration-200 hover:-translate-y-0.5 hover:border-brand-300 hover:shadow-md"
                            >
                                <div className="flex items-start gap-3">
                                    <div className="flex h-10 w-10 flex-shrink-0 items-center justify-center rounded-lg bg-gray-100">
                                        <File01 className="h-5 w-5 text-gray-600" />
                                    </div>
                                    <div className="min-w-0 flex-1">
                                        <p className="truncate text-sm font-medium text-gray-900 group-hover:text-brand-700">{String(artifact)}</p>
                                    </div>
                                    <ArrowRight className="h-4 w-4 flex-shrink-0 text-gray-300 transition-colors group-hover:text-brand-600" />
                                </div>
                            </div>
                        ))}
                    </div>
                </>
            ) : (
                <div className="space-y-6">
                    {/* Category Cards */}
                    <div className="grid gap-4 md:grid-cols-3">
                        {ARTIFACT_CATEGORIES.map((category) => {
                            const Icon = category.icon;
                            const colors = COLOR_STYLES[category.color];
                            return (
                                <div
                                    key={category.name}
                                    className={cx(
                                        "cursor-pointer rounded-xl border-2 p-5 transition-all duration-200 hover:-translate-y-0.5 hover:shadow-md",
                                        colors.border,
                                        colors.bg,
                                    )}
                                >
                                    <div className="flex items-start gap-3">
                                        <div className={cx("flex h-10 w-10 items-center justify-center rounded-lg", colors.iconBg)}>
                                            <Icon className={cx("h-5 w-5", colors.text)} />
                                        </div>
                                        <div className="flex-1">
                                            <h3 className={cx("text-base font-bold", colors.text)}>{category.name}</h3>
                                            <p className="mt-1 text-sm text-gray-600">{category.description}</p>
                                        </div>
                                    </div>
                                    <div className="mt-4 flex items-center gap-2">
                                        <Terminal className={cx("h-4 w-4", colors.text)} />
                                        <code className={cx("rounded px-1.5 py-0.5 font-mono text-xs", colors.iconBg, colors.text)}>{category.skill}</code>
                                    </div>
                                </div>
                            );
                        })}
                    </div>

                    {/* Empty State CTA */}
                    <div className="rounded-xl border-2 border-dashed border-gray-300 bg-white py-12 text-center">
                        <div className="mx-auto mb-4 flex h-14 w-14 items-center justify-center rounded-full bg-gray-100">
                            <Folder className="h-7 w-7 text-gray-400" />
                        </div>
                        <h3 className="text-lg font-semibold text-gray-900">No Artifacts Yet</h3>
                        <p className="mx-auto mt-2 max-w-md text-sm text-gray-500">
                            Artifacts are generated when you run execution skills. They include sales materials, marketing content, and engineering
                            deliverables.
                        </p>

                        <div className="mx-auto mt-6 max-w-md rounded-lg border border-brand-200 bg-brand-50 p-4">
                            <div className="flex items-start gap-3 text-left">
                                <Terminal className="mt-0.5 h-5 w-5 flex-shrink-0 text-brand-600" />
                                <div>
                                    <p className="text-sm font-semibold text-brand-800">Generate your first artifact</p>
                                    <p className="mt-1 text-sm text-brand-700">
                                        Run skills like <code className="rounded bg-brand-100 px-1 py-0.5 font-mono text-xs">sales-execution</code>,{" "}
                                        <code className="rounded bg-brand-100 px-1 py-0.5 font-mono text-xs">marketing-execution</code>, or{" "}
                                        <code className="rounded bg-brand-100 px-1 py-0.5 font-mono text-xs">product-builder</code> to create deliverables.
                                    </p>
                                </div>
                            </div>
                        </div>

                        <div className="mx-auto mt-6 max-w-lg border-t border-gray-200 pt-6">
                            <p className="text-xs text-gray-500">
                                <span className="font-medium">Artifacts are stored in:</span>{" "}
                                <code className="rounded bg-gray-100 px-1.5 py-0.5 font-mono">artifacts/</code> directory, organized by domain (sales/,
                                marketing/, engineering/)
                            </p>
                        </div>
                    </div>
                </div>
            )}
        </div>
    );
}
