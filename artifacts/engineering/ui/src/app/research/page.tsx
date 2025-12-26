import { Card, CardContent } from "@/components/ui/card";
import { BookOpen, FileText, Users } from "lucide-react";

export default function ResearchPage() {
  const sections = [
    {
      name: "Sources",
      icon: BookOpen,
      description: "Processed expert content (videos, podcasts, articles)",
      path: "research/sources/",
    },
    {
      name: "Playbooks",
      icon: FileText,
      description: "Actionable operational guides",
      path: "research/playbooks/",
    },
    {
      name: "Customer Research",
      icon: Users,
      description: "ICPs, prospects, insights",
      path: "research/customer/",
    },
  ];

  return (
    <div className="space-y-6">
      <div>
        <h1 className="text-2xl font-bold">Research</h1>
        <p className="text-text-tertiary">
          Knowledge base and market intelligence
        </p>
      </div>

      <div className="grid grid-cols-1 md:grid-cols-3 gap-4">
        {sections.map((section) => {
          const Icon = section.icon;
          return (
            <Card key={section.name} className="hover:bg-accent/50 transition-colors cursor-pointer">
              <CardContent className="p-6">
                <div className="w-10 h-10 rounded-lg bg-bg-primary/10 flex items-center justify-center mb-3">
                  <Icon className="w-5 h-5 text-primary" />
                </div>
                <h3 className="font-semibold">{section.name}</h3>
                <p className="text-sm text-text-tertiary mt-1">
                  {section.description}
                </p>
                <p className="text-xs text-text-tertiary mt-2">
                  <code>{section.path}</code>
                </p>
              </CardContent>
            </Card>
          );
        })}
      </div>

      <Card>
        <CardContent className="p-6 text-center text-text-tertiary">
          <BookOpen className="w-8 h-8 mx-auto mb-2 opacity-50" />
          <p>Research browser coming in Phase 4</p>
        </CardContent>
      </Card>
    </div>
  );
}
