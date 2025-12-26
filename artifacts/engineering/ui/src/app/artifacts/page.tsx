import { Card, CardContent } from "@/components/ui/card";
import { FolderOpen, FileText } from "lucide-react";

export default function ArtifactsPage() {
  const directories = [
    { name: "engineering", description: "Code, specs, configs, proofs" },
    { name: "sales", description: "Pitch decks, scripts, templates" },
    { name: "marketing", description: "Campaigns, content, analytics" },
    { name: "operations", description: "SOPs, runbooks, processes" },
  ];

  return (
    <div className="space-y-6">
      <div>
        <h1 className="text-2xl font-bold">Artifacts</h1>
        <p className="text-text-tertiary">
          Generated deliverables by domain
        </p>
      </div>

      <div className="grid grid-cols-1 md:grid-cols-2 gap-4">
        {directories.map((dir) => (
          <Card key={dir.name} className="hover:bg-accent/50 transition-colors cursor-pointer">
            <CardContent className="p-6">
              <div className="flex items-center gap-4">
                <div className="w-12 h-12 rounded-lg bg-bg-primary/10 flex items-center justify-center">
                  <FolderOpen className="w-6 h-6 text-primary" />
                </div>
                <div>
                  <h3 className="font-semibold capitalize">{dir.name}</h3>
                  <p className="text-sm text-text-tertiary">{dir.description}</p>
                </div>
              </div>
            </CardContent>
          </Card>
        ))}
      </div>

      <Card>
        <CardContent className="p-6 text-center text-text-tertiary">
          <FileText className="w-8 h-8 mx-auto mb-2 opacity-50" />
          <p>Artifact browser coming in Phase 4</p>
          <p className="text-sm mt-1">
            Browse files in <code>artifacts/</code>
          </p>
        </CardContent>
      </Card>
    </div>
  );
}
