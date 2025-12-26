import { Card, CardContent } from "@/components/ui/card";
import { Progress } from "@/components/ui/progress";
import fs from "fs";
import path from "path";

interface CanvasSection {
  number: string;
  name: string;
  status: string;
  summary?: string;
}

interface Canvas {
  mode: string;
  sections: CanvasSection[];
  health: number;
}

async function getData(): Promise<{ canvas: Canvas }> {
  const dataPath = path.join(process.cwd(), "public/data/leanos.json");
  try {
    const data = fs.readFileSync(dataPath, "utf-8");
    return JSON.parse(data);
  } catch {
    return { canvas: { mode: "VENTURE", sections: [], health: 0 } };
  }
}

export default async function CanvasPage() {
  const data = await getData();
  const { canvas } = data;

  const statusColors: Record<string, string> = {
    complete: "bg-green-500/20 border-green-500/30 text-green-400",
    draft: "bg-yellow-500/20 border-yellow-500/30 text-yellow-400",
    missing: "bg-red-500/20 border-red-500/30 text-red-400",
  };

  return (
    <div className="space-y-6">
      <div className="flex items-center justify-between">
        <div>
          <h1 className="text-2xl font-bold">Canvas</h1>
          <p className="text-text-tertiary">
            15-section Lean Canvas for strategic planning
          </p>
        </div>
        <div className="text-right">
          <div className="text-2xl font-bold">{canvas.health}%</div>
          <Progress value={canvas.health} className="w-32 h-2" />
        </div>
      </div>

      <div className="grid grid-cols-1 md:grid-cols-3 lg:grid-cols-5 gap-4">
        {canvas.sections.map((section) => (
          <Card
            key={section.number}
            className={`border ${statusColors[section.status] || ""}`}
          >
            <CardContent className="p-4">
              <div className="text-xs text-text-tertiary mb-1">
                {section.number}
              </div>
              <div className="font-medium text-sm">{section.name}</div>
              <div className="text-xs text-text-tertiary mt-2 capitalize">
                {section.status}
              </div>
              {section.summary && (
                <p className="text-xs mt-2 line-clamp-2 text-text-tertiary">
                  {section.summary}
                </p>
              )}
            </CardContent>
          </Card>
        ))}
      </div>
    </div>
  );
}
