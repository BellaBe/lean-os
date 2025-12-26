import { Card, CardContent, CardHeader, CardTitle } from "@/components/ui/card";
import { Badge } from "@/components/ui/badge";
import fs from "fs";
import path from "path";

interface Goal {
  id: string;
  title: string;
  type: string;
  status: string;
  autonomy: string;
  objective: string;
  progress: number;
}

async function getData(): Promise<{ goals: Goal[] }> {
  const dataPath = path.join(process.cwd(), "public/data/leanos.json");
  try {
    const data = fs.readFileSync(dataPath, "utf-8");
    return JSON.parse(data);
  } catch {
    return { goals: [] };
  }
}

export default async function GoalsPage() {
  const data = await getData();

  const autonomyColors: Record<string, string> = {
    auto: "bg-green-500/10 text-green-500",
    ask: "bg-yellow-500/10 text-yellow-500",
    hybrid: "bg-blue-500/10 text-blue-500",
  };

  return (
    <div className="space-y-6">
      <div>
        <h1 className="text-2xl font-bold">Goals</h1>
        <p className="text-text-tertiary">
          Track and manage your objectives
        </p>
      </div>

      {data.goals.length === 0 ? (
        <Card>
          <CardContent className="p-6 text-center text-text-tertiary">
            <p>No goals found.</p>
            <p className="text-sm mt-2">
              Create goals in <code>strategy/goals/active/</code>
            </p>
          </CardContent>
        </Card>
      ) : (
        <div className="grid grid-cols-1 md:grid-cols-2 gap-4">
          {data.goals.map((goal) => (
            <Card key={goal.id}>
              <CardHeader className="pb-2">
                <div className="flex items-center justify-between">
                  <CardTitle className="text-base">{goal.title}</CardTitle>
                  <Badge
                    variant="outline"
                    className={autonomyColors[goal.autonomy] || ""}
                  >
                    {goal.autonomy}
                  </Badge>
                </div>
              </CardHeader>
              <CardContent>
                <p className="text-sm text-text-tertiary line-clamp-2">
                  {goal.objective || "No objective specified"}
                </p>
                <div className="flex items-center gap-2 mt-3">
                  <Badge variant="secondary">{goal.type}</Badge>
                  <Badge variant="outline">{goal.status}</Badge>
                </div>
              </CardContent>
            </Card>
          ))}
        </div>
      )}
    </div>
  );
}
