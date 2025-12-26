import { Card, CardContent, CardHeader, CardTitle } from "@/components/ui/card";
import { Badge } from "@/components/ui/badge";
import fs from "fs";
import path from "path";

interface Thread {
  type: string;
  name: string;
  currentStage: number;
  goalId?: string;
}

async function getData(): Promise<{ threads: Thread[] }> {
  const dataPath = path.join(process.cwd(), "public/data/leanos.json");
  try {
    const data = fs.readFileSync(dataPath, "utf-8");
    return JSON.parse(data);
  } catch {
    return { threads: [] };
  }
}

export default async function ThreadsPage() {
  const data = await getData();

  const stageNames = ["Input", "Hypothesis", "Implication", "Decision", "Actions", "Learning"];

  const typeColors: Record<string, string> = {
    business: "bg-blue-500/10 text-blue-500",
    sales: "bg-green-500/10 text-green-500",
    marketing: "bg-pink-500/10 text-pink-500",
    engineering: "bg-purple-500/10 text-purple-500",
    operations: "bg-orange-500/10 text-orange-500",
  };

  // Group by type
  const threadsByType = data.threads.reduce((acc, thread) => {
    if (!acc[thread.type]) acc[thread.type] = [];
    acc[thread.type].push(thread);
    return acc;
  }, {} as Record<string, Thread[]>);

  return (
    <div className="space-y-6">
      <div>
        <h1 className="text-2xl font-bold">Threads</h1>
        <p className="text-text-tertiary">
          6-stage decision execution pipelines
        </p>
      </div>

      {data.threads.length === 0 ? (
        <Card>
          <CardContent className="p-6 text-center text-text-tertiary">
            <p>No threads found.</p>
            <p className="text-sm mt-2">
              Threads are created in <code>threads/</code>
            </p>
          </CardContent>
        </Card>
      ) : (
        <div className="space-y-6">
          {Object.entries(threadsByType).map(([type, threads]) => (
            <div key={type}>
              <h2 className="text-lg font-semibold capitalize mb-3 flex items-center gap-2">
                {type}
                <Badge variant="secondary">{threads.length}</Badge>
              </h2>
              <div className="grid grid-cols-1 md:grid-cols-2 gap-4">
                {threads.map((thread) => (
                  <Card key={`${thread.type}/${thread.name}`}>
                    <CardHeader className="pb-2">
                      <div className="flex items-center justify-between">
                        <CardTitle className="text-base">{thread.name}</CardTitle>
                        <Badge className={typeColors[thread.type] || ""}>
                          Stage {thread.currentStage}/6
                        </Badge>
                      </div>
                    </CardHeader>
                    <CardContent>
                      {/* 6-stage pipeline */}
                      <div className="flex items-center gap-1">
                        {[1, 2, 3, 4, 5, 6].map((stage) => (
                          <div key={stage} className="flex-1 flex flex-col items-center">
                            <div
                              className={`w-full h-2 rounded ${
                                stage <= thread.currentStage
                                  ? "bg-bg-primary"
                                  : "bg-muted"
                              }`}
                            />
                            <span className="text-[10px] text-text-tertiary mt-1">
                              {stageNames[stage - 1].slice(0, 3)}
                            </span>
                          </div>
                        ))}
                      </div>
                    </CardContent>
                  </Card>
                ))}
              </div>
            </div>
          ))}
        </div>
      )}
    </div>
  );
}
