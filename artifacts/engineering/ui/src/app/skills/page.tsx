import { Card, CardContent, CardHeader, CardTitle } from "@/components/ui/card";
import { Badge } from "@/components/ui/badge";
import { Tabs, TabsContent, TabsList, TabsTrigger } from "@/components/ui/tabs";
import fs from "fs";
import path from "path";

interface Skill {
  name: string;
  category: string;
  purpose: string;
  location: string;
}

interface Agent {
  name: string;
  purpose: string;
  skills: string[];
  location: string;
}

interface LeanOSData {
  skills: Skill[];
  agents: Agent[];
}

async function getData(): Promise<LeanOSData> {
  const dataPath = path.join(process.cwd(), "public/data/leanos.json");
  try {
    const data = fs.readFileSync(dataPath, "utf-8");
    return JSON.parse(data);
  } catch {
    return { skills: [], agents: [] };
  }
}

export default async function SkillsPage() {
  const data = await getData();

  // Group skills by category
  const skillsByCategory = data.skills.reduce((acc, skill) => {
    if (!acc[skill.category]) acc[skill.category] = [];
    acc[skill.category].push(skill);
    return acc;
  }, {} as Record<string, Skill[]>);

  const categories = Object.keys(skillsByCategory).sort();

  // Category colors
  const categoryColors: Record<string, string> = {
    action: "bg-blue-500/10 text-blue-500 border-blue-500/20",
    engineering: "bg-purple-500/10 text-purple-500 border-purple-500/20",
    foundations: "bg-green-500/10 text-green-500 border-green-500/20",
    goal: "bg-yellow-500/10 text-yellow-500 border-yellow-500/20",
    marketing: "bg-pink-500/10 text-pink-500 border-pink-500/20",
    product: "bg-orange-500/10 text-orange-500 border-orange-500/20",
    reasoning: "bg-cyan-500/10 text-cyan-500 border-cyan-500/20",
    research: "bg-indigo-500/10 text-indigo-500 border-indigo-500/20",
    sales: "bg-red-500/10 text-red-500 border-red-500/20",
  };

  return (
    <div className="space-y-6">
      <div>
        <h1 className="text-2xl font-bold">Skills & Agents</h1>
        <p className="text-text-tertiary">
          {data.skills.length} skills across {categories.length} categories,
          orchestrated by {data.agents.length} agents
        </p>
      </div>

      <Tabs defaultValue="skills" className="w-full">
        <TabsList>
          <TabsTrigger value="skills">Skills ({data.skills.length})</TabsTrigger>
          <TabsTrigger value="agents">Agents ({data.agents.length})</TabsTrigger>
        </TabsList>

        <TabsContent value="skills" className="mt-6">
          {/* Category Overview */}
          <div className="grid grid-cols-2 md:grid-cols-3 lg:grid-cols-5 gap-3 mb-6">
            {categories.map((category) => (
              <Card key={category} className="hover:bg-accent/50 transition-colors">
                <CardContent className="p-4">
                  <div className="flex items-center justify-between">
                    <span className="text-sm font-medium capitalize">{category}</span>
                    <Badge variant="secondary">
                      {skillsByCategory[category].length}
                    </Badge>
                  </div>
                </CardContent>
              </Card>
            ))}
          </div>

          {/* Skills by Category */}
          <div className="space-y-6">
            {categories.map((category) => (
              <div key={category}>
                <h2 className="text-lg font-semibold capitalize mb-3 flex items-center gap-2">
                  {category}
                  <Badge
                    variant="outline"
                    className={categoryColors[category] || ""}
                  >
                    {skillsByCategory[category].length}
                  </Badge>
                </h2>
                <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-3">
                  {skillsByCategory[category].map((skill) => (
                    <Card key={skill.name} className="hover:bg-accent/30 transition-colors">
                      <CardHeader className="pb-2">
                        <CardTitle className="text-sm font-medium">
                          {skill.name}
                        </CardTitle>
                      </CardHeader>
                      <CardContent>
                        <p className="text-xs text-text-tertiary line-clamp-2">
                          {skill.purpose || "No description available"}
                        </p>
                      </CardContent>
                    </Card>
                  ))}
                </div>
              </div>
            ))}
          </div>
        </TabsContent>

        <TabsContent value="agents" className="mt-6">
          <div className="grid grid-cols-1 md:grid-cols-2 gap-4">
            {data.agents.map((agent) => (
              <Card key={agent.name}>
                <CardHeader>
                  <CardTitle className="text-base">{agent.name}</CardTitle>
                </CardHeader>
                <CardContent>
                  <p className="text-sm text-text-tertiary mb-3">
                    {agent.purpose || "Orchestrator agent"}
                  </p>
                  {agent.skills.length > 0 && (
                    <div>
                      <p className="text-xs font-medium mb-2">Routes to:</p>
                      <div className="flex flex-wrap gap-1">
                        {agent.skills.slice(0, 8).map((skill) => (
                          <Badge key={skill} variant="outline" className="text-xs">
                            {skill}
                          </Badge>
                        ))}
                        {agent.skills.length > 8 && (
                          <Badge variant="outline" className="text-xs">
                            +{agent.skills.length - 8} more
                          </Badge>
                        )}
                      </div>
                    </div>
                  )}
                </CardContent>
              </Card>
            ))}
          </div>
        </TabsContent>
      </Tabs>
    </div>
  );
}
