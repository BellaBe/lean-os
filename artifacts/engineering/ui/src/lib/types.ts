// LeanOS Data Types

export interface Goal {
  id: string;
  title: string;
  type: string;
  status: string;
  autonomy: string;
  deadline?: string;
  objective: string;
  successCriteria: string[];
  subgoals: Array<{ id: string; description: string; status: string; linkedThread?: string }>;
  milestones: Array<{ id: string; description: string; date: string; status: string }>;
  linkedThreads: string[];
  progress: number;
}

export interface CanvasSection {
  number: string;
  name: string;
  slug: string;
  status: 'complete' | 'draft' | 'missing';
  content: string;
  summary?: string;
}

export interface Canvas {
  mode: string;
  sections: CanvasSection[];
  health: number;
}

export interface ThreadStage {
  number: number;
  name: string;
  status: 'pending' | 'completed';
  content?: string;
}

export interface Thread {
  type: string;
  name: string;
  path: string;
  goalId?: string;
  currentStage: number;
  stages: ThreadStage[];
}

export interface Skill {
  name: string;
  category: string;
  purpose: string;
  whenToUse: string[];
  location: string;
}

export interface Agent {
  name: string;
  purpose: string;
  skills: string[];
  location: string;
}

export interface LeanOSData {
  goals: Goal[];
  canvas: Canvas;
  threads: Thread[];
  skills: Skill[];
  agents: Agent[];
  artifacts: unknown[];
  research: { sources: unknown[]; playbooks: unknown[] };
  meta: {
    lastBuilt: string;
    version: string;
  };
}
