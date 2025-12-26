// LeanOS Data Types

export interface Goal {
  id: string;
  title: string;
  type: 'business' | 'brand' | 'product' | 'learning' | 'custom';
  status: 'active' | 'completed' | 'abandoned';
  autonomy: 'auto' | 'ask' | 'hybrid';
  deadline?: string;
  objective: string;
  successCriteria: string[];
  subgoals: Subgoal[];
  milestones: Milestone[];
  linkedThreads: string[];
  progress: number;
}

export interface Subgoal {
  id: string;
  description: string;
  status: 'pending' | 'in_progress' | 'completed';
  linkedThread?: string;
}

export interface Milestone {
  id: string;
  description: string;
  date: string;
  status: 'pending' | 'completed';
}

export interface CanvasSection {
  number: string;
  name: string;
  slug: string;
  status: 'complete' | 'draft' | 'missing';
  content: string;
  summary?: string;
  lastUpdated?: string;
}

export interface Canvas {
  mode: 'VENTURE' | 'BOOTSTRAP' | 'HYBRID';
  sections: CanvasSection[];
  health: number;
}

export interface ThreadStage {
  number: 1 | 2 | 3 | 4 | 5 | 6;
  name: string;
  status: 'pending' | 'in_progress' | 'completed';
  content?: string;
}

export interface Thread {
  type: 'business' | 'sales' | 'marketing' | 'engineering' | 'operations';
  name: string;
  path: string;
  goalId?: string;
  currentStage: number;
  stages: ThreadStage[];
  impactScore?: number;
  hypothesis?: string;
  createdAt?: string;
}

export interface Skill {
  name: string;
  category: string;
  purpose: string;
  question?: string;
  output?: string;
  routedBy?: string;
  whenToUse: string[];
  location: string;
}

export interface Agent {
  name: string;
  purpose: string;
  skills: string[];
  pipeline?: string[];
  location: string;
}

export interface Artifact {
  name: string;
  path: string;
  type: 'file' | 'directory';
  domain: 'engineering' | 'sales' | 'marketing' | 'operations';
  children?: Artifact[];
}

export interface ResearchSource {
  slug: string;
  title: string;
  type: 'video' | 'podcast' | 'article' | 'book';
  hasInsights: boolean;
  path: string;
}

export interface Playbook {
  name: string;
  domain: string;
  path: string;
}

export interface LeanOSData {
  goals: Goal[];
  canvas: Canvas;
  threads: Thread[];
  skills: Skill[];
  agents: Agent[];
  artifacts: Artifact[];
  research: {
    sources: ResearchSource[];
    playbooks: Playbook[];
  };
  meta: {
    lastBuilt: string;
    version: string;
  };
}
