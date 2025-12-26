/**
 * Build script to parse LeanOS markdown files and generate JSON data
 * Run with: npx tsx scripts/build-data.ts
 */

import fs from 'fs';
import path from 'path';
import matter from 'gray-matter';

// Paths relative to the ui directory (ui -> engineering -> artifacts -> lean-os)
const ROOT = path.resolve(__dirname, '../../../..');
const OUTPUT_DIR = path.resolve(__dirname, '../public/data');

interface Goal {
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

interface CanvasSection {
  number: string;
  name: string;
  slug: string;
  status: 'complete' | 'draft' | 'missing';
  content: string;
  summary?: string;
}

interface Thread {
  type: string;
  name: string;
  path: string;
  goalId?: string;
  currentStage: number;
  stages: Array<{ number: number; name: string; status: string; content?: string }>;
}

interface Skill {
  name: string;
  category: string;
  purpose: string;
  whenToUse: string[];
  location: string;
}

interface Agent {
  name: string;
  purpose: string;
  skills: string[];
  location: string;
}

// Helper functions
function ensureDir(dir: string) {
  if (!fs.existsSync(dir)) {
    fs.mkdirSync(dir, { recursive: true });
  }
}

function readMarkdownFile(filePath: string): { data: Record<string, unknown>; content: string } | null {
  try {
    const fileContent = fs.readFileSync(filePath, 'utf-8');
    return matter(fileContent);
  } catch {
    return null;
  }
}

function getFiles(dir: string, pattern?: RegExp): string[] {
  if (!fs.existsSync(dir)) return [];

  const files: string[] = [];
  const entries = fs.readdirSync(dir, { withFileTypes: true });

  for (const entry of entries) {
    const fullPath = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      files.push(...getFiles(fullPath, pattern));
    } else if (!pattern || pattern.test(entry.name)) {
      files.push(fullPath);
    }
  }

  return files;
}

// Parse goals
function parseGoals(): Goal[] {
  const goalsDir = path.join(ROOT, 'strategy/goals/active');
  const files = getFiles(goalsDir, /\.md$/);

  const goals: Goal[] = [];
  for (const file of files) {
    const parsed = readMarkdownFile(file);
    if (!parsed) continue;

    const { data, content } = parsed;
    const fileName = path.basename(file, '.md');

    // Extract sections from content
    const objectiveMatch = content.match(/## Objective\s*\n([\s\S]*?)(?=\n##|$)/);
    const criteriaMatch = content.match(/## Success Criteria\s*\n([\s\S]*?)(?=\n##|$)/);

    const successCriteria = criteriaMatch
      ? criteriaMatch[1].split('\n').filter(l => l.trim().startsWith('-')).map(l => l.replace(/^-\s*\[.\]\s*/, '').trim())
      : [];

    goals.push({
      id: (data.id as string) || fileName,
      title: (data.title as string) || fileName.replace('g-', '').replace(/-/g, ' '),
      type: (data.type as string) || 'business',
      status: (data.status as string) || 'active',
      autonomy: (data.autonomy as string) || 'hybrid',
      deadline: data.deadline as string | undefined,
      objective: objectiveMatch ? objectiveMatch[1].trim() : '',
      successCriteria,
      subgoals: [],
      milestones: [],
      linkedThreads: [],
      progress: 0,
    });
  }
  return goals;
}

// Parse canvas sections
function parseCanvas(): { mode: string; sections: CanvasSection[]; health: number } {
  const canvasDir = path.join(ROOT, 'strategy/canvas');

  // Check if directory exists
  if (!fs.existsSync(canvasDir)) {
    return { mode: 'VENTURE', sections: [], health: 0 };
  }

  const files = fs.readdirSync(canvasDir).filter(f => f.endsWith('.md')).sort();

  // Parse mode from 00-business-model-mode.md
  let mode = 'VENTURE';
  const modeFile = path.join(canvasDir, '00-business-model-mode.md');
  if (fs.existsSync(modeFile)) {
    const content = fs.readFileSync(modeFile, 'utf-8');
    if (content.includes('BOOTSTRAP')) mode = 'BOOTSTRAP';
    else if (content.includes('HYBRID')) mode = 'HYBRID';
  }

  const sectionNames: Record<string, string> = {
    '01': 'Context',
    '02': 'Constraints',
    '03': 'Opportunity',
    '04': 'Segments',
    '05': 'Problem',
    '06': 'Competitive',
    '07': 'UVP',
    '08': 'Advantage',
    '09': 'Solution',
    '10': 'Assumptions',
    '11': 'Pricing',
    '12': 'Costs',
    '13': 'Metrics',
    '14': 'Growth',
    '15': 'Go-to-Market',
  };

  const sections: CanvasSection[] = [];
  let completeCount = 0;

  for (const num of Object.keys(sectionNames)) {
    const fileName = files.find(f => f.startsWith(`${num}-`));

    if (fileName) {
      const parsed = readMarkdownFile(path.join(canvasDir, fileName));
      const content = parsed?.content || '';
      const status = content.length > 100 ? 'complete' : 'draft';
      if (status === 'complete') completeCount++;

      sections.push({
        number: num,
        name: sectionNames[num],
        slug: fileName.replace('.md', ''),
        status,
        content: content.slice(0, 500), // Preview only
        summary: content.split('\n').find(l => l.trim() && !l.startsWith('#'))?.trim(),
      });
    } else {
      sections.push({
        number: num,
        name: sectionNames[num],
        slug: `${num}-${sectionNames[num].toLowerCase()}`,
        status: 'missing',
        content: '',
      });
    }
  }

  const health = Math.round((completeCount / 15) * 100);

  return { mode, sections, health };
}

// Parse threads
function parseThreads(): Thread[] {
  const threadsDir = path.join(ROOT, 'threads');
  if (!fs.existsSync(threadsDir)) return [];

  const threads: Thread[] = [];
  const types = ['business', 'sales', 'marketing', 'engineering', 'operations'];

  for (const type of types) {
    const typeDir = path.join(threadsDir, type);
    if (!fs.existsSync(typeDir)) continue;

    const threadDirs = fs.readdirSync(typeDir, { withFileTypes: true })
      .filter(d => d.isDirectory())
      .map(d => d.name);

    for (const threadName of threadDirs) {
      const threadPath = path.join(typeDir, threadName);
      const stageFiles = fs.readdirSync(threadPath).filter(f => /^[1-6]-/.test(f));

      const stageNames = ['Input', 'Hypothesis', 'Implication', 'Decision', 'Actions', 'Learning'];
      const stages = stageNames.map((name, i) => {
        const stageFile = stageFiles.find(f => f.startsWith(`${i + 1}-`));
        return {
          number: i + 1,
          name,
          status: stageFile ? 'completed' : 'pending',
        };
      });

      const currentStage = stages.filter(s => s.status === 'completed').length + 1;

      threads.push({
        type,
        name: threadName,
        path: `threads/${type}/${threadName}`,
        currentStage: Math.min(currentStage, 6),
        stages,
      });
    }
  }

  return threads;
}

// Parse skills
function parseSkills(): Skill[] {
  const skillsDir = path.join(ROOT, '.claude/skills');
  if (!fs.existsSync(skillsDir)) return [];

  const skills: Skill[] = [];
  const skillDirs = fs.readdirSync(skillsDir, { withFileTypes: true })
    .filter(d => d.isDirectory())
    .map(d => d.name);

  for (const skillName of skillDirs) {
    const skillFile = path.join(skillsDir, skillName, 'SKILL.md');
    if (!fs.existsSync(skillFile)) continue;

    const content = fs.readFileSync(skillFile, 'utf-8');
    const category = skillName.split('-')[0]; // action, engineering, etc.

    // Extract purpose from first paragraph or description
    const purposeMatch = content.match(/(?:Purpose|Description)[:\s]*\n?(.*?)(?:\n\n|\n#|$)/is);
    const purpose = purposeMatch ? purposeMatch[1].trim().slice(0, 200) : '';

    skills.push({
      name: skillName,
      category,
      purpose,
      whenToUse: [],
      location: `.claude/skills/${skillName}/SKILL.md`,
    });
  }

  return skills;
}

// Parse agents
function parseAgents(): Agent[] {
  const agentsDir = path.join(ROOT, '.claude/agents');
  if (!fs.existsSync(agentsDir)) return [];

  const agents: Agent[] = [];
  const files = fs.readdirSync(agentsDir).filter(f => f.endsWith('.md'));

  for (const file of files) {
    const name = file.replace('.md', '');
    const content = fs.readFileSync(path.join(agentsDir, file), 'utf-8');

    // Extract purpose from content
    const purposeMatch = content.match(/(?:Purpose|orchestrat)[:\s]*(.*?)(?:\n\n|\n#|$)/is);
    const purpose = purposeMatch ? purposeMatch[1].trim().slice(0, 200) : '';

    // Extract skills loaded
    const skillsMatch = content.match(/Skills?\s*(?:loaded|routes?)[:\s]*(.*?)(?:\n\n|\n#|$)/is);
    const skills = skillsMatch
      ? skillsMatch[1].split(/[,\n]/).map(s => s.trim()).filter(s => s && !s.includes(':'))
      : [];

    agents.push({
      name,
      purpose,
      skills,
      location: `.claude/agents/${file}`,
    });
  }

  return agents;
}

// Main build function
async function build() {
  console.log('Building LeanOS data...');
  console.log(`Root: ${ROOT}`);
  console.log(`Output: ${OUTPUT_DIR}`);

  ensureDir(OUTPUT_DIR);

  // Parse all data
  const goals = parseGoals();
  console.log(`Parsed ${goals.length} goals`);

  const canvas = parseCanvas();
  console.log(`Parsed canvas with ${canvas.sections.length} sections (${canvas.health}% health)`);

  const threads = parseThreads();
  console.log(`Parsed ${threads.length} threads`);

  const skills = parseSkills();
  console.log(`Parsed ${skills.length} skills`);

  const agents = parseAgents();
  console.log(`Parsed ${agents.length} agents`);

  // Combine into single data file
  const data = {
    goals,
    canvas,
    threads,
    skills,
    agents,
    artifacts: [],
    research: { sources: [], playbooks: [] },
    meta: {
      lastBuilt: new Date().toISOString(),
      version: '1.0.0',
    },
  };

  // Write combined data
  fs.writeFileSync(
    path.join(OUTPUT_DIR, 'leanos.json'),
    JSON.stringify(data, null, 2)
  );

  console.log('Build complete!');
}

build().catch(console.error);
