import type { LeanOSData } from './types';

// Load LeanOS data at build time
export async function getLeanOSData(): Promise<LeanOSData> {
  // In production, this would be fetched from the public directory
  // For now, we import it directly for SSR
  const data = await import('../../public/data/leanos.json');
  return data.default as LeanOSData;
}

// Compute dashboard stats from data
export function computeStats(data: LeanOSData) {
  const activeGoals = data.goals.filter(g => g.status === 'active').length;
  const completedGoals = data.goals.filter(g => g.status === 'completed').length;

  const populatedSections = data.canvas.sections.filter(s => s.status !== 'missing').length;

  const activeThreads = data.threads.filter(t => t.currentStage < 6).length;
  const completedThreads = data.threads.filter(t => t.currentStage >= 6).length;

  const threadsByType = data.threads.reduce((acc, t) => {
    acc[t.type] = (acc[t.type] || 0) + 1;
    return acc;
  }, {} as Record<string, number>);

  const skillsByCategory = data.skills.reduce((acc, s) => {
    acc[s.category] = (acc[s.category] || 0) + 1;
    return acc;
  }, {} as Record<string, number>);

  return {
    goals: {
      active: activeGoals,
      completed: completedGoals,
      total: data.goals.length,
    },
    canvas: {
      health: data.canvas.health,
      mode: data.canvas.mode,
      populated: populatedSections,
      total: data.canvas.sections.length,
    },
    threads: {
      active: activeThreads,
      completed: completedThreads,
      total: data.threads.length,
      byType: threadsByType,
    },
    skills: {
      total: data.skills.length,
      byCategory: skillsByCategory,
    },
    agents: {
      total: data.agents.length,
    },
  };
}

// Get skill categories
export function getSkillCategories(skills: LeanOSData['skills']): string[] {
  const categories = new Set(skills.map(s => s.category));
  return Array.from(categories).sort();
}

// Get thread types
export function getThreadTypes(threads: LeanOSData['threads']): string[] {
  const types = new Set(threads.map(t => t.type));
  return Array.from(types).sort();
}
