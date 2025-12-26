import type { LeanOSData } from './types';

let cachedData: LeanOSData | null = null;

export async function getLeanOSData(): Promise<LeanOSData> {
  if (cachedData) return cachedData;

  // In production, fetch from the static JSON file
  // basePath is /lean-os for GitHub Pages
  const basePath = process.env.NODE_ENV === 'production' ? '/lean-os' : '';
  const response = await fetch(`${basePath}/data/leanos.json`);
  cachedData = await response.json();
  return cachedData as LeanOSData;
}

// For static generation, import the JSON directly
export function getLeanOSDataSync(): LeanOSData {
  // This will be replaced with actual data at build time
  // For now, return empty data structure
  return {
    goals: [],
    canvas: { mode: 'VENTURE', sections: [], health: 0 },
    threads: [],
    skills: [],
    agents: [],
    artifacts: [],
    research: { sources: [], playbooks: [] },
    meta: { lastBuilt: new Date().toISOString(), version: '1.0.0' },
  };
}
