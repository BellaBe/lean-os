/**
 * Figma Design System Extractor
 *
 * Extracts design tokens from Figma and saves as YAML files.
 *
 * Usage:
 *   FIGMA_TOKEN=your-token npm run design:extract
 *
 * Or set FIGMA_TOKEN in .env.local
 */

import fs from 'fs';
import path from 'path';

const FIGMA_API = 'https://api.figma.com/v1';
const OUTPUT_DIR = path.resolve(__dirname, '../design-system');

interface FigmaConfig {
  fileKey: string;
  fileUrl: string;
  lastSync?: string;
}

interface ColorToken {
  name: string;
  value: string;
  opacity?: number;
}

interface TypographyToken {
  name: string;
  fontFamily: string;
  fontSize: number;
  fontWeight: number;
  lineHeight: number | string;
  letterSpacing?: number;
}

interface SpacingToken {
  name: string;
  value: number;
}

// Load config
function loadConfig(): FigmaConfig {
  const configPath = path.join(OUTPUT_DIR, 'figma.yaml');
  if (!fs.existsSync(configPath)) {
    throw new Error('figma.yaml not found. Please configure your Figma file first.');
  }
  const content = fs.readFileSync(configPath, 'utf-8');
  // Simple YAML parsing for our use case
  const lines = content.split('\n');
  const config: Record<string, string> = {};
  for (const line of lines) {
    const match = line.match(/^(\w+):\s*(.+)$/);
    if (match) {
      config[match[1]] = match[2].replace(/^["']|["']$/g, '');
    }
  }
  return config as unknown as FigmaConfig;
}

// Fetch Figma file
async function fetchFigmaFile(fileKey: string, token: string) {
  const response = await fetch(`${FIGMA_API}/files/${fileKey}`, {
    headers: {
      'X-Figma-Token': token,
    },
  });

  if (!response.ok) {
    throw new Error(`Figma API error: ${response.status} ${response.statusText}`);
  }

  return response.json();
}

// Fetch styles
async function fetchFigmaStyles(fileKey: string, token: string) {
  const response = await fetch(`${FIGMA_API}/files/${fileKey}/styles`, {
    headers: {
      'X-Figma-Token': token,
    },
  });

  if (!response.ok) {
    throw new Error(`Figma API error: ${response.status} ${response.statusText}`);
  }

  return response.json();
}

// Convert Figma color to hex
function rgbaToHex(r: number, g: number, b: number, a?: number): string {
  const toHex = (n: number) => Math.round(n * 255).toString(16).padStart(2, '0');
  const hex = `#${toHex(r)}${toHex(g)}${toHex(b)}`;
  if (a !== undefined && a < 1) {
    return `${hex}${toHex(a)}`;
  }
  return hex;
}

// Extract colors from Figma file
function extractColors(document: any): ColorToken[] {
  const colors: ColorToken[] = [];

  function traverse(node: any, path: string[] = []) {
    // Check for color styles
    if (node.fills && Array.isArray(node.fills)) {
      for (const fill of node.fills) {
        if (fill.type === 'SOLID' && fill.color) {
          const { r, g, b } = fill.color;
          const opacity = fill.opacity;
          colors.push({
            name: [...path, node.name].join('/'),
            value: rgbaToHex(r, g, b),
            opacity: opacity !== 1 ? opacity : undefined,
          });
        }
      }
    }

    // Traverse children
    if (node.children) {
      for (const child of node.children) {
        traverse(child, [...path, node.name]);
      }
    }
  }

  traverse(document);
  return colors;
}

// Extract typography from Figma file
function extractTypography(document: any): TypographyToken[] {
  const typography: TypographyToken[] = [];

  function traverse(node: any) {
    if (node.type === 'TEXT' && node.style) {
      const style = node.style;
      typography.push({
        name: node.name,
        fontFamily: style.fontFamily || 'Inter',
        fontSize: style.fontSize || 16,
        fontWeight: style.fontWeight || 400,
        lineHeight: style.lineHeightPx || style.lineHeightPercent || 1.5,
        letterSpacing: style.letterSpacing,
      });
    }

    if (node.children) {
      for (const child of node.children) {
        traverse(child);
      }
    }
  }

  traverse(document);
  return typography;
}

// Write YAML file
function writeYaml(filename: string, data: any, header?: string) {
  const filePath = path.join(OUTPUT_DIR, filename);
  const dir = path.dirname(filePath);

  if (!fs.existsSync(dir)) {
    fs.mkdirSync(dir, { recursive: true });
  }

  let content = '';
  if (header) {
    content += `# ${header}\n`;
    content += `# Auto-generated from Figma - do not edit manually\n`;
    content += `# Last synced: ${new Date().toISOString()}\n\n`;
  }

  // Simple YAML serialization
  content += serializeYaml(data);

  fs.writeFileSync(filePath, content);
  console.log(`  Written: ${filename}`);
}

function serializeYaml(data: any, indent = 0): string {
  const spaces = '  '.repeat(indent);

  if (Array.isArray(data)) {
    return data.map(item => {
      if (typeof item === 'object') {
        const lines = serializeYaml(item, indent + 1).split('\n').filter(Boolean);
        return `${spaces}- ${lines[0].trim()}\n${lines.slice(1).map(l => `${spaces}  ${l.trim()}`).join('\n')}`;
      }
      return `${spaces}- ${item}`;
    }).join('\n');
  }

  if (typeof data === 'object' && data !== null) {
    return Object.entries(data)
      .filter(([, v]) => v !== undefined)
      .map(([key, value]) => {
        if (typeof value === 'object' && value !== null) {
          return `${spaces}${key}:\n${serializeYaml(value, indent + 1)}`;
        }
        return `${spaces}${key}: ${JSON.stringify(value)}`;
      }).join('\n');
  }

  return String(data);
}

// Main extraction
async function main() {
  const token = process.env.FIGMA_TOKEN;
  if (!token) {
    console.error('Error: FIGMA_TOKEN environment variable is required');
    console.error('Get your token from: https://www.figma.com/settings');
    process.exit(1);
  }

  console.log('Loading Figma configuration...');
  const config = loadConfig();
  console.log(`File: ${config.fileKey}`);

  console.log('\nFetching Figma file...');
  const file = await fetchFigmaFile(config.fileKey, token);
  console.log(`File name: ${file.name}`);

  console.log('\nExtracting design tokens...');

  // Extract colors
  const colors = extractColors(file.document);
  if (colors.length > 0) {
    writeYaml('tokens/colors.yaml', { colors }, 'Color Tokens');
  }

  // Extract typography
  const typography = extractTypography(file.document);
  if (typography.length > 0) {
    writeYaml('tokens/typography.yaml', { typography }, 'Typography Tokens');
  }

  // Update figma.yaml with last sync
  const figmaConfig = `# Figma Design System Source
fileKey: "${config.fileKey}"
fileUrl: "${config.fileUrl}"
fileName: "${file.name}"
lastSync: "${new Date().toISOString()}"
`;
  fs.writeFileSync(path.join(OUTPUT_DIR, 'figma.yaml'), figmaConfig);

  console.log('\nExtraction complete!');
}

main().catch(console.error);
