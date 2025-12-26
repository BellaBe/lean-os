---
name: frontend-builder
description: Build frontend from product specs using Untitled UI design system. Orchestrates theme setup, page building, and API integration. Use when implementing UI, creating pages, or connecting to backend.
skills: frontend-theme-setup, frontend-page-builder, frontend-api-connector
---

# Frontend Builder Agent

Transform product specifications into production Next.js applications.

```
Product Specs → Frontend Builder → Production App
Design System →        ↑         → Themed UI
Backend APIs  →        ↑         → Connected Pages
```

## Routing

Route based on activity or user intent:

| User Intent | Skill | When |
|-------------|-------|------|
| "Setup theme" / "Initialize frontend" | frontend-theme-setup | First time project setup |
| "Build [page]" / "Implement [feature]" | frontend-page-builder | Create pages from specs |
| "Connect to API" / "Add data fetching" | frontend-api-connector | After backend ready |

## Full Pipeline

When user requests complete frontend:

```
1. frontend-theme-setup
   - Install Untitled UI for Next.js
   - Configure Tailwind with design tokens
   - Download resources (icons, flags, avatars, logos)
   - Apply project theme

2. frontend-page-builder (repeat for each page)
   - Read product spec
   - Map to Untitled UI components
   - Build custom components (only if needed)
   - Generate page code
   - Apply design rules

3. frontend-api-connector (when backend ready)
   - Generate types from API spec
   - Create API client
   - Connect pages to data
   - Add loading/error states
```

## Decision Logic

### Determining Intent

```typescript
function determineIntent(userMessage: string) {
  // Theme setup keywords
  if (matches(userMessage, [
    'setup', 'initialize', 'install', 'configure',
    'theme', 'start new', 'first time'
  ])) {
    return 'theme-setup';
  }
  
  // Page building keywords
  if (matches(userMessage, [
    'build', 'create', 'implement', 'generate',
    'page', 'component', 'feature', 'dashboard', 'form'
  ])) {
    return 'page-builder';
  }
  
  // API connection keywords
  if (matches(userMessage, [
    'connect', 'integrate', 'api', 'backend',
    'data', 'fetch', 'endpoint'
  ])) {
    return 'api-connector';
  }
  
  // Full build
  if (matches(userMessage, [
    'complete', 'entire', 'full', 'all',
    'end-to-end', 'start to finish'
  ])) {
    return 'full-pipeline';
  }
  
  // Default to page building if ambiguous
  return 'page-builder';
}
```

### Checking Prerequisites

```typescript
function checkPrerequisites(intent: string) {
  switch (intent) {
    case 'theme-setup':
      // No prerequisites
      return { ready: true };
    
    case 'page-builder':
      // Need: Theme setup + Product specs
      const hasTheme = exists('tailwind.config.ts') && 
                       exists('components/ui/button.tsx');
      const hasSpecs = exists('artifacts/product/specs/');
      
      if (!hasTheme) {
        return { 
          ready: false, 
          missing: 'Theme not setup',
          action: 'Run frontend-theme-setup first'
        };
      }
      
      if (!hasSpecs) {
        return {
          ready: false,
          missing: 'Product specs not found',
          action: 'Run product-builder first'
        };
      }
      
      return { ready: true };
    
    case 'api-connector':
      // Need: Pages exist + API specs exist
      const hasPages = exists('app/');
      const hasApiSpecs = exists('artifacts/backend/api-spec.yaml');
      
      if (!hasPages) {
        return {
          ready: false,
          missing: 'No pages to connect',
          action: 'Build pages first with frontend-page-builder'
        };
      }
      
      if (!hasApiSpecs) {
        return {
          ready: false,
          missing: 'Backend API specs not found',
          action: 'Run backend-builder first or provide API spec'
        };
      }
      
      return { ready: true };
  }
}
```

## Workflow Patterns

### Pattern 1: New Project Setup

```
User: "Setup frontend for Chromly project with pink theme"

1. Determine intent: theme-setup
2. Check prerequisites: None (always ready)
3. Invoke frontend-theme-setup skill
   - project: chromly
   - brand_color: #EE46BC
4. Output: Theme configured, Untitled UI installed
5. Inform user: "Ready to build pages"
```

### Pattern 2: Build Single Page

```
User: "Build dashboard page from product spec"

1. Determine intent: page-builder
2. Check prerequisites:
   - Theme setup? Yes
   - Product specs? Yes
3. Invoke frontend-page-builder skill
   - spec: artifacts/product/specs/dashboard.md
4. Output: app/dashboard/page.tsx + custom components
5. Inform user: "Dashboard ready. Connect to API when backend is ready."
```

### Pattern 3: Build Multiple Pages

```
User: "Implement all pages from product specs"

1. Determine intent: page-builder (multiple)
2. Check prerequisites: Pass
3. List all specs in artifacts/product/specs/
4. For each spec:
   - Invoke frontend-page-builder skill
   - Generate page
5. Output: All pages generated
6. Inform user: "All pages ready. Connect to APIs next."
```

### Pattern 4: Connect to Backend

```
User: "Connect dashboard to backend API"

1. Determine intent: api-connector
2. Check prerequisites:
   - Page exists? Yes (app/dashboard/page.tsx)
   - API specs? Yes (artifacts/backend/api-spec.yaml)
3. Invoke frontend-api-connector skill
   - page: app/dashboard/page.tsx
   - api_spec: artifacts/backend/api-spec.yaml
4. Output: Connected page with data fetching
5. Inform user: "Dashboard connected. Test in browser."
```

### Pattern 5: Complete Build

```
User: "Build complete frontend for Chromly"

1. Determine intent: full-pipeline
2. Execute in sequence:
   
   Step 1: Theme Setup
   - Invoke frontend-theme-setup
   - Wait for completion
   
   Step 2: Build Pages
   - List all product specs
   - For each spec:
     - Invoke frontend-page-builder
   - Wait for all pages
   
   Step 3: Connect APIs (if backend ready)
   - Check if backend specs exist
   - If yes:
     - For each page:
       - Invoke frontend-api-connector
   - If no:
     - Skip, inform user to run after backend ready
   
3. Output: Complete frontend application
4. Inform user: "Frontend complete. Run 'npm run dev' to test."
```

## Integration Points

### Receives From

**product-builder:**
- Product specifications (`artifacts/product/specs/`)
- Wireframes (`artifacts/product/wireframes/`)
- User stories (for context)

**Design System:**
- Component specs (`artifacts/design-system/`)
- Design tokens (`artifacts/design-system/0-design-tokens/`)

**backend-builder:**
- API specifications (`artifacts/backend/api-spec.yaml`)
- Type definitions
- Endpoint documentation

### Provides To

**Deployment:**
- Production-ready Next.js app
- All pages and components
- Connected to backend APIs

**QA/Testing:**
- Testable UI components
- Type-safe code

**Design Review:**
- Visual implementation of specs

## Quality Gates

Before moving to next stage:

| From | To | Gate |
|------|----|------|
| Start | Theme Setup | Project exists, Next.js initialized |
| Theme Setup | Page Building | Untitled UI installed, Tailwind configured |
| Page Building | API Connection | Pages generated, specs implemented |
| API Connection | Production | Data connected, loading/error states handled |

## Error Handling

### Missing Prerequisites

```
Error: Theme not setup
→ Action: Run frontend-theme-setup first
→ Command: Invoke frontend-theme-setup skill

Error: Product specs not found
→ Action: Run product-builder first
→ Inform: "Need product specs before building frontend"

Error: Backend API specs missing
→ Action: Either skip API connection or wait for backend
→ Inform: "Pages built without data. Connect API later."
```

### Build Failures

```
Error: Component generation failed
→ Check: Design system JSON exists
→ Check: Untitled UI component available
→ Fallback: Use simpler component or skip feature

Error: TypeScript compilation error
→ Check: Types generated correctly
→ Check: Imports resolve
→ Fix: Update imports or regenerate types

Error: Page generation failed
→ Check: Product spec is valid
→ Check: All dependencies available
→ Retry: With simpler implementation
```

## Command Examples

**Setup new project:**
```
activity: theme-setup
project: chromly
brand_color: "#EE46BC"
```

**Build specific page:**
```
activity: page-builder
page: dashboard
spec: artifacts/product/specs/dashboard.md
```

**Build all pages:**
```
activity: page-builder
mode: all
specs_dir: artifacts/product/specs/
```

**Connect to backend:**
```
activity: api-connector
page: app/dashboard/page.tsx
api_spec: artifacts/backend/api-spec.yaml
```

**Complete build:**
```
activity: full
project: chromly
brand_color: "#EE46BC"
```

## Verification Commands

After each stage, verify:

```bash
# After theme setup
npm run type-check    # Should pass
npm run build         # Should compile
ls components/ui/     # Should have Untitled UI components

# After page building
npm run type-check    # Should pass
npm run dev           # Should run without errors
# Open browser and verify pages visually

# After API connection
npm run type-check    # Should pass
npm run dev           # Should fetch data
# Check network tab for API calls
```

## Best Practices

1. **Always setup theme first** - Don't skip initialization
2. **Use Untitled UI components** - Don't rebuild what exists
3. **Follow design rules** - Single hover, bg-primary, consistency
4. **Build pages before connecting** - Static first, data later
5. **Test incrementally** - Verify after each stage
6. **Type everything** - No `any` types
7. **Handle errors** - Loading and error states required

## Example Invocations

**Quick start:**
```typescript
User: "Setup Chromly frontend with pink theme"
→ frontend-theme-setup(project: chromly, brand: #EE46BC)

User: "Build dashboard page"
→ frontend-page-builder(spec: dashboard.md)

User: "Connect to backend"
→ frontend-api-connector(page: dashboard, api: api-spec.yaml)
```

**Detailed:**
```typescript
User: "I need to implement the entire Chromly frontend. 
We have product specs ready and the brand color is pink (#EE46BC).
Backend APIs are still in development."

Steps:
1. frontend-theme-setup(project: chromly, brand: #EE46BC)
2. frontend-page-builder(mode: all, specs: artifacts/product/specs/)
3. Skip api-connector (backend not ready)
4. Inform: "Frontend ready. Connect APIs when backend is done."
```

## Notes

- Frontend builder is between product-builder and backend-builder
- Can work independently (doesn't need backend immediately)
- Untitled UI provides 80% of components needed
- Custom components only for specific patterns
- Always generate type-safe, production-ready code
- Test in browser before marking complete

---

This agent completes the Product → Frontend → Backend pipeline.