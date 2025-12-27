import {
  Home03,
  Grid01,
  Route,
  Zap,
  Users01,
  Target04,
  BookOpen01,
  Folder,
} from "@untitledui/icons";
import type { NavItemType } from "@/components/application/app-navigation/config";

export const mainNavItems: NavItemType[] = [
  {
    label: "Dashboard",
    href: "/",
    icon: Home03,
  },
  {
    label: "Canvas",
    href: "/canvas",
    icon: Grid01,
  },
  {
    label: "Threads",
    href: "/threads",
    icon: Route,
  },
  {
    label: "Goals",
    href: "/goals",
    icon: Target04,
  },
  {
    label: "Skills",
    href: "/skills",
    icon: Zap,
  },
  {
    label: "Agents",
    href: "/agents",
    icon: Users01,
  },
];

export const footerNavItems: NavItemType[] = [
  {
    label: "Research",
    href: "/research",
    icon: BookOpen01,
  },
  {
    label: "Artifacts",
    href: "/artifacts",
    icon: Folder,
  },
];
