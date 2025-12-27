"use client";

import { createContext, useContext, type ReactNode } from "react";
import type { LeanOSData } from "@/lib/types";

const DataContext = createContext<LeanOSData | null>(null);

interface DataProviderProps {
  data: LeanOSData;
  children: ReactNode;
}

export function DataProvider({ data, children }: DataProviderProps) {
  return <DataContext.Provider value={data}>{children}</DataContext.Provider>;
}

export function useLeanOSData(): LeanOSData {
  const context = useContext(DataContext);
  if (!context) {
    throw new Error("useLeanOSData must be used within a DataProvider");
  }
  return context;
}
