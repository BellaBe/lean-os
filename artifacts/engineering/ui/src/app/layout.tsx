import type { Metadata, Viewport } from "next";
import { Inter } from "next/font/google";
import { RouteProvider } from "@/providers/router-provider";
import { Theme } from "@/providers/theme";
import { DataProvider } from "@/providers/data-provider";
import { Sidebar } from "@/components/leanos/sidebar";
import { getLeanOSData } from "@/lib/data";
import "@/styles/globals.css";
import { cx } from "@/utils/cx";

const inter = Inter({
    subsets: ["latin"],
    display: "swap",
    variable: "--font-inter",
});

export const metadata: Metadata = {
    title: "LeanOS Dashboard",
    description: "Autonomous operating system for startups",
};

export const viewport: Viewport = {
    themeColor: "#7f56d9",
    colorScheme: "light dark",
};

export default async function RootLayout({
    children,
}: Readonly<{
    children: React.ReactNode;
}>) {
    const data = await getLeanOSData();

    return (
        <html lang="en" suppressHydrationWarning>
            <body className={cx(inter.variable, "bg-primary antialiased")}>
                <RouteProvider>
                    <Theme>
                        <DataProvider data={data}>
                            <Sidebar mode={data.canvas.mode} />
                            <main className="lg:pl-64 min-h-screen">
                                {children}
                            </main>
                        </DataProvider>
                    </Theme>
                </RouteProvider>
            </body>
        </html>
    );
}
