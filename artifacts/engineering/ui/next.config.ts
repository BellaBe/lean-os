import type { NextConfig } from "next";

const nextConfig: NextConfig = {
  output: 'export',
  basePath: '/lean-os',
  assetPrefix: '/lean-os',
  images: {
    unoptimized: true,
  },
  trailingSlash: true,
};

export default nextConfig;
