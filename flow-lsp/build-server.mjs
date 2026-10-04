import { build } from "esbuild";
import { cp } from "node:fs/promises";

await build({
  entryPoints: { server: "src/server.ts", "flow-checker-worker": "src/checker-worker.ts" },
  outdir: "dist",
  bundle: true,
  platform: "node",
  format: "esm",
  target: "node20",
  sourcemap: true,
  alias: { "bend-infrastructure": "../vendor/bend2/bend2/bend.ts" },
  banner: { js: 'import { createRequire as __createRequire } from "node:module"; const require = __createRequire(import.meta.url);' },
  logLevel: "info",
});
await cp("../vendor/bend2/bend2/base.bend", "dist/base.bend");
