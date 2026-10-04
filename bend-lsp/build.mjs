import { build } from "esbuild";
import { cp, mkdir, rm } from "node:fs/promises";

await rm("dist", { recursive: true, force: true });
await mkdir("dist/test", { recursive: true });

const common = {
  bundle: true,
  platform: "node",
  format: "esm",
  target: "node20",
  sourcemap: true,
  alias: { "bend-infrastructure": "../vendor/bend2/bend2/bend.ts" },
  banner: { js: 'import { createRequire as __createRequire } from "node:module"; const require = __createRequire(import.meta.url);' },
  logLevel: "info",
};

await build({
  ...common,
  entryPoints: ["src/server.ts", "src/checker-worker.ts", "src/analyzer.ts", "src/semantic-tokens.ts"],
  outdir: "dist",
});
await build({
  ...common,
  entryPoints: ["src/test/analyzer.test.ts", "src/test/checker.test.ts", "src/test/semantic-tokens.test.ts"],
  outdir: "dist/test",
});
await cp("../vendor/bend2/bend2/base.bend", "dist/base.bend");
await cp("../vendor/bend2/bend2/base.bend", "dist/test/base.bend");
