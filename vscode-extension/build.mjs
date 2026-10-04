import { build } from "esbuild";
import { cp, mkdir, rm } from "node:fs/promises";

await rm("dist", { recursive: true, force: true });
await rm("server", { recursive: true, force: true });
await mkdir("dist", { recursive: true });
await mkdir("server", { recursive: true });

await build({
  entryPoints: ["src/extension.ts"],
  outfile: "dist/extension.cjs",
  bundle: true,
  platform: "node",
  format: "cjs",
  target: "node20",
  external: ["vscode"],
  sourcemap: true,
  logLevel: "info",
});

await cp("../bend-lsp/dist/server.js", "server/server.js");
await cp("../bend-lsp/dist/server.js.map", "server/server.js.map");
await cp("../bend-lsp/dist/checker-worker.js", "server/checker-worker.js");
await cp("../bend-lsp/dist/checker-worker.js.map", "server/checker-worker.js.map");
await cp("../bend-lsp/dist/base.bend", "server/base.bend");
await cp("../flow-lsp/dist/server.js", "server/flow-server.js");
await cp("../flow-lsp/dist/server.js.map", "server/flow-server.js.map");
await cp("../flow-lsp/dist/flow-checker-worker.js", "server/flow-checker-worker.js");
await cp("../flow-lsp/dist/flow-checker-worker.js.map", "server/flow-checker-worker.js.map");
