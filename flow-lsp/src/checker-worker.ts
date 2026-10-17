import { parentPort } from "node:worker_threads";
import { checkFlow } from "./checker-core.js";
import type { FlowCheckRequest } from "./checker-protocol.js";

let queue = Promise.resolve();
parentPort?.on("message", (request: FlowCheckRequest) => {
  queue = queue.then(async () => parentPort?.postMessage(await checkFlow(request))).catch((error) => {
    parentPort?.postMessage({
      id: request.id,
      uri: request.uri,
      version: request.version,
      diagnostics: [{ uri: request.uri, start: 0, end: 1, message: error instanceof Error ? error.message : String(error), code: "lowering" }],
      hovers: {},
      typedHovers: [],
      valuePreviews: [],
    });
  });
});
