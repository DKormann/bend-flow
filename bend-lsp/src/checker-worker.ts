import { parentPort } from "node:worker_threads";
import { checkBend } from "./checker-core.js";
import type { CheckRequest } from "./checker-protocol.js";

let queue = Promise.resolve();
parentPort?.on("message", (request: CheckRequest) => {
  queue = queue
    .then(async () => parentPort?.postMessage(await checkBend(request)))
    .catch((error) => parentPort?.postMessage({
      id: request.id,
      uri: request.uri,
      version: request.version,
      versions: {},
      diagnostics: [{
        uri: request.uri,
        start: 0,
        end: 1,
        message: error instanceof Error ? error.message : String(error),
        code: "checking",
      }],
      hovers: {},
      typedHovers: [],
      valuePreviews: [],
    }));
});
