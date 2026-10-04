import { Worker } from "node:worker_threads";
import type { FlowCheckRequest, FlowCheckResult } from "./checker-protocol.js";

type Pending = { resolve: (result: FlowCheckResult) => void; reject: (error: Error) => void };

export class FlowChecker {
  private worker = new Worker(new URL("./flow-checker-worker.js", import.meta.url));
  private pending = new Map<number, Pending>();
  private stopping = false;

  constructor() {
    this.listen();
  }

  private listen(): void {
    this.worker.on("message", (result: FlowCheckResult) => {
      const pending = this.pending.get(result.id);
      if (!pending) return;
      this.pending.delete(result.id);
      pending.resolve(result);
    });
    const fail = (cause: unknown): void => {
      if (this.stopping) return;
      const error = cause instanceof Error ? cause : new Error(String(cause));
      for (const pending of this.pending.values()) pending.reject(error);
      this.pending.clear();
    };
    this.worker.on("error", fail);
    this.worker.on("exit", (code) => { if (code !== 0) fail(`Flow checker exited with ${code}`); });
  }

  check(request: FlowCheckRequest): Promise<FlowCheckResult> {
    return new Promise((resolve, reject) => {
      this.pending.set(request.id, { resolve, reject });
      this.worker.postMessage(request);
    });
  }

  async close(): Promise<void> {
    this.stopping = true;
    await this.worker.terminate();
  }
}
