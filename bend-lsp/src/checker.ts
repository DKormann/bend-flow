import { Worker } from "node:worker_threads";
import type { CheckRequest, CheckResult } from "./checker-protocol.js";

type Pending = { resolve: (result: CheckResult) => void; reject: (error: Error) => void };

export class BendChecker {
  private worker!: Worker;
  private pending = new Map<number, Pending>();
  private stopping = false;

  constructor() { this.spawn(); }

  private spawn(): void {
    this.worker = new Worker(new URL("./checker-worker.js", import.meta.url));
    this.worker.on("message", (result: CheckResult) => {
      const pending = this.pending.get(result.id);
      if (!pending) return;
      this.pending.delete(result.id);
      pending.resolve(result);
    });
    const fail = (cause: unknown): void => {
      if (this.stopping) return;
      const error = cause instanceof Error ? cause : new Error(`Bend checker worker exited: ${String(cause)}`);
      const pending = [...this.pending.values()];
      this.pending.clear();
      for (const request of pending) request.reject(error);
    };
    this.worker.on("error", fail);
    this.worker.on("exit", (code) => { if (code !== 0) fail(code); });
  }

  check(request: CheckRequest): Promise<CheckResult> {
    if (this.worker.threadId === -1) this.spawn();
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
