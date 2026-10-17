import { Worker } from "node:worker_threads";
import type { FlowCheckRequest, FlowCheckResult } from "./checker-protocol.js";

type Pending = {
  request: FlowCheckRequest;
  resolve: (result: FlowCheckResult) => void;
  reject: (error: Error) => void;
  timer: NodeJS.Timeout;
};

const CHECK_TIMEOUT_MS = 10_000;

export class FlowChecker {
  private worker!: Worker;
  private pending = new Map<number, Pending>();
  private stopping = false;

  constructor() { this.spawn(); }

  private spawn(): void {
    const worker = new Worker(new URL("./flow-checker-worker.js", import.meta.url));
    this.worker = worker;
    worker.on("message", (result: FlowCheckResult) => {
      if (worker !== this.worker) return;
      const pending = this.pending.get(result.id);
      if (!pending) return;
      clearTimeout(pending.timer);
      this.pending.delete(result.id);
      pending.resolve(result);
    });
    const fail = (cause: unknown): void => {
      if (this.stopping || worker !== this.worker) return;
      this.restart(cause instanceof Error ? cause.message : String(cause));
    };
    worker.on("error", fail);
    worker.on("exit", (code) => { if (code !== 0) fail(`Flow checker exited with ${code}`); });
  }

  private failure(request: FlowCheckRequest, message: string): FlowCheckResult {
    return {
      id: request.id,
      uri: request.uri,
      version: request.version,
      diagnostics: [{ uri: request.uri, start: 0, end: 1, message, code: "checking" }],
      hovers: {},
      typedHovers: [],
      valuePreviews: [],
    };
  }

  private restart(reason: string): void {
    const old = this.worker;
    const pending = [...this.pending.values()];
    this.pending.clear();
    for (const item of pending) {
      clearTimeout(item.timer);
      item.resolve(this.failure(item.request, reason));
    }
    if (!this.stopping) this.spawn();
    void old.terminate();
  }

  check(request: FlowCheckRequest): Promise<FlowCheckResult> {
    return new Promise((resolve, reject) => {
      const timer = setTimeout(() => {
        if (!this.pending.has(request.id)) return;
        this.restart(`Flow checking timed out after ${CHECK_TIMEOUT_MS / 1000} seconds. The checker worker was restarted.`);
      }, CHECK_TIMEOUT_MS);
      timer.unref();
      this.pending.set(request.id, { request, resolve, reject, timer });
      this.worker.postMessage(request);
    });
  }

  async close(): Promise<void> {
    this.stopping = true;
    for (const pending of this.pending.values()) {
      clearTimeout(pending.timer);
      pending.reject(new Error("Flow checker closed"));
    }
    this.pending.clear();
    await this.worker.terminate();
  }
}
