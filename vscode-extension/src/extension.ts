import * as path from "node:path";
import type { ExtensionContext } from "vscode";
import {
  LanguageClient,
  TransportKind,
  type LanguageClientOptions,
  type ServerOptions,
} from "vscode-languageclient/node.js";

const clients: LanguageClient[] = [];

function createClient(
  context: ExtensionContext,
  id: string,
  name: string,
  language: string,
  serverFile: string,
  debugPort: number,
): LanguageClient {
  const module = context.asAbsolutePath(path.join("server", serverFile));
  const serverOptions: ServerOptions = {
    run: { module, transport: TransportKind.stdio },
    debug: {
      module,
      transport: TransportKind.stdio,
      options: { execArgv: ["--nolazy", `--inspect=${debugPort}`] },
    },
  };
  const clientOptions: LanguageClientOptions = {
    documentSelector: [
      { scheme: "file", language },
      { scheme: "untitled", language },
    ],
  };
  return new LanguageClient(id, name, serverOptions, clientOptions);
}

export async function activate(context: ExtensionContext): Promise<void> {
  clients.push(
    createClient(context, "bend-lsp", "Bend Language Server", "bend", "server.js", 6009),
    createClient(context, "flow-lsp", "Flow Language Server", "flow", "flow-server.js", 6010),
  );
  await Promise.all(clients.map((client) => client.start()));
  context.subscriptions.push({ dispose: () => { for (const client of clients) void client.stop(); } });
}

export async function deactivate(): Promise<void> {
  await Promise.all(clients.map((client) => client.stop()));
  clients.length = 0;
}
