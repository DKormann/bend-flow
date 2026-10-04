#!/usr/bin/env node
import * as fs from "node:fs";
import { fileURLToPath } from "node:url";
import {
  createConnection,
  DiagnosticSeverity,
  MarkupKind,
  ProposedFeatures,
  SemanticTokensBuilder,
  TextDocuments,
  TextDocumentSyncKind,
  type Definition,
  type Hover,
  type InitializeResult,
  type SemanticTokens,
} from "vscode-languageserver/node.js";
import { TextDocument } from "vscode-languageserver-textdocument";
import { FlowChecker } from "./checker.js";
import type { FlowCheckResult } from "./checker-protocol.js";
import { FlowParseError } from "./expression-parser.js";
import { flowProjectDefinitionAt } from "./project-navigation.js";
import { parseFlow } from "./parser.js";
import { FLOW_TOKEN_MODIFIERS, FLOW_TOKEN_TYPES, tokenizeFlow } from "./semantic-tokens.js";

const connection = createConnection(ProposedFeatures.all);
const documents = new TextDocuments(TextDocument);
const checker = new FlowChecker();
const timers = new Map<string, NodeJS.Timeout>();
const checkResults = new Map<string, FlowCheckResult>();
const diagnosticTargets = new Map<string, Set<string>>();
const importsByUri = new Map<string, Set<string>>();
let nextCheckId = 1;

connection.onInitialize((): InitializeResult => ({
  capabilities: {
    textDocumentSync: TextDocumentSyncKind.Full,
    definitionProvider: true,
    hoverProvider: true,
    semanticTokensProvider: {
      legend: { tokenTypes: [...FLOW_TOKEN_TYPES], tokenModifiers: [...FLOW_TOKEN_MODIFIERS] },
      full: true,
    },
  },
  serverInfo: { name: "flow-lsp", version: "0.1.0" },
}));

function tokenAt(document: TextDocument, offset: number): string {
  const source = document.getText();
  let start = offset;
  let end = offset;
  while (start > 0 && /[A-Za-z0-9_.]/.test(source[start - 1])) start--;
  while (end < source.length && /[A-Za-z0-9_.]/.test(source[end])) end++;
  return source.slice(start, end);
}

connection.onHover((params): Hover | null => {
  const document = documents.get(params.textDocument.uri);
  if (!document || document.languageId !== "flow") return null;
  const offset = document.offsetAt(params.position);
  const result = checkResults.get(document.uri);
  const typed = result?.typedHovers
    .filter((item) => item.start <= offset && offset <= item.end)
    .sort((left, right) => (left.end - left.start) - (right.end - right.start))[0];
  if (typed) return { contents: { kind: MarkupKind.Markdown, value: typed.value } };
  const token = tokenAt(document, offset);
  const hovers = result?.hovers;
  const value = hovers?.[token] ?? hovers?.[token.split(".").at(-1) ?? token];
  return value ? { contents: { kind: MarkupKind.Markdown, value } } : null;
});

connection.onDefinition((params): Definition | null => {
  const document = documents.get(params.textDocument.uri);
  if (!document || document.languageId !== "flow") return null;
  try {
    const file = document.uri.startsWith("file:") ? fileURLToPath(document.uri) : "untitled.flow";
    const overlays = documents.all().flatMap((item) => {
      if (!item.uri.startsWith("file:") || item.languageId !== "flow") return [];
      try { return [{ path: fileURLToPath(item.uri), uri: item.uri, text: item.getText() }]; } catch { return []; }
    });
    const found = flowProjectDefinitionAt(file, document.uri, document.getText(), document.offsetAt(params.position), overlays);
    if (!found) return null;
    const target = documents.get(found.uri);
    let targetDocument = target;
    if (!targetDocument && found.uri.startsWith("file:")) {
      try { targetDocument = TextDocument.create(found.uri, found.uri.endsWith(".flow") ? "flow" : "bend", 0, fs.readFileSync(fileURLToPath(found.uri), "utf8")); } catch { /* target vanished */ }
    }
    if (!targetDocument) return null;
    return {
      uri: found.uri,
      range: { start: targetDocument.positionAt(found.range.start), end: targetDocument.positionAt(found.range.end) },
    };
  } catch {
    return null;
  }
});

function importUris(document: TextDocument): Set<string> {
  const found = new Set<string>();
  try {
    for (const statement of parseFlow(document.getText()).statements) {
      if (statement.kind !== "ImportStatement" || statement.path === "Base"
        || /^0x[0-9a-f]+\//.test(statement.path) || /^[^/]+@[^/]+\//.test(statement.path)) continue;
      try { found.add(new URL(statement.path, document.uri).href); } catch {}
    }
  } catch {}
  return found;
}

function dependentsOf(uri: string): Set<string> {
  const result = new Set([uri]);
  let changed = true;
  while (changed) {
    changed = false;
    for (const [candidate, imports] of importsByUri) {
      if (result.has(candidate) || ![...imports].some((item) => result.has(item))) continue;
      result.add(candidate);
      changed = true;
    }
  }
  return result;
}

function scheduleCheck(document: TextDocument): void {
  const previous = timers.get(document.uri);
  if (previous) clearTimeout(previous);
  timers.set(document.uri, setTimeout(() => {
    timers.delete(document.uri);
    const version = document.version;
    let file: string;
    try { file = document.uri.startsWith("file:") ? fileURLToPath(document.uri) : "untitled.flow"; }
    catch { file = "untitled.flow"; }
    const overlays = documents.all().flatMap((item) => {
      if (!item.uri.startsWith("file:") || item.languageId !== "flow") return [];
      try { return [{ path: fileURLToPath(item.uri), uri: item.uri, text: item.getText(), version: item.version }]; } catch { return []; }
    });
    void checker.check({ id: nextCheckId++, uri: document.uri, path: file, text: document.getText(), version, overlays }).then((result) => {
      const current = documents.get(result.uri);
      if (!current || current.version !== result.version) return;
      checkResults.set(result.uri, result);
      const grouped = new Map<string, typeof result.diagnostics>();
      for (const item of result.diagnostics) grouped.set(item.uri, [...(grouped.get(item.uri) ?? []), item]);
      const previousTargets = diagnosticTargets.get(result.uri) ?? new Set<string>();
      const targets = new Set([result.uri, ...previousTargets, ...grouped.keys()]);
      diagnosticTargets.set(result.uri, new Set([result.uri, ...grouped.keys()]));
      for (const targetUri of targets) {
        let targetDocument = documents.get(targetUri);
        if (!targetDocument && targetUri.startsWith("file:")) {
          try { targetDocument = TextDocument.create(targetUri, targetUri.endsWith(".flow") ? "flow" : "bend", 0, fs.readFileSync(fileURLToPath(targetUri), "utf8")); } catch { continue; }
        }
        if (!targetDocument) continue;
        connection.sendDiagnostics({
          uri: targetUri,
          version: documents.get(targetUri)?.version,
          diagnostics: (grouped.get(targetUri) ?? []).map((item) => ({
            range: { start: targetDocument.positionAt(item.start), end: targetDocument.positionAt(item.end) },
            message: item.message,
            severity: DiagnosticSeverity.Error,
            source: "bend via flow",
            code: item.code,
          })),
        });
      }
    }).catch((error) => connection.console.error(error instanceof Error ? error.stack ?? error.message : String(error)));
  }, 250));
}

function validate(document: TextDocument): void {
  if (document.languageId !== "flow") return;
  checkResults.delete(document.uri);
  try {
    parseFlow(document.getText());
    importsByUri.set(document.uri, importUris(document));
    for (const uri of dependentsOf(document.uri)) {
      const dependent = documents.get(uri);
      if (dependent) scheduleCheck(dependent);
    }
  } catch (error) {
    const previous = timers.get(document.uri);
    if (previous) clearTimeout(previous);
    timers.delete(document.uri);
    const span = error instanceof FlowParseError ? error.span : { start: 0, end: 1 };
    connection.sendDiagnostics({
      uri: document.uri,
      version: document.version,
      diagnostics: [{
        range: {
          start: document.positionAt(span.start),
          end: document.positionAt(Math.max(span.end, span.start + 1)),
        },
        message: error instanceof Error ? error.message : String(error),
        severity: DiagnosticSeverity.Error,
        source: "flow",
        code: "parsing",
      }],
    });
  }
}

connection.languages.semanticTokens.on((params): SemanticTokens => {
  const document = documents.get(params.textDocument.uri);
  const builder = new SemanticTokensBuilder();
  if (!document || document.languageId !== "flow") return builder.build();
  for (const token of tokenizeFlow(document.getText())) {
    const start = document.positionAt(token.start);
    const end = document.positionAt(token.start + token.length);
    const tokenType = FLOW_TOKEN_TYPES.indexOf(token.type);
    const modifiers = (token.modifiers ?? []).reduce(
      (bits, modifier) => bits | (1 << FLOW_TOKEN_MODIFIERS.indexOf(modifier)),
      0,
    );
    if (start.line === end.line) builder.push(start.line, start.character, token.length, tokenType, modifiers);
  }
  return builder.build();
});

documents.onDidOpen(({ document }) => validate(document));
documents.onDidChangeContent(({ document }) => validate(document));
documents.onDidClose(({ document }) => {
  const dependents = dependentsOf(document.uri);
  const timer = timers.get(document.uri);
  if (timer) clearTimeout(timer);
  timers.delete(document.uri);
  importsByUri.delete(document.uri);
  checkResults.delete(document.uri);
  for (const target of diagnosticTargets.get(document.uri) ?? [document.uri]) connection.sendDiagnostics({ uri: target, diagnostics: [] });
  diagnosticTargets.delete(document.uri);
  for (const uri of dependents) {
    const dependent = documents.get(uri);
    if (dependent && uri !== document.uri) scheduleCheck(dependent);
  }
});
connection.onShutdown(async () => checker.close());
documents.listen(connection);
connection.listen();
