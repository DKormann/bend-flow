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
  type Diagnostic,
  type Hover,
  type InlayHint,
  type InitializeResult,
  type SemanticTokens,
} from "vscode-languageserver/node.js";
import { TextDocument } from "vscode-languageserver-textdocument";
import { definitionAt, type TextOverlay } from "./analyzer.js";
import { BendChecker } from "./checker.js";
import type { CheckDiagnostic, CheckResult } from "./checker-protocol.js";
import { TOKEN_MODIFIERS, TOKEN_TYPES, tokenizeBend } from "./semantic-tokens.js";

const connection = createConnection(ProposedFeatures.all);
const documents = new TextDocuments(TextDocument);
const checker = new BendChecker();
const checkTimers = new Map<string, NodeJS.Timeout>();
const importsByUri = new Map<string, Set<string>>();
const diagnosticTargets = new Map<string, Set<string>>();
const checkResults = new Map<string, CheckResult>();
let nextCheckId = 1;

function supported(document: TextDocument): boolean {
  return document.languageId === "bend" || document.languageId === "bend2";
}

function pathFromUri(uri: string): string | null {
  try { return uri.startsWith("file:") ? fileURLToPath(uri) : null; } catch { return null; }
}

function overlays(): TextOverlay[] {
  return documents.all().flatMap((document) => {
    const file = pathFromUri(document.uri);
    return file && supported(document) ? [{ path: file, uri: document.uri, text: document.getText() }] : [];
  });
}

connection.onInitialize((): InitializeResult => ({
  capabilities: {
    textDocumentSync: TextDocumentSyncKind.Full,
    definitionProvider: true,
    hoverProvider: true,
    inlayHintProvider: true,
    semanticTokensProvider: {
      legend: { tokenTypes: [...TOKEN_TYPES], tokenModifiers: [...TOKEN_MODIFIERS] },
      full: true,
    },
  },
  serverInfo: { name: "bend-lsp", version: "0.2.0" },
}));

function hoverToken(document: TextDocument, offset: number): string {
  const source = document.getText();
  let start = offset;
  let end = offset;
  while (start > 0 && /[A-Za-z0-9_.]/.test(source[start - 1])) start--;
  while (end < source.length && /[A-Za-z0-9_.]/.test(source[end])) end++;
  return source.slice(start, end);
}

connection.onHover((params): Hover | null => {
  const document = documents.get(params.textDocument.uri);
  if (!document || !supported(document)) return null;
  const offset = document.offsetAt(params.position);
  const result = checkResults.get(document.uri);
  const typed = result?.typedHovers
    .filter((item) => item.uri === document.uri && item.start <= offset && offset <= item.end)
    .sort((left, right) => (left.end - left.start) - (right.end - right.start))[0];
  if (typed) return { contents: { kind: MarkupKind.Markdown, value: typed.value } };
  const token = hoverToken(document, offset);
  const hovers = result?.hovers;
  const value = hovers?.[token] ?? hovers?.[token.split(".").at(-1) ?? token];
  return value ? { contents: { kind: MarkupKind.Markdown, value } } : null;
});

connection.onDefinition(async (params): Promise<Definition | null> => {
  const document = documents.get(params.textDocument.uri);
  if (!document || !supported(document)) return null;
  const file = pathFromUri(document.uri);
  if (!file) return null;
  try {
    const found = await definitionAt(
      file,
      document.uri,
      document.getText(),
      document.offsetAt(params.position),
      overlays(),
    );
    if (!found) return null;
    return {
      uri: found.uri,
      range: {
        start: documentForUri(found.uri)?.positionAt(found.range.start) ?? offsetPosition(found.uri, found.range.start),
        end: documentForUri(found.uri)?.positionAt(found.range.end) ?? offsetPosition(found.uri, found.range.end),
      },
    };
  } catch (error) {
    connection.console.error(error instanceof Error ? error.stack ?? error.message : String(error));
    return null;
  }
});

function documentForUri(uri: string): TextDocument | undefined {
  return documents.get(uri);
}

function offsetPosition(uri: string, offset: number): { line: number; character: number } {
  const file = pathFromUri(uri);
  if (!file) return { line: 0, character: 0 };
  try {
    return TextDocument.create(uri, "bend", 0, requireText(file)).positionAt(offset);
  } catch {
    return { line: 0, character: 0 };
  }
}

function requireText(file: string): string {
  // Kept here rather than cached so imported edits on disk are immediately visible.
  return fs.readFileSync(file, "utf8");
}

connection.languages.inlayHint.on((params): InlayHint[] => {
  const document = documents.get(params.textDocument.uri);
  if (!document || !supported(document)) return [];
  const result = checkResults.get(document.uri);
  if (!result) return [];
  const rangeStart = document.offsetAt(params.range.start);
  const rangeEnd = document.offsetAt(params.range.end);
  return result.valuePreviews
    .filter((preview) => preview.uri === document.uri && preview.offset >= rangeStart && preview.offset <= rangeEnd)
    .map((preview) => ({
      position: document.positionAt(preview.offset),
      label: ` ${preview.value}`,
      tooltip: "Computed by the Bend interpreter",
      paddingLeft: true,
    }));
});

connection.languages.semanticTokens.on((params): SemanticTokens => {
  const document = documents.get(params.textDocument.uri);
  const builder = new SemanticTokensBuilder();
  if (!document || !supported(document)) return builder.build();
  for (const token of tokenizeBend(document.getText())) {
    const start = document.positionAt(token.start);
    const end = document.positionAt(token.start + token.length);
    const tokenType = TOKEN_TYPES.indexOf(token.type);
    const modifiers = (token.modifiers ?? []).reduce(
      (bits, modifier) => bits | (1 << TOKEN_MODIFIERS.indexOf(modifier)),
      0,
    );
    if (start.line === end.line) {
      builder.push(start.line, start.character, token.length, tokenType, modifiers);
    } else {
      for (let line = start.line; line <= end.line; line++) {
        const from = line === start.line ? start.character : 0;
        const to = line === end.line ? end.character : document.getText({
          start: { line, character: 0 }, end: { line: line + 1, character: 0 },
        }).replace(/\r?\n$/, "").length;
        if (to > from) builder.push(line, from, to - from, tokenType, modifiers);
      }
    }
  }
  return builder.build();
});

function importedUris(document: TextDocument): Set<string> {
  const found = new Set<string>();
  if (!pathFromUri(document.uri)) return found;
  for (const line of document.getText().split("\n")) {
    const value = line.trim();
    if (!value || value.startsWith("#")) continue;
    const match = /^import\s+(\S+)(?:\s+as\s+[A-Za-z_]\w*)?\s*(?:#.*)?$/.exec(value);
    if (!match) break;
    if (match[1] !== "Base" && !/^0x[0-9a-f]+\//.test(match[1])) {
      try { found.add(new URL(match[1], document.uri).href); } catch { /* checker reports malformed imports */ }
    }
  }
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

function checkerOverlays(): Array<TextOverlay & { version: number }> {
  return documents.all().flatMap((document) => {
    const file = pathFromUri(document.uri);
    return file && supported(document)
      ? [{ path: file, uri: document.uri, text: document.getText(), version: document.version }]
      : [];
  });
}

function diagnosticDocument(uri: string): TextDocument | null {
  const open = documents.get(uri);
  if (open) return open;
  const file = pathFromUri(uri);
  if (!file) return null;
  try { return TextDocument.create(uri, "bend", 0, fs.readFileSync(file, "utf8")); } catch { return null; }
}

function lspDiagnostic(item: CheckDiagnostic): Diagnostic | null {
  const document = diagnosticDocument(item.uri);
  if (!document) return null;
  return {
    range: { start: document.positionAt(item.start), end: document.positionAt(item.end) },
    message: item.message,
    severity: DiagnosticSeverity.Error,
    source: "bend",
    code: item.code,
  };
}

async function check(uri: string): Promise<void> {
  const document = documents.get(uri);
  const file = document && pathFromUri(uri);
  if (!document || !supported(document) || !file) return;
  const result = await checker.check({
    id: nextCheckId++,
    uri,
    path: file,
    version: document.version,
    overlays: checkerOverlays(),
  });
  const current = documents.get(uri);
  if (!current || current.version !== result.version) return;
  for (const [overlayUri, version] of Object.entries(result.versions)) {
    const overlay = documents.get(overlayUri);
    if (overlay && overlay.version !== version) return;
  }

  checkResults.set(uri, result);
  void connection.languages.inlayHint.refresh().catch(() => { /* Client does not support refresh. */ });
  const grouped = new Map<string, CheckDiagnostic[]>();
  for (const item of result.diagnostics) grouped.set(item.uri, [...(grouped.get(item.uri) ?? []), item]);
  const previous = diagnosticTargets.get(uri) ?? new Set<string>();
  const targets = new Set([uri, ...previous, ...grouped.keys()]);
  diagnosticTargets.set(uri, new Set([uri, ...grouped.keys()]));
  for (const target of targets) {
    connection.sendDiagnostics({
      uri: target,
      version: documents.get(target)?.version,
      diagnostics: (grouped.get(target) ?? []).flatMap((item) => {
        const converted = lspDiagnostic(item);
        return converted ? [converted] : [];
      }),
    });
  }
}

function scheduleCheck(uri: string, delay = 250): void {
  const previous = checkTimers.get(uri);
  if (previous) clearTimeout(previous);
  checkTimers.set(uri, setTimeout(() => {
    checkTimers.delete(uri);
    void check(uri).catch((error) => connection.console.error(error instanceof Error ? error.stack ?? error.message : String(error)));
  }, delay));
}

documents.onDidOpen(({ document }) => {
  if (!supported(document)) return;
  importsByUri.set(document.uri, importedUris(document));
  scheduleCheck(document.uri, 0);
});

documents.onDidChangeContent(({ document }) => {
  if (!supported(document)) return;
  checkResults.delete(document.uri);
  importsByUri.set(document.uri, importedUris(document));
  for (const uri of dependentsOf(document.uri)) scheduleCheck(uri);
});

documents.onDidClose(({ document }) => {
  const dependents = dependentsOf(document.uri);
  const timer = checkTimers.get(document.uri);
  if (timer) clearTimeout(timer);
  checkTimers.delete(document.uri);
  importsByUri.delete(document.uri);
  checkResults.delete(document.uri);
  for (const target of diagnosticTargets.get(document.uri) ?? [document.uri]) {
    connection.sendDiagnostics({ uri: target, diagnostics: [] });
  }
  diagnosticTargets.delete(document.uri);
  for (const uri of dependents) if (uri !== document.uri) scheduleCheck(uri, 0);
});

connection.onShutdown(async () => checker.close());
documents.listen(connection);
connection.listen();
