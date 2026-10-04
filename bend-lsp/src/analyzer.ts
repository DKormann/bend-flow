import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { pathToFileURL } from "node:url";
import {
  BASE_BEND,
  book_nil,
  parse_book,
  term_lower,
  type Book,
  type HTerm,
  type LTerm,
  type Span,
} from "bend-infrastructure";

export type OffsetRange = { start: number; end: number };
export type OffsetLocation = { uri: string; range: OffsetRange };
export type TextOverlay = { path: string; uri: string; text: string };

type Import = { path: string; alias?: string; line: number };
type Source = {
  path: string;
  uri: string;
  text: string;
  body: string;
  namespace: string;
  aliases: Record<string, string>;
};
type Graph = {
  book: Book;
  root: Source;
  sources: Source[];
  declarations: Map<string, OffsetLocation>;
};
type Use = { start: number; end: number; target: OffsetLocation };

function fileKey(file: string): string {
  const key = path.resolve(file).replaceAll("\\", "/");
  return process.platform === "win32" ? key.toLowerCase() : key;
}

function sourceImports(text: string): Import[] {
  const result: Import[] = [];
  const lines = text.split("\n");
  for (let line = 0; line < lines.length; line++) {
    const value = lines[line].trim();
    if (!value || value.startsWith("#")) continue;
    const match = /^import\s+(\S+)(?:\s+as\s+([A-Za-z_]\w*))?\s*(?:#.*)?$/.exec(value);
    if (!match) break;
    result.push({ path: match[1], alias: match[2], line });
  }
  return result;
}

function withoutImports(text: string, imports: Import[]): string {
  const lines = text.split("\n");
  // Spaces keep every compiler span aligned with the editor document.
  for (const imported of imports) lines[imported.line] = " ".repeat(lines[imported.line].length);
  return lines.join("\n");
}

function qualified(namespace: string, name: string): string {
  return namespace ? `${namespace}.${name}` : name;
}

function scanDeclarations(source: Source, declarations: Map<string, OffsetLocation>): void {
  const top = /^\s*(def|law|type)\s+([A-Za-z_][A-Za-z0-9_.]*)/gm;
  const starts: Array<{ kind: string; name: string; start: number; bodyStart: number }> = [];
  for (const match of source.body.matchAll(top)) {
    const name = match[2];
    const start = match.index + match[0].lastIndexOf(name);
    starts.push({ kind: match[1], name, start, bodyStart: match.index + match[0].length });
    const key = qualified(source.namespace, name);
    if (!declarations.has(key)) {
      declarations.set(key, { uri: source.uri, range: { start, end: start + name.length } });
    }
  }

  for (let index = 0; index < starts.length; index++) {
    const declaration = starts[index];
    if (declaration.kind !== "type") continue;
    const end = starts[index + 1]?.start ?? source.body.length;
    const body = source.body.slice(declaration.bodyStart, end);
    const constructors = /^\s*([A-Za-z_][A-Za-z0-9_.]*)\s*\{/gm;
    for (const match of body.matchAll(constructors)) {
      const name = match[1];
      const start = declaration.bodyStart + match.index + match[0].indexOf(name);
      const key = qualified(source.namespace, name);
      if (!declarations.has(key)) {
        declarations.set(key, { uri: source.uri, range: { start, end: start + name.length } });
      }
    }
  }
}

async function loadGraph(entryPath: string, entryUri: string, entryText: string, overlays: TextOverlay[]): Promise<Graph> {
  const book = book_nil();
  const sources: Source[] = [];
  const declarations = new Map<string, OffsetLocation>();
  const seen = new Set<string>();
  const overlayMap = new Map(overlays.map((item) => [fileKey(item.path), item]));
  overlayMap.set(fileKey(entryPath), { path: entryPath, uri: entryUri, text: entryText });
  const projectRoot = path.dirname(path.resolve(entryPath));

  const load = async (file: string, namespace: string, uri?: string): Promise<Source | null> => {
    const key = fileKey(file);
    const open = overlayMap.get(key);
    if (seen.has(key)) return sources.find((source) => fileKey(source.path) === key) ?? null;
    if (!open && !fs.existsSync(file)) return null;
    seen.add(key);
    const text = open?.text ?? fs.readFileSync(file, "utf8");
    const imports = sourceImports(text);
    const aliases: Record<string, string> = Object.create(null) as Record<string, string>;

    for (const imported of imports) {
      if (imported.path === "Base" && !imported.alias) {
        await load(BASE_BEND, "", pathToFileURL(BASE_BEND).href);
        continue;
      }
      if (!imported.alias || !imported.path.endsWith(".bend") || /^0x[0-9a-f]+\//.test(imported.path)) continue;
      const childPath = path.resolve(path.dirname(file), imported.path);
      const childNamespace = path.relative(projectRoot, childPath).replaceAll("\\", "/").replace(/\.bend$/, "");
      aliases[imported.alias] = childNamespace;
      await load(childPath, childNamespace);
    }

    const source: Source = {
      path: path.resolve(file),
      uri: open?.uri ?? uri ?? pathToFileURL(file).href,
      text,
      body: withoutImports(text, imports),
      namespace,
      aliases,
    };
    sources.push(source);
    scanDeclarations(source, declarations);
    try {
      parse_book(book, path.dirname(source.path).replaceAll("\\", "/") + "/", source.body, namespace, aliases);
    } catch {
      // A partially typed document still leaves useful declarations in the book.
    }
    return source;
  };

  const root = await load(entryPath, "", entryUri);
  if (!root) throw new Error(`Unable to read ${entryPath}`);
  return { book, root, sources, declarations };
}

function nameRange(source: string, span: Span | undefined): OffsetRange | null {
  if (!span) return null;
  let start = span.beg;
  while (start < span.end && !/[A-Za-z_]/.test(source[start] ?? "")) start++;
  const match = /^[A-Za-z_][A-Za-z0-9_.]*/.exec(source.slice(start));
  return match ? { start, end: start + match[0].length } : null;
}

function spanLocation(span: Span | undefined, graph: Graph): OffsetLocation | null {
  if (!span) return null;
  const source = graph.sources.find((candidate) => candidate.body === span.src || candidate.text === span.src);
  if (!source) return null;
  const range = nameRange(span.src, span);
  return range ? { uri: source.uri, range } : null;
}

function collectUses(term: LTerm, graph: Graph, root: Source, uses: Use[], binders = new Map<number, OffsetLocation>()): void {
  const addGlobal = (name: string, span: Span | undefined): void => {
    if (!span || span.src !== root.body) return;
    const range = nameRange(span.src, span);
    const target = graph.declarations.get(name);
    if (range && target) uses.push({ ...range, target });
  };
  const addLocal = (index: number, span: Span | undefined, scope: Map<number, OffsetLocation>): void => {
    if (!span || span.src !== root.body) return;
    const range = nameRange(span.src, span);
    const target = scope.get(index);
    if (range && target) uses.push({ ...range, target });
  };
  const walk = (value: LTerm, scope: Map<number, OffsetLocation>): void => {
    switch (value.$) {
      case "Var": addLocal(value.i, value.s, scope); return;
      case "Ref": addGlobal(value.k, value.s); return;
      case "ADT": addGlobal(value.k, value.s); value.x.forEach((item: LTerm) => walk(item, scope)); return;
      case "Ctr": addGlobal(value.k, value.s); value.x.forEach((item: LTerm) => walk(item, scope)); return;
      case "Let": {
        value.v.forEach((item: LTerm) => walk(item, scope));
        const nested = new Map(scope);
        value.i.forEach((id: number, index: number) => {
          const target = spanLocation(value.s, graph);
          if (target) nested.set(id, index === 0 ? target : target);
        });
        walk(value.f, nested);
        return;
      }
      case "All": {
        walk(value.A, scope);
        const nested = new Map(scope);
        const target = spanLocation(value.s, graph);
        if (target) nested.set(value.i, target);
        walk(value.B, nested);
        return;
      }
      case "Lam": {
        const nested = new Map(scope);
        const target = spanLocation(value.s, graph);
        if (target) nested.set(value.i, target);
        walk(value.f, nested);
        return;
      }
      case "Sub": walk(value.f, scope); return;
      case "Typ": walk(value.g, scope); return;
      case "Min": walk(value.a, scope); walk(value.b, scope); return;
      case "App": walk(value.f, scope); walk(value.x, scope); return;
      case "Mat": walk(value.h, scope); walk(value.m, scope); return;
      case "Eql": walk(value.a, scope); walk(value.b, scope); walk(value.T, scope); return;
      case "Rwt": walk(value.e, scope); walk(value.p, scope); walk(value.f, scope); return;
      case "Ann": walk(value.x, scope); walk(value.T, scope); return;
      case "Qua": case "Qnt": case "Lit": case "Efq": case "Rfl": case "Hol": return;
    }
  };
  walk(term, binders);
}

function collectBookUses(graph: Graph): Use[] {
  const uses: Use[] = [];
  for (const tld of Object.values(graph.book.tlds)) {
    const terms: HTerm[] = [tld.T];
    if (tld.$ === "Def" && tld.v) terms.push(tld.v);
    for (const term of terms) {
      try { collectUses(term_lower(term), graph, graph.root, uses); } catch { /* keep fallback navigation */ }
    }
  }
  for (const constructor of Object.values(graph.book.ctrs)) {
    try { collectUses(term_lower(constructor.T), graph, graph.root, uses); } catch { /* keep fallback navigation */ }
  }
  return uses;
}

function tokenAt(text: string, offset: number): { text: string; start: number; end: number } | null {
  let start = Math.min(offset, text.length);
  let end = start;
  while (start > 0 && /[A-Za-z0-9_.]/.test(text[start - 1])) start--;
  while (end < text.length && /[A-Za-z0-9_.]/.test(text[end])) end++;
  return start < end && /[A-Za-z_]/.test(text[start]) ? { text: text.slice(start, end), start, end } : null;
}

function importDefinition(entry: string, source: string, offset: number, overlays: TextOverlay[]): OffsetLocation | null {
  const token = tokenAt(source, offset)?.text ?? "";
  let lineOffset = 0;
  for (const line of source.split("\n")) {
    const match = /^\s*import\s+(\S+)(?:\s+as\s+([A-Za-z_]\w*))?/.exec(line);
    if (match) {
      const pathStart = lineOffset + line.indexOf(match[1]);
      const aliasStart = match[2] ? lineOffset + line.lastIndexOf(match[2]) : -1;
      const selected = pathStart <= offset && offset <= pathStart + match[1].length
        || aliasStart >= 0 && aliasStart <= offset && offset <= aliasStart + match[2].length
        || match[2] && token.startsWith(match[2] + ".");
      if (selected) {
        let target: string;
        if (match[1] === "Base") target = BASE_BEND;
        else if (/^0x[0-9a-f]+\//.test(match[1])) target = path.join(process.env.BEND_LIB ?? path.join(os.homedir(), ".bend", "lib"), match[1]);
        else {
          const named = /^([^/]+@[^/]+)\/(.+)$/.exec(match[1]);
          if (named) {
            try {
              const library = process.env.BEND_LIB ?? path.join(os.homedir(), ".bend", "lib");
              const hash = fs.readFileSync(path.join(library, "names", named[1]), "utf8").trim();
              target = path.join(library, hash, named[2]);
            } catch { return null; }
          } else target = path.resolve(path.dirname(entry), match[1]);
        }
        const overlay = overlays.find((item) => fileKey(item.path) === fileKey(target));
        if (!overlay && !fs.existsSync(target)) return null;
        const targetSource = overlay?.text ?? fs.readFileSync(target, "utf8");
        const uri = overlay?.uri ?? pathToFileURL(target).href;
        if (pathStart <= offset && offset <= pathStart + match[1].length || aliasStart >= 0 && aliasStart <= offset && offset <= aliasStart + (match[2]?.length ?? 0)) {
          return { uri, range: { start: 0, end: 0 } };
        }
        const symbol = match[2] ? token.slice(match[2].length + 1) : token;
        for (const declaration of targetSource.matchAll(/^\s*(?:def|law|type)\s+([A-Za-z_][A-Za-z0-9_.]*)/gm)) {
          if (declaration[1] !== symbol && declaration[1].split(".").at(-1) !== symbol) continue;
          const start = declaration.index + declaration[0].lastIndexOf(declaration[1]);
          return { uri, range: { start, end: start + declaration[1].length } };
        }
        for (const constructor of targetSource.matchAll(/^\s*([A-Za-z_][A-Za-z0-9_.]*)\s*\{/gm)) {
          if (constructor[1] !== symbol && constructor[1].split(".").at(-1) !== symbol) continue;
          const start = constructor.index + constructor[0].indexOf(constructor[1]);
          return { uri, range: { start, end: start + constructor[1].length } };
        }
      }
    }
    lineOffset += line.length + 1;
  }
  return null;
}

function fallbackDefinition(graph: Graph, offset: number): OffsetLocation | null {
  const token = tokenAt(graph.root.text, offset);
  if (!token) return null;
  const dot = token.text.indexOf(".");
  if (dot > 0 && graph.root.aliases[token.text.slice(0, dot)]) {
    const canonical = graph.root.aliases[token.text.slice(0, dot)] + token.text.slice(dot);
    return graph.declarations.get(canonical) ?? null;
  }
  return graph.declarations.get(qualified(graph.root.namespace, token.text))
    ?? graph.declarations.get(token.text)
    ?? null;
}

export async function definitionAt(
  file: string,
  uri: string,
  text: string,
  offset: number,
  overlays: TextOverlay[] = [],
): Promise<OffsetLocation | null> {
  const graph = await loadGraph(file, uri, text, overlays);
  const use = collectBookUses(graph)
    .filter((candidate) => candidate.start <= offset && offset <= candidate.end)
    .sort((a, b) => (a.end - a.start) - (b.end - b.start))[0];
  return use?.target ?? fallbackDefinition(graph, offset) ?? importDefinition(file, text, offset, overlays);
}
