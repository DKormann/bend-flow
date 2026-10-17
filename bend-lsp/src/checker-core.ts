import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { pathToFileURL } from "node:url";
import { book_load, book_nil, book_valid, err_show, parse_book, term_lower, term_show, term_snf, type Book, type Err } from "bend-infrastructure";
import type { CheckDiagnostic, CheckRequest, CheckResult, TypedHover, ValuePreview } from "./checker-protocol.js";

type StagedSource = { original: string; staged: string; uri: string; text: string };

function key(file: string): string {
  const value = path.resolve(file).replaceAll("\\", "/");
  return process.platform === "win32" ? value.toLowerCase() : value;
}

function mirrorPath(file: string, root: string): string {
  const absolute = path.resolve(file);
  const parsed = path.parse(absolute);
  const volume = parsed.root.replace(/[^A-Za-z0-9]/g, "") || "root";
  return path.join(root, volume, absolute.slice(parsed.root.length));
}

function imports(text: string): string[] {
  const found: string[] = [];
  for (const line of text.split("\n")) {
    const value = line.trim();
    if (!value || value.startsWith("#")) continue;
    const match = /^import\s+(\S+)(?:\s+as\s+[A-Za-z_]\w*)?\s*(?:#.*)?$/.exec(value);
    if (!match) break;
    if (match[1] !== "Base") found.push(match[1]);
  }
  return found;
}

function stageProject(request: CheckRequest, runRoot: string): { entry: string; sources: StagedSource[] } {
  const overlayMap = new Map(request.overlays.map((overlay) => [key(overlay.path), overlay]));
  const sources: StagedSource[] = [];
  const seen = new Set<string>();

  const stage = (file: string): void => {
    const id = key(file);
    if (seen.has(id)) return;
    seen.add(id);
    const overlay = overlayMap.get(id);
    if (!overlay && !fs.existsSync(file)) return;
    const text = overlay?.text ?? fs.readFileSync(file, "utf8");
    const staged = mirrorPath(file, runRoot);
    fs.mkdirSync(path.dirname(staged), { recursive: true });
    fs.writeFileSync(staged, text);
    sources.push({
      original: path.resolve(file),
      staged,
      uri: overlay?.uri ?? pathToFileURL(file).href,
      text,
    });
    for (const imported of imports(text)) {
      if (path.isAbsolute(imported) || /^0x[0-9a-f]+\//.test(imported) || /^[^/]+@[^/]+\//.test(imported)) continue;
      stage(path.resolve(path.dirname(file), imported));
    }
  };

  stage(request.path);
  return { entry: mirrorPath(request.path, runRoot), sources };
}

function errorMessage(error: Err): string {
  return err_show(error).replace(/\nLocation:[\s\S]*$/, "").trim();
}

function diagnosticSource(sources: StagedSource[], spanSource: string | undefined, fallback: StagedSource): StagedSource {
  return sources.find((source) => source.text === spanSource) ?? fallback;
}

function boundedRange(source: string, begin: number, end: number): { start: number; end: number } {
  const start = Math.max(0, Math.min(source.length, begin));
  const boundedEnd = Math.max(start, Math.min(source.length, end));
  return { start, end: boundedEnd === start && start < source.length ? start + 1 : boundedEnd };
}

function renderHovers(book: Book): Record<string, string> {
  const hovers: Record<string, string> = Object.create(null) as Record<string, string>;
  const add = (name: string, kind: string, type: unknown): void => {
    try {
      const signature = term_show(term_lower(type));
      const value = `**${kind} ${name}**\n\n\`\`\`bend\n${name} : ${signature}\n\`\`\``;
      hovers[name] = value;
      const leaf = name.split(".").at(-1)!;
      if (!(leaf in hovers)) hovers[leaf] = value;
    } catch { /* An incomplete term has no preview yet. */ }
  };
  for (const [name, tld] of Object.entries(book.tlds)) add(name, tld.$ === "ADT" ? "type" : "def", tld.T);
  for (const [name, constructor] of Object.entries(book.ctrs)) add(name, "constructor", constructor.T);
  return hovers;
}

function compilerSource(text: string): string {
  const lines = text.split("\n");
  for (let index = 0; index < lines.length; index++) {
    const value = lines[index].trim();
    if (!value || value.startsWith("#")) continue;
    if (/^import(?:\s|$)/.test(value)) lines[index] = "";
    else break;
  }
  return lines.join("\n");
}

function sourceOffset(source: StagedSource, compilerText: string, offset: number): number {
  if (source.text === compilerText) return offset;
  const before = compilerText.slice(0, offset);
  const line = before.split("\n").length - 1;
  const column = offset - before.lastIndexOf("\n") - 1;
  const lines = source.text.split("\n");
  let result = 0;
  for (let index = 0; index < line; index++) result += (lines[index]?.length ?? 0) + 1;
  return result + column;
}

function renderTypedHovers(book: Book, sources: StagedSource[]): TypedHover[] {
  const result: TypedHover[] = [];
  const seen = new Set<string>();
  const add = (span: { src: string; beg: number; end: number } | undefined, name: string, type: any): void => {
    if (!span || name === "_") return;
    const source = sources.find((item) => item.text === span.src || compilerSource(item.text) === span.src);
    if (!source) return;
    let compilerStart = span.beg;
    while (compilerStart < span.end && !/[A-Za-z_]/.test(span.src[compilerStart] ?? "")) compilerStart++;
    const match = /^[A-Za-z_][A-Za-z0-9_.]*/.exec(span.src.slice(compilerStart));
    const compilerEnd = match ? compilerStart + match[0].length : span.end;
    const start = sourceOffset(source, span.src, compilerStart);
    const end = sourceOffset(source, span.src, compilerEnd);
    const key = `${source.uri}:${start}:${end}`;
    if (seen.has(key)) return;
    try {
      const actual = type?.$ === "Var" && type.v ? type.v : type;
      const shown = term_show(term_lower(actual));
      result.push({ uri: source.uri, start, end, value: `\`\`\`bend\n${name} : ${shown}\n\`\`\`` });
      seen.add(key);
    } catch { /* A partial checker term has no type preview. */ }
  };
  const walk = (term: any): void => {
    if (!term || typeof term !== "object") return;
    switch (term.$) {
      case "Ann":
        if (term.x?.$ === "Var") add(term.x.s, term.x.k, term.T);
        walk(term.x);
        return;
      case "Let":
        if (term.k?.length && term.v?.length) add(term.s, term.k[0], term.v[0]?.T);
        term.v.forEach(walk); walk(term.f); return;
      case "All": add(term.s, term.k, term.A); walk(term.A); walk(term.B); return;
      case "Lam": walk(term.f); return;
      case "Sub": walk(term.f); return;
      case "Typ": walk(term.g); return;
      case "Min": walk(term.a); walk(term.b); return;
      case "App": walk(term.f); walk(term.x); return;
      case "ADT": case "Ctr": term.x.forEach(walk); return;
      case "Mat": walk(term.h); walk(term.m); return;
      case "Eql": walk(term.a); walk(term.b); walk(term.T); return;
      case "Rwt": walk(term.e); walk(term.p); walk(term.f); return;
    }
  };
  for (const tld of Object.values(book.tlds)) {
    if (tld.$ !== "Def") continue;
    try { walk(term_lower(tld.T)); } catch {}
    if (tld.e) walk(tld.e);
  }
  return result;
}

function errorCode(error: Err, checking: boolean): CheckDiagnostic["code"] {
  if (checking) return "checking";
  const expected = typeof error.exp === "string" ? error.exp : "";
  return /import|file|hash|namespace|cycle|BEND_HUB/i.test(expected) ? "imports" : "parsing";
}

type SourceDefinition = { name: string; start: number; returnType?: string };

function sourceDefinitions(source: string): SourceDefinition[] {
  const definitions: SourceDefinition[] = [];
  const pattern = /^def\s+([A-Za-z_][A-Za-z0-9_.]*)\s*\([^\n]*\)\s*(?:->\s*(.+?)\s*)?:\s*(?:#.*)?$/gm;
  for (let match = pattern.exec(source); match; match = pattern.exec(source)) {
    definitions.push({ name: match[1], start: match.index, returnType: match[2] });
  }
  return definitions;
}

/** Evaluate a #? expression, or the surrounding argument-free top-level def. */
function renderValuePreviews(book: Book, source: StagedSource): ValuePreview[] {
  const result: ValuePreview[] = [];
  const definitions = sourceDefinitions(source.text);
  const markers = /#\?/g;
  let previewId = 0;
  for (let marker = markers.exec(source.text); marker; marker = markers.exec(source.text)) {
    const lineEnd = source.text.indexOf("\n", marker.index);
    const end = lineEnd < 0 ? source.text.length : lineEnd;
    const expression = source.text.slice(marker.index + marker[0].length, end).trim();
    let evaluationBook = book;
    let definition: any;

    try {
      if (expression) {
        // Let Bend parse, resolve, infer, and check the expression by placing it
        // in a private zero-argument definition. A copy keeps previews out of
        // diagnostics, navigation, and subsequent expressions.
        evaluationBook = {
          ...book,
          tlds: { ...book.tlds },
          ctrs: { ...book.ctrs },
          order: [...book.order],
          tmps: { ...book.tmps },
        };
        const name = `__bend_value_preview_${previewId++}`;
        const callee = /^([A-Za-z_][A-Za-z0-9_.]*)\s*(?:\(|$)/.exec(expression)?.[1];
        const returnType = definitions.find((item) => item.name === callee)?.returnType;
        if (!returnType) continue;
        const done = evaluationBook.order.length;
        parse_book(evaluationBook, path.dirname(source.staged).replaceAll("\\", "/"), `def ${name}() -> ${returnType}:\n  ${expression}\n`, "", {});
        book_valid(evaluationBook, done);
        definition = evaluationBook.tlds[name];
      } else {
        const containing = definitions.filter((item) => item.start <= marker.index).at(-1);
        const following = definitions.find((item) => item.start > marker.index);
        definition = book.tlds[containing?.name ?? following?.name ?? ""];
      }

      if (!definition || definition.$ !== "Def" || definition.n !== 0 || definition.v === null || definition.i !== undefined) continue;
      const type = term_show(term_lower(definition.T));
      // Normalizing an effect only constructs it; it does not execute it, so
      // showing that as a computed result would be misleading.
      if (/^IO(?:\b|\()/.test(type)) continue;
      const value = term_show(term_lower(term_snf(evaluationBook, definition.v)))
        .replace(/\s+/g, " ")
        .trim();
      if (!value) continue;
      result.push({
        uri: source.uri,
        offset: expression ? end : marker.index + marker[0].length,
        value: value.length > 200 ? `${value.slice(0, 197)}...` : value,
      });
    } catch { /* An expression that cannot be parsed, checked, or reduced has no preview. */ }
  }
  return result;
}

export async function checkBend(request: CheckRequest): Promise<CheckResult> {
  const runRoot = path.join(os.tmpdir(), "bend-flow-lsp", `${process.pid}-${request.id}`);
  try {
    const staged = stageProject(request, runRoot);
    const root = staged.sources.find((source) => key(source.original) === key(request.path));
    if (!root) throw new Error(`Unable to read ${request.path}`);
    const book = book_nil();
    let checking = false;
    let diagnostics: CheckDiagnostic[] = [];
    try {
      await book_load(book, staged.entry.replaceAll("\\", "/"), "", new Map());
      checking = true;
      book_valid(book);
      if (book.hols > 0) {
        for (const source of staged.sources) {
          const hole = /\?[A-Za-z_][A-Za-z0-9_]*/.exec(source.text);
          if (!hole) continue;
          diagnostics.push({
            uri: source.uri,
            start: hole.index,
            end: hole.index + hole[0].length,
            message: `Unresolved hole '${hole[0]}'.`,
            code: "holes",
          });
          break;
        }
      }
    } catch (caught) {
      const candidate = caught as Partial<Err>;
      if (candidate.$ === "Err" && candidate.bok && candidate.ctx && candidate.exp !== undefined) {
        const error = candidate as Err;
        const source = diagnosticSource(staged.sources, error.spn?.src, root);
        const range = boundedRange(source.text, error.spn?.beg ?? 0, error.spn?.end ?? 0);
        diagnostics = [{
          uri: source.uri,
          ...range,
          message: errorMessage(error),
          code: errorCode(error, checking),
        }];
      } else {
        diagnostics = [{
          uri: request.uri,
          start: 0,
          end: 1,
          message: caught instanceof Error ? caught.message : String(caught),
          code: checking ? "checking" : "imports",
        }];
      }
    }
    return {
      id: request.id,
      uri: request.uri,
      version: request.version,
      versions: Object.fromEntries(request.overlays.map((overlay) => [overlay.uri, overlay.version])),
      diagnostics,
      hovers: renderHovers(book),
      typedHovers: renderTypedHovers(book, staged.sources),
      valuePreviews: diagnostics.length === 0 && book.hols === 0 ? renderValuePreviews(book, root) : [],
    };
  } finally {
    fs.rmSync(runRoot, { recursive: true, force: true });
  }
}
