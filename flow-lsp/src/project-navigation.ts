import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import type { Declaration, ImportStatement, Program, Span } from "./ast.js";
import { flowDefinitionAt } from "./navigation.js";
import { parseFlow } from "./parser.js";

export type FlowOverlay = { path: string; uri: string; text: string };
export type FlowLocation = { uri: string; range: Span };

function tokenAt(source: string, offset: number): string {
  let start = offset;
  let end = offset;
  while (start > 0 && /[A-Za-z0-9_.]/.test(source[start - 1])) start--;
  while (end < source.length && /[A-Za-z0-9_.]/.test(source[end])) end++;
  return source.slice(start, end);
}

function resolveHub(raw: string): string | null {
  const library = path.resolve(process.env.BEND_LIB ?? path.join(os.homedir(), ".bend", "lib"));
  if (/^0x[0-9a-f]+\//.test(raw)) return path.join(library, raw);
  const named = /^([^/]+@[^/]+)\/(.+)$/.exec(raw);
  if (!named) return null;
  try {
    const hash = fs.readFileSync(path.join(library, "names", named[1]), "utf8").trim();
    return /^0x[0-9a-f]+$/.test(hash) ? path.join(library, hash, named[2]) : null;
  } catch { return null; }
}

function importedPath(entry: string, imported: ImportStatement): string | null {
  if (imported.path === "Base") return fileURLToPath(new URL("./base.bend", import.meta.url));
  return resolveHub(imported.path) ?? path.resolve(path.dirname(entry), imported.path);
}

function flowDeclaration(program: Program, name: string): Span | null {
  for (const statement of program.statements) {
    if (statement.kind !== "Declaration") continue;
    if (statement.name.name === name) return statement.name.span;
    if (statement.body.kind === "UnionExpression") {
      const variant = statement.body.variants.find((item) => item.name.name === name);
      if (variant) return variant.name.span;
    }
    if (statement.body.kind === "TupleExpression" && name === `${statement.name.name}.mk`) return statement.name.span;
  }
  return null;
}

function bendDeclaration(source: string, name: string): Span | null {
  const escaped = name.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const top = new RegExp(`^\\s*(?:def|law|type)\\s+(${escaped})(?=[?(<\\s:])`, "m").exec(source);
  if (top) {
    const start = top.index + top[0].lastIndexOf(top[1]);
    return { start, end: start + top[1].length };
  }
  for (const match of source.matchAll(/^\s*([A-Za-z_][A-Za-z0-9_.]*)\s*\{/gm)) {
    if (match[1] === name || match[1].split(".").at(-1) === name) {
      const start = match.index + match[0].indexOf(match[1]);
      return { start, end: start + match[1].length };
    }
  }
  return null;
}

export function flowProjectDefinitionAt(
  file: string,
  uri: string,
  source: string,
  offset: number,
  overlays: FlowOverlay[] = [],
): FlowLocation | null {
  const own = flowDefinitionAt(source, offset);
  if (own) return { uri, range: own };
  const program = parseFlow(source);
  const imports = program.statements.filter((item): item is ImportStatement => item.kind === "ImportStatement");
  const token = tokenAt(source, offset);
  const selected = imports.find((item) =>
    item.pathSpan.start <= offset && offset <= item.pathSpan.end
    || item.alias && item.alias.span.start <= offset && offset <= item.alias.span.end
    || item.alias && token.startsWith(item.alias.name + "."))
    ?? imports.find((item) => item.path === "Base");
  if (!selected) return null;
  const targetPath = importedPath(file, selected);
  if (!targetPath) return null;
  const overlay = overlays.find((item) => path.resolve(item.path) === path.resolve(targetPath));
  if (!overlay && !fs.existsSync(targetPath)) return null;
  const targetSource = overlay?.text ?? fs.readFileSync(targetPath, "utf8");
  const targetUri = overlay?.uri ?? pathToFileURL(targetPath).href;
  if (selected.pathSpan.start <= offset && offset <= selected.pathSpan.end
    || selected.alias && selected.alias.span.start <= offset && offset <= selected.alias.span.end) {
    return { uri: targetUri, range: { start: 0, end: 0 } };
  }
  const symbol = selected.alias ? token.slice(selected.alias.name.length + 1) : token;
  try {
    const range = targetPath.endsWith(".flow") ? flowDeclaration(parseFlow(targetSource), symbol) : bendDeclaration(targetSource, symbol);
    return range ? { uri: targetUri, range } : null;
  } catch { return null; }
}
