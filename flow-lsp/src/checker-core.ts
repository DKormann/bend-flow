import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { pathToFileURL } from "node:url";
import { book_load, book_nil, book_valid, err_show, term_lower, term_show, type Book, type Err } from "bend-infrastructure";
import type { Block, Declaration, Expression, ImportStatement, Program, Statement } from "./ast.js";
import type { FlowCheckDiagnostic, FlowCheckRequest, FlowCheckResult, FlowTypedHover } from "./checker-protocol.js";
import { lowerFlow, originalFlowSpan, type LoweredFlow } from "./lower.js";
import { flowOccurrences } from "./navigation.js";

type FlowSource = { original: string; staged: string; uri: string; text: string; lowered: LoweredFlow };
type BendSource = { original: string; staged: string; uri: string; text: string };

function message(error: Err): string {
  return err_show(error).replace(/\nLocation:[\s\S]*$/, "").trim();
}

function key(file: string): string {
  const value = path.resolve(file).replaceAll("\\", "/");
  return process.platform === "win32" ? value.toLowerCase() : value;
}

function mirrorPath(file: string, root: string, extension?: string): string {
  const absolute = path.resolve(file);
  const parsed = path.parse(absolute);
  const volume = parsed.root.replace(/[^A-Za-z0-9]/g, "") || "root";
  const relative = absolute.slice(parsed.root.length);
  const mirrored = path.join(root, volume, relative);
  return extension ? mirrored.replace(/\.[^.\/]+$/, extension) : mirrored;
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

function compilerOffset(text: string, compilerText: string, offset: number): number {
  if (text === compilerText) return offset;
  const before = compilerText.slice(0, offset);
  const line = before.split("\n").length - 1;
  const column = offset - before.lastIndexOf("\n") - 1;
  const lines = text.split("\n");
  let result = 0;
  for (let index = 0; index < line; index++) result += (lines[index]?.length ?? 0) + 1;
  return result + column;
}

function renderFlowTypedHovers(source: string, program: Program): FlowTypedHover[] {
  const declarations = new Map<number, { name: string; type: Expression }>();
  const visitStatements = (statements: Statement[], depth: number): void => {
    for (const statement of statements) if (statement.kind === "Declaration") visitDeclaration(statement, depth);
  };
  const visitDeclaration = (node: Declaration, depth: number): void => {
    if (depth > 0 && node.parameters.length === 0 && node.body.kind !== "UnionExpression" && node.body.kind !== "TupleExpression") {
      declarations.set(node.name.span.start, { name: node.name.name, type: node.returnType });
    }
    for (const field of [...node.typeParameters, ...node.parameters]) {
      if (field.name) declarations.set(field.name.span.start, { name: field.name.name, type: field.type });
    }
    if (node.body.kind === "Block") visitStatements(node.body.statements, depth + 1);
    else if (node.body.kind === "MatchExpression") {
      for (const item of node.body.cases) if (item.body.kind === "Block") visitStatements(item.body.statements, depth + 1);
    }
  };
  visitStatements(program.statements, 0);
  return flowOccurrences(program).flatMap((occurrence) => {
    const declared = declarations.get(occurrence.definition.start);
    if (!declared) return [];
    const type = source.slice(declared.type.span.start, declared.type.span.end);
    return [{ start: occurrence.start, end: occurrence.end, value: `\`\`\`bend\n${declared.name} : ${type}\n\`\`\`` }];
  });
}

function renderHovers(book: Book): Record<string, string> {
  const hovers: Record<string, string> = Object.create(null) as Record<string, string>;
  const add = (name: string, kind: string, term: unknown): void => {
    try {
      const signature = term_show(term_lower(term));
      const value = `**${kind} ${name}**\n\n\`\`\`bend\n${name} : ${signature}\n\`\`\``;
      hovers[name] = value;
      const leaf = name.split(".").at(-1)!;
      if (!(leaf in hovers)) hovers[leaf] = value;
    } catch {}
  };
  for (const [name, tld] of Object.entries(book.tlds)) add(name, tld.$ === "ADT" ? "type" : "def", tld.T);
  for (const [name, constructor] of Object.entries(book.ctrs)) add(name, "constructor", constructor.T);
  return hovers;
}

function localFlowImports(program: Program): ImportStatement[] {
  return program.statements.filter((item): item is ImportStatement => item.kind === "ImportStatement" && item.path !== "Base");
}

function bendImports(text: string): string[] {
  const result: string[] = [];
  for (const line of text.split("\n")) {
    const value = line.trim();
    if (!value || value.startsWith("#")) continue;
    const match = /^import\s+(\S+)(?:\s+as\s+[A-Za-z_]\w*)?/.exec(value);
    if (!match) break;
    if (match[1] !== "Base") result.push(match[1]);
  }
  return result;
}

function isHub(imported: string): boolean {
  return /^0x[0-9a-f]+\//.test(imported) || /^[^/]+@[^/]+\//.test(imported);
}

function stageProject(request: FlowCheckRequest, root: string): { entry: string; flows: FlowSource[]; bends: BendSource[] } {
  const overlays = new Map(request.overlays.map((item) => [key(item.path), item]));
  overlays.set(key(request.path), { path: request.path, uri: request.uri, text: request.text, version: request.version });
  const flows: FlowSource[] = [];
  const bends: BendSource[] = [];
  const seen = new Set<string>();

  const stageBend = (file: string): void => {
    const id = `bend:${key(file)}`;
    if (seen.has(id) || !fs.existsSync(file)) return;
    seen.add(id);
    const text = fs.readFileSync(file, "utf8");
    const staged = mirrorPath(file, root);
    fs.mkdirSync(path.dirname(staged), { recursive: true });
    fs.writeFileSync(staged, text);
    bends.push({ original: path.resolve(file), staged, uri: pathToFileURL(file).href, text });
    for (const imported of bendImports(text)) if (!isHub(imported)) stageBend(path.resolve(path.dirname(file), imported));
  };

  const stageFlow = (file: string): void => {
    const id = `flow:${key(file)}`;
    if (seen.has(id)) return;
    const overlay = overlays.get(key(file));
    if (!overlay && !fs.existsSync(file)) return;
    seen.add(id);
    const text = overlay?.text ?? fs.readFileSync(file, "utf8");
    const lowered = lowerFlow(text);
    const staged = mirrorPath(file, root, ".bend");
    fs.mkdirSync(path.dirname(staged), { recursive: true });
    fs.writeFileSync(staged, lowered.bend);
    flows.push({ original: path.resolve(file), staged, uri: overlay?.uri ?? pathToFileURL(file).href, text, lowered });
    for (const imported of localFlowImports(lowered.program)) {
      if (isHub(imported.path)) continue;
      const child = path.resolve(path.dirname(file), imported.path);
      if (imported.path.endsWith(".flow")) stageFlow(child);
      else if (imported.path.endsWith(".bend")) stageBend(child);
    }
  };

  stageFlow(request.path);
  return { entry: mirrorPath(request.path, root, ".bend"), flows, bends };
}

export async function checkFlow(request: FlowCheckRequest): Promise<FlowCheckResult> {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), "flow-check-"));
  let diagnostics: FlowCheckDiagnostic[] = [];
  let hovers: Record<string, string> = {};
  let typedHovers: FlowTypedHover[] = [];
  try {
    const staged = stageProject(request, directory);
    const root = staged.flows.find((item) => key(item.original) === key(request.path));
    if (!root) throw new Error(`Unable to read ${request.path}`);
    typedHovers = renderFlowTypedHovers(root.text, root.lowered.program);
    const book = book_nil();
    let checking = false;
    try {
      await book_load(book, staged.entry.replaceAll("\\", "/"), "", new Map());
      checking = true;
      book_valid(book);
      if (book.hols > 0) {
        for (const source of staged.flows) {
          const hole = /\?[A-Za-z_][A-Za-z0-9_]*/.exec(source.text);
          if (hole) {
            diagnostics = [{ uri: source.uri, start: hole.index, end: hole.index + hole[0].length, message: `Unresolved hole '${hole[0]}'.`, code: "holes" }];
            break;
          }
        }
      }
    } catch (caught) {
      const candidate = caught as Partial<Err>;
      if (candidate.$ === "Err" && candidate.bok && candidate.ctx && candidate.exp !== undefined) {
        const error = candidate as Err;
        const flow = staged.flows.find((item) => compilerSource(item.lowered.bend) === error.spn?.src || item.lowered.bend === error.spn?.src);
        if (flow) {
          const generatedOffset = compilerOffset(flow.lowered.bend, error.spn?.src ?? flow.lowered.bend, error.spn?.beg ?? 0);
          const original = originalFlowSpan(flow.lowered, generatedOffset) ?? { start: 0, end: 1 };
          diagnostics = [{ uri: flow.uri, start: original.start, end: Math.max(original.end, original.start + 1), message: message(error), code: checking ? "checking" : "bend-parsing" }];
        } else {
          const bend = staged.bends.find((item) => compilerSource(item.text) === error.spn?.src || item.text === error.spn?.src);
          diagnostics = [{ uri: bend?.uri ?? request.uri, start: error.spn?.beg ?? 0, end: Math.max(error.spn?.end ?? 0, (error.spn?.beg ?? 0) + 1), message: message(error), code: checking ? "checking" : "bend-parsing" }];
        }
      } else {
        diagnostics = [{ uri: request.uri, start: 0, end: 1, message: caught instanceof Error ? caught.message : String(caught), code: checking ? "checking" : "lowering" }];
      }
    }
    hovers = renderHovers(book);
  } catch (error) {
    diagnostics = [{ uri: request.uri, start: 0, end: 1, message: error instanceof Error ? error.message : String(error), code: "lowering" }];
  } finally {
    fs.rmSync(directory, { recursive: true, force: true });
  }
  return { id: request.id, uri: request.uri, version: request.version, diagnostics, hovers, typedHovers };
}
