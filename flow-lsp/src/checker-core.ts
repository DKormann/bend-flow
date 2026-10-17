import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { pathToFileURL } from "node:url";
import { book_load, book_nil, book_valid, err_show, term_lower, term_show, term_snf, type Book, type Err } from "bend-infrastructure";
import type { Block, Declaration, Expression, ImportStatement, MatchCase, Pattern, Program, Statement } from "./ast.js";
import type { FlowCheckDiagnostic, FlowCheckRequest, FlowCheckResult, FlowTypedHover, FlowValuePreview } from "./checker-protocol.js";
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
  const aliases = new Map<string, Expression>();
  const typeFunctions = new Map<string, { parameters: string[]; body: Expression }>();
  const constructors = new Map<string, { owner: string; parameters: string[]; fields: Expression[] }>();
  for (const statement of program.statements) {
    if (statement.kind !== "Declaration" || statement.body.kind === "Block") continue;
    aliases.set(statement.name.name, statement.body);
    if (statement.parameters.length > 0) {
      typeFunctions.set(statement.name.name, {
        parameters: statement.parameters.flatMap((field) => field.name ? [field.name.name] : []),
        body: statement.body,
      });
    }
    if (statement.body.kind !== "UnionExpression") continue;
    for (const variant of statement.body.variants) {
      const info = {
        owner: statement.name.name,
        parameters: statement.typeParameters.flatMap((field) => field.name ? [field.name.name] : []),
        fields: variant.fields.map((field) => field.type),
      };
      constructors.set(variant.name.name, info);
      const leaf = variant.name.name.split(".").at(-1)!;
      if (!constructors.has(leaf)) constructors.set(leaf, info);
    }
  }

  type TypeScope = Map<string, Expression>;
  const substitute = (type: Expression, values: Map<string, Expression>): Expression => {
    if (type.kind === "Identifier") return values.get(type.name) ?? type;
    if (type.kind === "CallExpression" || type.kind === "TypeApplicationExpression") return { ...type, callee: substitute(type.callee, values), arguments: type.arguments.map((item) => substitute(item, values)) };
    if (type.kind === "ArrowExpression") return { ...type, domain: substitute(type.domain, values), codomain: substitute(type.codomain, values) };
    if (type.kind === "EqualityExpression" || type.kind === "BinaryExpression") return { ...type, left: substitute(type.left, values), right: substitute(type.right, values) };
    if (type.kind === "TypedEqualityExpression") return { ...type, left: substitute(type.left, values), right: substitute(type.right, values), type: substitute(type.type, values) };
    if (type.kind === "AnnotationExpression") return { ...type, value: substitute(type.value, values), type: substitute(type.type, values) };
    return type;
  };
  const resolve = (original: Expression): Expression => {
    let type = original;
    const seen = new Set<string>();
    while (type.kind === "Identifier" && aliases.has(type.name) && !seen.has(type.name)) {
      seen.add(type.name);
      type = aliases.get(type.name)!;
    }
    if (type.kind === "CallExpression" && type.callee.kind === "Identifier") {
      const functionType = typeFunctions.get(type.callee.name);
      if (functionType) {
        const values = new Map<string, Expression>();
        functionType.parameters.forEach((name, index) => { if (type.arguments[index]) values.set(name, type.arguments[index]); });
        return substitute(functionType.body, values);
      }
    }
    return type;
  };
  const typeText = (type: Expression): string => {
    switch (type.kind) {
      case "Identifier": case "NumberExpression": case "QuantExpression": case "StringExpression": return source.slice(type.span.start, type.span.end);
      case "CallExpression": return `${typeText(type.callee)}(${type.arguments.map(typeText).join(", ")})`;
      case "TypeApplicationExpression": return `${typeText(type.callee)}<${type.arguments.map(typeText).join(", ")}>`;
      case "ArrowExpression": return `${typeText(type.domain)} -> ${typeText(type.codomain)}`;
      case "EqualityExpression": return `${typeText(type.left)} == ${typeText(type.right)}`;
      case "TypedEqualityExpression": return `{${typeText(type.left)} == ${typeText(type.right)} : ${typeText(type.type)}}`;
      case "BinaryExpression": return `${typeText(type.left)} ${type.operator} ${typeText(type.right)}`;
      case "AnnotationExpression": return `${typeText(type.value)} : ${typeText(type.type)}`;
      default: return source.slice(type.span.start, type.span.end);
    }
  };
  const expressionType = (expression: Expression, scope: TypeScope): Expression | undefined => {
    if (expression.kind === "Identifier") return scope.get(expression.name);
    if (expression.kind === "AnnotationExpression") return expression.type;
    if (expression.kind === "CallExpression" && expression.callee.kind === "Identifier") return scope.get(expression.callee.name);
    return undefined;
  };
  const bindPattern = (pattern: Pattern, type: Expression | undefined, scope: TypeScope): void => {
    if (pattern.kind === "NamePattern") {
      if (pattern.name !== "_" && type) {
        declarations.set(pattern.span.start, { name: pattern.name, type });
        scope.set(pattern.name, type);
      }
      return;
    }
    if (pattern.kind === "LiteralPattern") return;
    if (pattern.kind === "NatAddPattern") { bindPattern(pattern.rest, type, scope); return; }
    const actual = type && resolve(type);
    if (pattern.constructor === "Tuple" && actual?.kind === "BinaryExpression" && actual.operator === "&") {
      bindPattern(pattern.fields[0], actual.left, scope);
      bindPattern(pattern.fields[1], actual.right, scope);
      for (let index = 2; index < pattern.fields.length; index++) bindPattern(pattern.fields[index], undefined, scope);
      return;
    }
    const constructor = constructors.get(pattern.constructor) ?? constructors.get(pattern.constructor.split(".").at(-1)!);
    if (constructor) {
      const substitutions = new Map<string, Expression>();
      if (actual?.kind === "TypeApplicationExpression" && actual.callee.kind === "Identifier" && actual.callee.name === constructor.owner) {
        constructor.parameters.forEach((name, index) => { if (actual.arguments[index]) substitutions.set(name, actual.arguments[index]); });
      }
      pattern.fields.forEach((field, index) => {
        const declared = constructor.fields[index];
        const fieldType = declared ? substitute(declared, substitutions) : undefined;
        bindPattern(field, fieldType, scope);
      });
      return;
    }
    pattern.fields.forEach((field) => bindPattern(field, undefined, scope));
  };
  const visitCase = (item: MatchCase, scrutineeType: Expression | undefined, outer: TypeScope, depth: number): void => {
    const scope = new Map(outer);
    bindPattern(item.pattern, scrutineeType, scope);
    visitBody(item.body, scope, depth);
  };
  const visitExpression = (node: Expression, scope: TypeScope, depth: number): void => {
    switch (node.kind) {
      case "MatchExpression": {
        const type = expressionType(node.scrutinee, scope);
        node.cases.forEach((item) => visitCase(item, type, scope, depth));
        return;
      }
      case "ArrowExpression": visitExpression(node.domain, scope, depth); visitExpression(node.codomain, scope, depth); return;
      case "EqualityExpression": case "BinaryExpression": visitExpression(node.left, scope, depth); visitExpression(node.right, scope, depth); return;
      case "TypedEqualityExpression": visitExpression(node.left, scope, depth); visitExpression(node.right, scope, depth); visitExpression(node.type, scope, depth); return;
      case "AnnotationExpression": visitExpression(node.value, scope, depth); visitExpression(node.type, scope, depth); return;
      case "CallExpression": case "TypeApplicationExpression": case "ConstructorExpression":
        visitExpression(node.callee, scope, depth); node.arguments.forEach((item) => visitExpression(item, scope, depth)); return;
      case "TupleExpression": node.fields.forEach((field) => visitExpression(field.type, scope, depth)); return;
      case "UnionExpression": node.variants.forEach((variant) => variant.fields.forEach((field) => visitExpression(field.type, scope, depth))); return;
      case "ListExpression": node.values.forEach((item) => visitExpression(item, scope, depth)); return;
      case "ArrayExpression": visitExpression(node.value, scope, depth); visitExpression(node.type, scope, depth); visitExpression(node.size, scope, depth); return;
      case "IndexExpression": visitExpression(node.target, scope, depth); visitExpression(node.index, scope, depth); return;
      case "ArraySetExpression": visitExpression(node.target, scope, depth); visitExpression(node.index, scope, depth); visitExpression(node.value, scope, depth); return;
      case "RewriteExpression": visitExpression(node.proof, scope, depth); visitExpression(node.motive, scope, depth); visitExpression(node.value, scope, depth); return;
      case "DoExpression": visitExpression(node.effect, scope, depth); return;
      case "PrefixQuantityExpression": visitExpression(node.value, scope, depth); return;
      case "Identifier": case "NumberExpression": case "QuantExpression": case "StringExpression": case "ReflexivityExpression": return;
    }
  };
  const visitBody = (body: Expression | Block, scope: TypeScope, depth: number): void => {
    if (body.kind === "Block") visitStatements(body.statements, new Map(scope), depth + 1);
    else visitExpression(body, scope, depth);
  };
  const visitDeclaration = (node: Declaration, outer: TypeScope, depth: number): void => {
    outer.set(node.name.name, node.returnType);
    const scope = new Map(outer);
    if (depth > 0 && node.parameters.length === 0 && node.body.kind !== "UnionExpression" && node.body.kind !== "TupleExpression") {
      declarations.set(node.name.span.start, { name: node.name.name, type: node.returnType });
    }
    for (const field of [...node.typeParameters, ...node.parameters]) {
      if (!field.name) continue;
      declarations.set(field.name.span.start, { name: field.name.name, type: field.type });
      scope.set(field.name.name, field.type);
    }
    visitBody(node.body, scope, depth);
  };
  const visitStatements = (statements: Statement[], scope: TypeScope, depth: number): void => {
    for (const statement of statements) {
      if (statement.kind === "Declaration") visitDeclaration(statement, scope, depth);
      else if (statement.kind === "PatternDeclaration") {
        visitExpression(statement.value, scope, depth);
        bindPattern(statement.pattern, expressionType(statement.value, scope), scope);
      } else if (statement.kind === "ExpressionStatement") visitExpression(statement.expression, scope, depth);
    }
  };
  visitStatements(program.statements, new Map(), 0);
  return flowOccurrences(program).flatMap((occurrence) => {
    const declared = declarations.get(occurrence.definition.start);
    if (!declared) return [];
    const type = typeText(declared.type);
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

/** Evaluate pure, argument-free top-level Flow declarations selected by a #? comment. */
function renderValuePreviews(book: Book, source: FlowSource): FlowValuePreview[] {
  const result: FlowValuePreview[] = [];
  const declarations = source.lowered.program.statements
    .filter((statement): statement is Declaration => statement.kind === "Declaration")
    .sort((left, right) => left.span.start - right.span.start);
  const markers = /#\?/g;
  for (let marker = markers.exec(source.text); marker; marker = markers.exec(source.text)) {
    const lineEnd = source.text.indexOf("\n", marker.index);
    const end = lineEnd < 0 ? source.text.length : lineEnd;
    const after = source.text.slice(marker.index + marker[0].length, end);
    const named = /^\s+([A-Za-z_][A-Za-z0-9_.]*)\s*$/.exec(after);
    const containing = declarations.filter((declaration) => declaration.span.start <= marker.index).at(-1);
    const following = declarations.find((declaration) => declaration.span.start > marker.index);
    const name = named?.[1] ?? containing?.name.name ?? following?.name.name;
    if (!name) continue;

    const definition = book.tlds[name];
    if (!definition || definition.$ !== "Def" || definition.n !== 0 || definition.v === null || definition.i !== undefined) continue;
    try {
      const type = term_show(term_lower(definition.T));
      if (/^IO(?:\b|\()/.test(type)) continue;
      const value = term_show(term_lower(term_snf(book, definition.v))).replace(/\s+/g, " ").trim();
      if (!value) continue;
      result.push({
        uri: source.uri,
        offset: named ? end : marker.index + marker[0].length,
        value: value.length > 200 ? `${value.slice(0, 197)}...` : value,
      });
    } catch { /* A value that cannot be interpreted simply has no preview. */ }
  }
  return result;
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
  let valuePreviews: FlowValuePreview[] = [];
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
    if (diagnostics.length === 0 && book.hols === 0) valuePreviews = renderValuePreviews(book, root);
  } catch (error) {
    diagnostics = [{ uri: request.uri, start: 0, end: 1, message: error instanceof Error ? error.message : String(error), code: "lowering" }];
  } finally {
    fs.rmSync(directory, { recursive: true, force: true });
  }
  return { id: request.id, uri: request.uri, version: request.version, diagnostics, hovers, typedHovers, valuePreviews };
}
