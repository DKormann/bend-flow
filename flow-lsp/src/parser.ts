import type {
  Block,
  Declaration,
  DoExpression,
  DoStatement,
  Expression,
  ExpressionStatement,
  Field,
  ImportStatement,
  MatchCase,
  MatchExpression,
  Program,
  Quantity,
  RawBendDefinition,
  Statement,
  UnionExpression,
  Variant,
} from "./ast.js";
import { ExpressionParser, FlowParseError, expressionToPattern } from "./expression-parser.js";

type Line = { raw: string; content: string; indent: number; start: number; end: number; number: number };

function linesOf(source: string): Line[] {
  const result: Line[] = [];
  let offset = 0;
  for (const [index, rawLine] of source.split("\n").entries()) {
    const raw = rawLine.endsWith("\r") ? rawLine.slice(0, -1) : rawLine;
    const whitespace = /^[ \t]*/.exec(raw)![0];
    if (whitespace.includes("\t")) {
      throw new FlowParseError("Flow indentation must use spaces", { start: offset, end: offset + whitespace.length });
    }
    result.push({
      raw,
      content: raw.slice(whitespace.length),
      indent: whitespace.length,
      start: offset,
      end: offset + raw.length,
      number: index,
    });
    offset += rawLine.length + 1;
  }
  return result;
}

function isTrivia(line: Line): boolean {
  const content = line.content.trim();
  return content === "" || content.startsWith("#");
}

function topLevelIndex(source: string, wanted: string): number {
  let round = 0;
  let curly = 0;
  let angle = 0;
  let string = false;
  for (let index = 0; index < source.length; index++) {
    const char = source[index];
    if (string) {
      if (char === "\\") index++;
      else if (char === '"') string = false;
      continue;
    }
    if (char === '"') { string = true; continue; }
    if (char === "(") round++;
    else if (char === ")") round--;
    else if (char === "{") curly++;
    else if (char === "}") curly--;
    else if (char === "<") angle++;
    else if (char === ">" && source[index - 1] !== "-") angle--;
    else if (char === wanted && round === 0 && curly === 0 && angle === 0) {
      if (wanted === "=" && (source[index + 1] === "=" || source[index - 1] === "=" || source[index - 1] === ">")) continue;
      return index;
    }
  }
  return -1;
}

function matching(source: string, start: number, open: string, close: string): number {
  let depth = 0;
  for (let index = start; index < source.length; index++) {
    if (source[index] === open) depth++;
    else if (source[index] === close && --depth === 0) return index;
  }
  return -1;
}

export class FlowParser {
  private readonly lines: Line[];
  private index = 0;

  constructor(private readonly source: string) {
    this.lines = linesOf(source);
  }

  parse(): Program {
    const statements = this.parseBlockStatements(0);
    return { kind: "Program", statements, span: { start: 0, end: this.source.length } };
  }

  private parseBlockStatements(indent: number): Statement[] {
    const statements: Statement[] = [];
    while (this.index < this.lines.length) {
      const line = this.lines[this.index];
      if (isTrivia(line)) { this.index++; continue; }
      if (line.indent < indent) break;
      if (line.indent > indent) {
        throw new FlowParseError(`Unexpected indentation on line ${line.number + 1}`, { start: line.start, end: line.start + line.indent });
      }
      statements.push(this.parseStatement(indent));
    }
    return statements;
  }

  private parseStatement(indent: number): Statement {
    const line = this.lines[this.index];
    if (/^import\b/.test(line.content)) return this.parseImport();
    if (/^(?:@unsafe\s+)?def\b|^law\b|^type\b/.test(line.content)) return this.parseRawBend(indent);
    if (/^do\b/.test(line.content)) {
      const expression = this.parseDo(indent);
      return { kind: "ExpressionStatement", expression, span: expression.span };
    }
    if (/^match\b/.test(line.content)) {
      const expression = this.parseMatch(indent);
      return { kind: "ExpressionStatement", expression, span: expression.span };
    }
    if (topLevelIndex(line.content, "=") >= 0) return this.parseDeclaration(indent);
    this.index++;
    const expression = this.parseExpression(line.content, line.start + line.indent);
    return { kind: "ExpressionStatement", expression, span: expression.span };
  }

  private parseImport(): ImportStatement {
    const line = this.lines[this.index++];
    const match = /^import\s+(\S+)(?:\s+as\s+([A-Za-z_]\w*))?\s*(?:#.*)?$/.exec(line.content);
    if (!match) throw new FlowParseError("Expected 'import Base' or 'import <path> as <Name>'", { start: line.start + line.indent, end: line.end });
    const pathStart = line.start + line.indent + line.content.indexOf(match[1]);
    const aliasStart = match[2] ? line.start + line.indent + line.content.lastIndexOf(match[2]) : 0;
    return {
      kind: "ImportStatement",
      path: match[1],
      alias: match[2] ? { kind: "Identifier", name: match[2], span: { start: aliasStart, end: aliasStart + match[2].length } } : undefined,
      pathSpan: { start: pathStart, end: pathStart + match[1].length },
      span: { start: line.start + line.indent, end: line.end },
    };
  }

  private parseRawBend(indent: number): RawBendDefinition {
    const first = this.index;
    this.index++;
    while (this.index < this.lines.length) {
      const line = this.lines[this.index];
      if (!isTrivia(line) && line.indent <= indent) break;
      this.index++;
    }
    const start = this.lines[first].start;
    const end = this.index < this.lines.length ? this.lines[this.index].start : this.source.length;
    return { kind: "RawBendDefinition", source: this.source.slice(start, end).replace(/\n+$/, ""), span: { start, end } };
  }

  private parseDeclaration(indent: number): Declaration {
    const line = this.lines[this.index++];
    const equals = topLevelIndex(line.content, "=");
    const header = line.content.slice(0, equals).trimEnd();
    const inlineBody = line.content.slice(equals + 1).trim();
    const parsed = this.parseDeclarationHeader(header, line.start + line.indent);
    let body: Expression | Block;
    if (inlineBody) {
      const bodyColumn = line.content.indexOf(inlineBody, equals + 1);
      body = this.parseExpression(inlineBody, line.start + line.indent + bodyColumn);
    } else {
      const childIndent = this.nextContentIndent();
      if (childIndent === null || childIndent <= indent) {
        throw new FlowParseError(`Expected an indented body for '${parsed.name.name}'`, { start: line.end, end: line.end });
      }
      if (this.lines[this.index].content.trimStart().startsWith("|")) {
        body = this.parseMultilineUnion(childIndent);
      } else {
        const statements = this.parseBlockStatements(childIndent);
        body = {
          kind: "Block",
          statements,
          span: { start: statements[0]?.span.start ?? line.end, end: statements.at(-1)?.span.end ?? line.end },
        };
      }
    }
    return {
      kind: "Declaration",
      ...parsed,
      body,
      span: { start: line.start + line.indent, end: body.span.end },
    };
  }

  private parseDeclarationHeader(header: string, base: number): Omit<Declaration, "kind" | "body" | "span"> {
    const marker = /^[+\-~]/.exec(header)?.[0];
    const quantity: Quantity = marker === "+" ? "many" : marker === "-" ? "none" : marker === "~" ? "comptime" : "lone";
    const quantitySpan = marker ? { start: base, end: base + 1 } : undefined;
    const nameOffset = marker ? 1 : 0;
    const nameMatch = /^[A-Za-z_][A-Za-z0-9_.]*/.exec(header.slice(nameOffset));
    if (!nameMatch) throw new FlowParseError("Expected a declaration name", { start: base + nameOffset, end: base + header.length });
    let cursor = nameOffset + nameMatch[0].length;
    const name = { kind: "Identifier" as const, name: nameMatch[0], span: { start: base + nameOffset, end: base + cursor } };
    let typeParameters: Field[] = [];
    let parameters: Field[] = [];

    while (/\s/.test(header[cursor] ?? "")) cursor++;
    if (header[cursor] === "<") {
      const close = matching(header, cursor, "<", ">");
      if (close < 0) throw new FlowParseError("Expected '>'", { start: base + cursor, end: base + header.length });
      typeParameters = this.parseFieldText(header.slice(cursor, close + 1), base + cursor, "<", ">");
      cursor = close + 1;
    }
    while (/\s/.test(header[cursor] ?? "")) cursor++;
    if (header[cursor] === "(") {
      const close = matching(header, cursor, "(", ")");
      if (close < 0) throw new FlowParseError("Expected ')'", { start: base + cursor, end: base + header.length });
      parameters = this.parseFieldText(header.slice(cursor, close + 1), base + cursor, "(", ")");
      cursor = close + 1;
    }
    while (/\s/.test(header[cursor] ?? "")) cursor++;
    if (header[cursor] !== ":") throw new FlowParseError("Expected ':' before the declaration type", { start: base + cursor, end: base + cursor + 1 });
    cursor++;
    while (/\s/.test(header[cursor] ?? "")) cursor++;
    const returnSource = header.slice(cursor);
    if (!returnSource) throw new FlowParseError("Expected a declaration type", { start: base + cursor, end: base + cursor });
    const returnType = this.parseExpression(returnSource, base + cursor);
    return { name, quantity, quantitySpan, typeParameters, parameters, returnType };
  }

  private parseFieldText(source: string, base: number, open: string, close: string): Field[] {
    const parser = new ExpressionParser(source, base);
    const fields = parser.parseFields(open, close);
    parser.expectEnd();
    return fields;
  }

  private parseMultilineUnion(indent: number): UnionExpression {
    const variants: Variant[] = [];
    while (this.index < this.lines.length) {
      const line = this.lines[this.index];
      if (isTrivia(line)) { this.index++; continue; }
      if (line.indent !== indent || !line.content.startsWith("|")) break;
      const expression = this.parseExpression(line.content, line.start + line.indent);
      if (expression.kind !== "UnionExpression") throw new FlowParseError("Expected a union variant", expression.span);
      variants.push(...expression.variants);
      this.index++;
    }
    if (!variants.length) throw new FlowParseError("Expected at least one union variant", { start: this.lines[this.index]?.start ?? this.source.length, end: this.lines[this.index]?.end ?? this.source.length });
    return { kind: "UnionExpression", variants, span: { start: variants[0].span.start, end: variants.at(-1)!.span.end } };
  }

  private parseDo(indent: number): DoExpression {
    const line = this.lines[this.index++];
    const match = /^do\s+(.+):\s*(?:#.*)?$/.exec(line.content);
    if (!match) throw new FlowParseError("Expected 'do <effect>:'", { start: line.start + line.indent, end: line.end });
    const effectColumn = line.content.indexOf(match[1]);
    const effect = this.parseExpression(match[1], line.start + line.indent + effectColumn);
    const bodyIndent = this.nextContentIndent();
    if (bodyIndent === null || bodyIndent <= indent) throw new FlowParseError("Expected an indented do body", { start: line.end, end: line.end });
    const statements: DoStatement[] = [];
    while (this.index < this.lines.length) {
      const bodyLine = this.lines[this.index];
      if (!isTrivia(bodyLine) && bodyLine.indent < bodyIndent) break;
      this.index++;
      if (!bodyLine.raw.trim()) continue;
      const start = bodyLine.start + Math.min(bodyIndent, bodyLine.raw.length);
      statements.push({ kind: "DoStatement", source: bodyLine.raw.slice(Math.min(bodyIndent, bodyLine.raw.length)), span: { start, end: bodyLine.end } });
    }
    if (!statements.length) throw new FlowParseError("A do block requires at least one statement", { start: line.end, end: line.end });
    return { kind: "DoExpression", effect, statements, span: { start: line.start + line.indent, end: statements.at(-1)!.span.end } };
  }

  private parseMatch(indent: number): MatchExpression {
    const line = this.lines[this.index++];
    const match = /^match\s+(.+):\s*(?:#.*)?$/.exec(line.content);
    if (!match) throw new FlowParseError("Expected 'match <expression>:'", { start: line.start + line.indent, end: line.end });
    const expressionColumn = line.content.indexOf(match[1]);
    const scrutinee = this.parseExpression(match[1], line.start + line.indent + expressionColumn);
    const caseIndent = this.nextContentIndent();
    if (caseIndent === null || caseIndent <= indent) throw new FlowParseError("Expected indented match cases", { start: line.end, end: line.end });
    const cases: MatchCase[] = [];
    while (this.index < this.lines.length) {
      const caseLine = this.lines[this.index];
      if (isTrivia(caseLine)) { this.index++; continue; }
      if (caseLine.indent !== caseIndent || !caseLine.content.startsWith("|")) break;
      const arrow = topLevelIndex(caseLine.content, "=");
      if (arrow < 0 || caseLine.content[arrow + 1] !== ">") {
        throw new FlowParseError("Expected '| <pattern> => <body>'", { start: caseLine.start + caseLine.indent, end: caseLine.end });
      }
      const patternSource = caseLine.content.slice(1, arrow).trim();
      const patternColumn = caseLine.content.indexOf(patternSource);
      const pattern = expressionToPattern(this.parseExpression(patternSource, caseLine.start + caseLine.indent + patternColumn));
      const bodySource = caseLine.content.slice(arrow + 2).trim();
      this.index++;
      let body: Expression | Block;
      if (bodySource) {
        const bodyColumn = caseLine.content.indexOf(bodySource, arrow + 2);
        body = this.parseExpression(bodySource, caseLine.start + caseLine.indent + bodyColumn);
      } else {
        const bodyIndent = this.nextContentIndent();
        if (bodyIndent === null || bodyIndent <= caseIndent) throw new FlowParseError("Expected an indented case body", { start: caseLine.end, end: caseLine.end });
        const statements = this.parseBlockStatements(bodyIndent);
        body = { kind: "Block", statements, span: { start: statements[0].span.start, end: statements.at(-1)!.span.end } };
      }
      cases.push({ kind: "MatchCase", pattern, body, span: { start: caseLine.start + caseLine.indent, end: body.span.end } });
    }
    if (!cases.length) throw new FlowParseError("A match requires at least one case", { start: line.end, end: line.end });
    return { kind: "MatchExpression", scrutinee, cases, span: { start: line.start + line.indent, end: cases.at(-1)!.span.end } };
  }

  private parseExpression(source: string, base: number): Expression {
    return new ExpressionParser(source, base).parse();
  }

  private nextContentIndent(): number | null {
    while (this.index < this.lines.length && isTrivia(this.lines[this.index])) this.index++;
    return this.index < this.lines.length ? this.lines[this.index].indent : null;
  }
}

export function parseFlow(source: string): Program {
  return new FlowParser(source).parse();
}
