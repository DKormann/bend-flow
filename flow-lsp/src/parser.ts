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
  PatternDeclaration,
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
  let square = 0;
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
    else if (char === "<" && source[index + 1] !== "-") angle++;
    else if (char === ">" && source[index - 1] !== "-") angle--;
    else if (char === "[") square++;
    else if (char === "]") square--;
    else if (char === wanted && round === 0 && curly === 0 && angle === 0 && square === 0) {
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

function delimiterDepth(source: string): number {
  const closes: string[] = [];
  let string = false;
  for (let index = 0; index < source.length; index++) {
    const char = source[index];
    if (string) {
      if (char === "\\") index++;
      else if (char === '"') string = false;
      continue;
    }
    if (char === '"') { string = true; continue; }
    if (char === "#") {
      while (index < source.length && source[index] !== "\n") index++;
      continue;
    }
    if (char === "(" || char === "{" || char === "[" || char === "<" && source[index + 1] !== "-") closes.push(char === "(" ? ")" : char === "{" ? "}" : char === "[" ? "]" : ">");
    else if (closes.at(-1) === char) closes.pop();
  }
  return closes.length;
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
    if (line.content.startsWith("%") && topLevelIndex(line.content, ";") < 0) return this.parseMultilineRewrite(indent);
    const equals = topLevelIndex(line.content, "=");
    if (equals >= 0 && line.content.slice(0, equals).trimStart().startsWith("(")) return this.parsePatternDeclaration();
    if (equals >= 0 || this.hasContinuedDeclarationHeader()) {
      return this.parseDeclaration(indent);
    }
    const expression = this.parseContinuedExpression(line.start + line.indent, line.end);
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

  private hasContinuedDeclarationHeader(): boolean {
    const first = this.lines[this.index];
    if (delimiterDepth(first.content) === 0 || !/^[+\-~]?[A-Za-z_][A-Za-z0-9_.]*\s*(?:<|\()/.test(first.content)) return false;
    const start = first.start + first.indent;
    for (let index = this.index; index < this.lines.length; index++) {
      const source = this.source.slice(start, this.lines[index].end);
      if (delimiterDepth(source) > 0) continue;
      return topLevelIndex(source, "=") >= 0 && topLevelIndex(source, ":") >= 0;
    }
    return false;
  }

  private parseMultilineRewrite(indent: number): ExpressionStatement {
    const line = this.lines[this.index++];
    const colon = topLevelIndex(line.content, ":");
    if (colon < 0) throw new FlowParseError("Expected ':' after the rewrite proof", { start: line.start + line.indent, end: line.end });
    const proofSource = line.content.slice(1, colon).trim();
    const motiveSource = line.content.slice(colon + 1).replace(/#.*$/, "").trim();
    if (!proofSource || !motiveSource) throw new FlowParseError("Expected '%proof : motive'", { start: line.start + line.indent, end: line.end });
    const proofColumn = line.content.indexOf(proofSource, 1);
    const motiveColumn = line.content.indexOf(motiveSource, colon + 1);
    const proof = this.parseExpression(proofSource, line.start + line.indent + proofColumn);
    const motive = this.parseExpression(motiveSource, line.start + line.indent + motiveColumn);
    while (this.index < this.lines.length && isTrivia(this.lines[this.index])) this.index++;
    const bodyLine = this.lines[this.index];
    if (!bodyLine || bodyLine.indent < indent) throw new FlowParseError("Expected a rewrite body", { start: line.end, end: line.end });
    const body = this.parseStatement(bodyLine.indent);
    if (body.kind !== "ExpressionStatement") throw new FlowParseError("A rewrite body must be an expression", body.span);
    const expression: Expression = {
      kind: "RewriteExpression",
      proof,
      motive,
      value: body.expression,
      span: { start: line.start + line.indent, end: body.span.end },
    };
    return { kind: "ExpressionStatement", expression, span: expression.span };
  }

  private parsePatternDeclaration(): PatternDeclaration {
    const line = this.lines[this.index++];
    const equals = topLevelIndex(line.content, "=");
    const patternSource = line.content.slice(0, equals).trim();
    const patternColumn = line.content.indexOf(patternSource);
    const pattern = expressionToPattern(this.parseExpression(patternSource, line.start + line.indent + patternColumn));
    const valueSource = line.content.slice(equals + 1).trim();
    if (!valueSource) throw new FlowParseError("Expected a value after '='", { start: line.end, end: line.end });
    const valueColumn = line.content.indexOf(valueSource, equals + 1);
    const value = this.parseContinuedExpression(line.start + line.indent + valueColumn, line.end);
    return { kind: "PatternDeclaration", pattern, value, span: { start: pattern.span.start, end: value.span.end } };
  }

  private parseDeclaration(indent: number): Declaration {
    const first = this.lines[this.index];
    const start = first.start + first.indent;
    let end = first.end;
    let equals = -1;
    while (this.index < this.lines.length) {
      const line = this.lines[this.index++];
      end = line.end;
      const source = this.source.slice(start, end);
      equals = topLevelIndex(source, "=");
      if (equals >= 0) break;
      if (delimiterDepth(source) === 0) break;
    }
    const declarationSource = this.source.slice(start, end);
    if (equals < 0) throw new FlowParseError("Expected '=' after the declaration header", { start, end });
    const header = declarationSource.slice(0, equals).trimEnd();
    const inlineBody = declarationSource.slice(equals + 1).trim();
    const parsed = this.parseDeclarationHeader(header, start);
    let body: Expression | Block;
    if (inlineBody) {
      const bodyOffset = declarationSource.indexOf(inlineBody, equals + 1);
      body = this.parseContinuedExpression(start + bodyOffset, end);
    } else {
      const childIndent = this.nextContentIndent();
      if (childIndent === null || childIndent <= indent) {
        throw new FlowParseError(`Expected an indented body for '${parsed.name.name}'`, { start: end, end });
      }
      if (this.lines[this.index].content.trimStart().startsWith("|")) {
        body = this.parseMultilineUnion(childIndent);
      } else {
        const statements = this.parseBlockStatements(childIndent);
        body = {
          kind: "Block",
          statements,
          span: { start: statements[0]?.span.start ?? end, end: statements.at(-1)?.span.end ?? end },
        };
      }
    }
    return {
      kind: "Declaration",
      ...parsed,
      body,
      span: { start, end: body.span.end },
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
      const start = line.start + line.indent;
      this.index++;
      while (this.index < this.lines.length) {
        const next = this.lines[this.index];
        if (!isTrivia(next) && next.indent <= indent) break;
        this.index++;
      }
      const end = this.index < this.lines.length ? this.lines[this.index].start : this.source.length;
      const expression = this.parseExpression(this.source.slice(start, end).replace(/\s+$/, ""), start);
      if (expression.kind !== "UnionExpression") throw new FlowParseError("Expected a union variant", expression.span);
      variants.push(...expression.variants);
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

  private parseContinuedExpression(start: number, initialEnd: number): Expression {
    let end = initialEnd;
    // The caller has not consumed its first line yet for ordinary expression
    // statements, but has for inline declaration bodies.
    const first = this.lines.findIndex((line) => line.start <= start && start <= line.end);
    if (this.index <= first) this.index = first + 1;
    while (delimiterDepth(this.source.slice(start, end)) > 0 && this.index < this.lines.length) {
      end = this.lines[this.index].end;
      this.index++;
    }
    return this.parseExpression(this.source.slice(start, end), start);
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
