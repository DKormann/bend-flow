import type { Block, Declaration, Expression, Field, MatchCase, Pattern, Program, Quantity, Span, Statement, UnionExpression } from "./ast.js";
import { parseFlow } from "./parser.js";

export type FlowSourceMapping = {
  generatedStart: number;
  generatedEnd: number;
  flowStart: number;
  flowEnd: number;
};

export type LoweredFlow = { bend: string; mappings: FlowSourceMapping[]; program: Program };
type SymbolKind = "type" | "function" | "value" | "constructor" | "binding";
type Symbol = { kind: SymbolKind; target: string; span: Span; type?: Expression; owner?: string; quantity?: Quantity };
type Scope = Map<string, Symbol>;
type Snippet = { text: string; mappings: FlowSourceMapping[] };

class Writer {
  text = "";
  mappings: FlowSourceMapping[] = [];
  write(text: string, span?: Span): void {
    const start = this.text.length;
    this.text += text;
    if (span && text.length) this.mappings.push({ generatedStart: start, generatedEnd: this.text.length, flowStart: span.start, flowEnd: span.end });
  }
  line(text = "", span?: Span): void { this.write(text, span); this.write("\n"); }
}

function append(output: Writer, snippet: Snippet): void {
  const offset = output.text.length;
  output.text += snippet.text;
  output.mappings.push(...snippet.mappings.map((mapping) => ({
    ...mapping,
    generatedStart: mapping.generatedStart + offset,
    generatedEnd: mapping.generatedEnd + offset,
  })));
}

function indent(text: string, spaces = 2): string {
  const prefix = " ".repeat(spaces);
  return text.split("\n").map((line) => line ? prefix + line : line).join("\n");
}

export class FlowLowerer {
  private readonly imports: Snippet[] = [];
  private readonly hoisted: Snippet[] = [];
  private readonly regular: Snippet[] = [];
  private readonly global: Scope = new Map();
  private hasBaseImport = false;

  constructor(private readonly program: Program) {}

  lower(): LoweredFlow {
    for (const statement of this.program.statements) this.lowerTopStatement(statement);
    const output = new Writer();
    if (this.hasBaseImport) output.line("import Base");
    for (const imported of this.imports) append(output, imported);
    if (this.hasBaseImport || this.imports.length) output.line();
    for (const snippet of [...this.hoisted, ...this.regular]) {
      append(output, snippet);
      if (!output.text.endsWith("\n\n")) output.line();
    }
    return { bend: output.text, mappings: output.mappings, program: this.program };
  }

  private lowerTopStatement(statement: Statement): void {
    if (statement.kind === "ImportStatement") {
      if (statement.path === "Base") { this.hasBaseImport = true; return; }
      const writer = new Writer();
      const importedPath = statement.path.endsWith(".flow") ? statement.path.slice(0, -5) + ".bend" : statement.path;
      writer.write("import "); writer.write(importedPath, statement.pathSpan);
      if (statement.alias) { writer.write(" as "); writer.write(statement.alias.name, statement.alias.span); }
      writer.line();
      this.imports.push({ text: writer.text, mappings: writer.mappings });
      return;
    }
    if (statement.kind === "RawBendDefinition") {
      const found = /^\s*(?:@unsafe\s+)?(?:def|law|type)\s+([A-Za-z_][A-Za-z0-9_.]*)/m.exec(statement.source);
      if (found) {
        const kind: SymbolKind = /^\s*type\b/.test(statement.source) ? "type" : "function";
        this.global.set(found[1], { kind, target: found[1], span: statement.span });
      }
      const writer = new Writer();
      writer.line(statement.source, statement.span);
      this.regular.push({ text: writer.text, mappings: writer.mappings });
      return;
    }
    if (statement.kind === "Declaration") {
      this.lowerDeclaration(statement, statement.name.name, this.global, false);
      return;
    }
    const type = this.expressionType(statement.expression, this.global) ?? "Type";
    const writer = new Writer();
    writer.line(`def main() -> ${type}:`, statement.span);
    writer.line("  " + this.renderExpression(statement.expression, this.global), statement.expression.span);
    this.regular.push({ text: writer.text, mappings: writer.mappings });
  }

  private lowerDeclaration(node: Declaration, target: string, outer: Scope, nested: boolean): void {
    const typeDeclaration = node.body.kind === "UnionExpression" || node.body.kind === "TupleExpression";
    const kind: SymbolKind = typeDeclaration ? "type" : node.parameters.length ? "function" : "value";
    outer.set(node.name.name, { kind, target, span: node.name.span, type: node.returnType });
    const scope = new Map(outer);
    this.bindFields(node.typeParameters, scope);
    this.bindFields(node.parameters, scope);
    const snippet = typeDeclaration
      ? this.lowerTypeDeclaration(node, target, scope, outer)
      : this.lowerValueDeclaration(node, target, scope);
    (nested ? this.hoisted : this.regular).push(snippet);
  }

  private lowerTypeDeclaration(node: Declaration, target: string, scope: Scope, outer: Scope): Snippet {
    const writer = new Writer();
    const parameters = this.renderTypeParameters(node.typeParameters, scope);
    writer.write("type "); writer.write(target, node.name.span); writer.write(parameters);
    writer.write(" is "); writer.write(this.renderExpression(node.returnType, scope), node.returnType.span); writer.line(":");
    if (node.body.kind === "UnionExpression") {
      for (const variant of node.body.variants) {
        const constructor = target.includes(".") ? `${target}.${variant.name.name}` : variant.name.name;
        outer.set(variant.name.name, { kind: "constructor", target: constructor, owner: target, span: variant.name.span });
        scope.set(variant.name.name, { kind: "constructor", target: constructor, owner: target, span: variant.name.span });
        writer.write("  "); writer.write(constructor, variant.name.span); writer.write("{");
        const fieldScope = new Map(scope);
        variant.fields.forEach((field, index) => {
          if (index) writer.write(", ");
          const name = field.name?.name ?? `field${index}`;
          writer.write(this.quantityMarker(field.quantity), field.quantitySpan); writer.write(name, field.name?.span ?? field.span); writer.write(": ");
          writer.write(this.renderType(field.type, fieldScope), field.type.span);
          if (field.name) fieldScope.set(field.name.name, { kind: "binding", target: field.name.name, span: field.name.span, type: field.type });
        });
        writer.line("}");
      }
    } else if (node.body.kind === "TupleExpression") {
      const constructor = `${target}.mk`;
      outer.set(`${node.name.name}.mk`, { kind: "constructor", target: constructor, owner: target, span: node.name.span });
      writer.write("  "); writer.write(constructor, node.name.span); writer.write("{");
      const fieldScope = new Map(scope);
      node.body.fields.forEach((field, index) => {
        if (index) writer.write(", ");
        const name = field.name?.name ?? (field.type.kind === "EqualityExpression" ? "proof" : `field${index}`);
        writer.write(this.quantityMarker(field.quantity), field.quantitySpan); writer.write(name, field.name?.span ?? field.span); writer.write(": ");
        writer.write(this.renderType(field.type, fieldScope), field.type.span);
        if (field.name) fieldScope.set(field.name.name, { kind: "binding", target: field.name.name, span: field.name.span, type: field.type });
      });
      writer.line("}");
    }
    return { text: writer.text, mappings: writer.mappings };
  }

  private lowerValueDeclaration(node: Declaration, target: string, scope: Scope): Snippet {
    const writer = new Writer();
    writer.write("def "); writer.write(target, node.name.span); writer.write("(");
    node.parameters.forEach((field, index) => {
      if (index) writer.write(", ");
      writer.write(this.quantityMarker(field.quantity), field.quantitySpan); writer.write(field.name?.name ?? `arg${index}`, field.name?.span ?? field.span); writer.write(": ");
      writer.write(this.renderType(field.type, scope), field.type.span);
    });
    writer.write(") -> "); writer.write(this.renderType(node.returnType, scope), node.returnType.span); writer.line(":");
    if (node.body.kind === "Block") {
      const body = this.renderBlock(node.body, scope, target);
      writer.write(indent(body.text), node.body.span);
      if (!writer.text.endsWith("\n")) writer.line();
    } else {
      writer.line("  " + this.renderExpression(node.body, scope), node.body.span);
    }
    return { text: writer.text, mappings: writer.mappings };
  }

  private renderBlock(block: Block, parent: Scope, owner: string): Snippet {
    const writer = new Writer();
    const scope = new Map(parent);
    for (const statement of block.statements) {
      if (statement.kind === "ImportStatement") {
        throw new Error("Flow imports must be at the top level");
      } else if (statement.kind === "RawBendDefinition") {
        writer.line(statement.source, statement.span);
      } else if (statement.kind === "ExpressionStatement") {
        writer.line(this.renderExpression(statement.expression, scope), statement.span);
      } else {
        const needsLift = statement.parameters.length > 0 || statement.body.kind === "UnionExpression" || statement.body.kind === "TupleExpression";
        if (needsLift) {
          const target = `${owner}.${statement.name.name}`;
          this.lowerDeclaration(statement, target, scope, true);
        } else {
          scope.set(statement.name.name, { kind: "binding", target: statement.name.name, span: statement.name.span, type: statement.returnType, quantity: statement.quantity });
          writer.write(this.quantityMarker(statement.quantity), statement.quantitySpan); writer.write(statement.name.name, statement.name.span); writer.write(": ");
          writer.write(this.renderType(statement.returnType, scope), statement.returnType.span); writer.write(" = ");
          if (statement.body.kind === "Block") {
            const helper = `${owner}.${statement.name.name}`;
            const free = this.freeBlockNames(statement.body);
            const captures = [...scope.entries()].filter(([name, symbol]) => name !== statement.name.name && free.has(name) && symbol.kind === "binding" && symbol.type);
            const lifted = new Writer();
            lifted.write("def "); lifted.write(helper, statement.name.span); lifted.write("(");
            captures.forEach(([name, symbol], index) => {
              if (index) lifted.write(", ");
              lifted.write(this.quantityMarker(symbol.quantity ?? "lone")); lifted.write(name, symbol.span); lifted.write(": ");
              lifted.write(this.renderType(symbol.type as Expression, scope), symbol.type?.span);
            });
            lifted.write(") -> "); lifted.write(this.renderType(statement.returnType, scope), statement.returnType.span); lifted.line(":");
            const nested = this.renderBlock(statement.body, scope, helper);
            lifted.write(indent(nested.text), statement.body.span);
            if (!lifted.text.endsWith("\n")) lifted.line();
            this.hoisted.push({ text: lifted.text, mappings: lifted.mappings });
            writer.line(`${helper}(${captures.map(([name]) => name).join(", ")})`, statement.body.span);
          } else {
            writer.line(this.renderExpression(statement.body, scope), statement.body.span);
          }
        }
      }
    }
    return { text: writer.text, mappings: writer.mappings };
  }

  private renderExpression(node: Expression, scope: Scope): string {
    switch (node.kind) {
      case "Identifier": {
        const symbol = scope.get(node.name);
        if (!symbol) return node.name;
        if (symbol.kind === "value") return `${symbol.target}()`;
        if (symbol.kind === "constructor") return `${symbol.target}{}`;
        return symbol.target;
      }
      case "NumberExpression": return node.value;
      case "StringExpression": return node.raw;
      case "ArrowExpression": return `${this.renderExpression(node.domain, scope)} -> ${this.renderExpression(node.codomain, scope)}`;
      case "EqualityExpression": {
        const type = this.inferEqualityType(node.left, node.right, scope);
        return `{${this.renderExpression(node.left, scope)} == ${this.renderExpression(node.right, scope)} : ${type}}`;
      }
      case "TypedEqualityExpression": return `{${this.renderExpression(node.left, scope)} == ${this.renderExpression(node.right, scope)} : ${this.renderType(node.type, scope)}}`;
      case "ReflexivityExpression": return "{==}";
      case "AnnotationExpression": return `{${this.renderExpression(node.value, scope)} : ${this.renderType(node.type, scope)}}`;
      case "CallExpression": return `${this.renderExpression(node.callee, scope)}(${node.arguments.map((item) => this.renderExpression(item, scope)).join(", ")})`;
      case "TypeApplicationExpression": return `${this.renderExpression(node.callee, scope)}<${node.arguments.map((item) => this.renderType(item, scope)).join(", ")}>`;
      case "ConstructorExpression": {
        let callee = node.callee;
        let typeArguments: Expression[] = [];
        if (callee.kind === "TypeApplicationExpression") {
          typeArguments = callee.arguments;
          callee = callee.callee;
        }
        const renderedCallee = this.renderExpression(callee, scope).replace(/\{\}$/, "");
        const value = `${renderedCallee}{${node.arguments.map((item) => this.renderExpression(item, scope)).join(", ")}}`;
        if (typeArguments.length && callee.kind === "Identifier") {
          const symbol = scope.get(callee.name);
          if (symbol?.owner) return `{${value} : ${symbol.owner}<${typeArguments.map((item) => this.renderType(item, scope)).join(", ")}>}`;
        }
        return value;
      }
      case "TupleExpression": return `(${node.fields.map((field) => this.renderType(field.type, scope)).join(", ")})`;
      case "UnionExpression": throw new Error("An inline union must be lifted before expression rendering");
      case "MatchExpression": {
        const lines = [`match ${this.renderExpression(node.scrutinee, scope)}:`];
        for (const item of node.cases) lines.push(...this.renderCase(item, scope).split("\n").map((line) => "  " + line));
        return lines.join("\n");
      }
      case "DoExpression":
        return [`do ${this.renderExpression(node.effect, scope)}:`, ...node.statements.map((statement) => "  " + statement.source)].join("\n");
    }
  }

  private renderCase(item: MatchCase, parent: Scope): string {
    const scope = new Map(parent);
    const pattern = this.renderPattern(item.pattern, scope);
    const body = item.body.kind === "Block" ? this.renderBlock(item.body, scope, "case").text : this.renderExpression(item.body, scope);
    return `case ${pattern}:\n${indent(body)}`;
  }

  private renderPattern(node: Pattern, scope: Scope): string {
    if (node.kind === "NamePattern") {
      if (node.name === "_") return "_";
      const symbol = scope.get(node.name);
      if (symbol?.kind === "constructor") return `${symbol.target}{}`;
      scope.set(node.name, { kind: "binding", target: node.name, span: node.span });
      return node.name;
    }
    const symbol = scope.get(node.constructor);
    const constructor = symbol?.kind === "constructor" ? symbol.target : node.constructor;
    return `${constructor}{${node.fields.map((field) => this.renderPattern(field, scope)).join(", ")}}`;
  }

  private renderType(node: Expression, scope: Scope): string {
    return this.renderExpression(node, scope);
  }

  private renderTypeParameters(fields: Field[], scope: Scope): string {
    if (!fields.length) return "";
    return `<${fields.map((field, index) => `${this.quantityMarker(field.quantity)}${field.name?.name ?? `T${index}`}: ${this.renderType(field.type, scope)}`).join(", ")}>`;
  }

  private freeBlockNames(block: Block): Set<string> {
    const names = new Set<string>();
    const visit = (node: Expression, bound = new Set<string>()): void => {
      switch (node.kind) {
        case "Identifier": if (!bound.has(node.name)) names.add(node.name); return;
        case "NumberExpression": case "StringExpression": return;
        case "ArrowExpression": visit(node.domain, bound); visit(node.codomain, bound); return;
        case "EqualityExpression": visit(node.left, bound); visit(node.right, bound); return;
        case "TypedEqualityExpression": visit(node.left, bound); visit(node.right, bound); visit(node.type, bound); return;
        case "AnnotationExpression": visit(node.value, bound); visit(node.type, bound); return;
        case "ReflexivityExpression": return;
        case "CallExpression": case "TypeApplicationExpression": case "ConstructorExpression":
          visit(node.callee, bound); node.arguments.forEach((item) => visit(item, bound)); return;
        case "TupleExpression": node.fields.forEach((field) => visit(field.type, bound)); return;
        case "UnionExpression": node.variants.forEach((variant) => variant.fields.forEach((field) => visit(field.type, bound))); return;
        case "MatchExpression":
          visit(node.scrutinee, bound);
          for (const item of node.cases) {
            const inner = new Set(bound);
            const bindPattern = (pattern: Pattern): void => {
              if (pattern.kind === "NamePattern") { if (pattern.name !== "_") inner.add(pattern.name); }
              else pattern.fields.forEach(bindPattern);
            };
            bindPattern(item.pattern);
            if (item.body.kind === "Block") visitBlock(item.body, inner); else visit(item.body, inner);
          }
          return;
        case "DoExpression":
          visit(node.effect, bound);
          for (const statement of node.statements) {
            for (const match of statement.source.matchAll(/[A-Za-z_][A-Za-z0-9_.]*/g)) if (!bound.has(match[0])) names.add(match[0]);
          }
          return;
      }
    };
    const visitBlock = (value: Block, inherited = new Set<string>()): void => {
      const bound = new Set(inherited);
      for (const statement of value.statements) {
        if (statement.kind === "ExpressionStatement") visit(statement.expression, bound);
        else if (statement.kind === "Declaration") {
          statement.typeParameters.forEach((field) => visit(field.type, bound));
          statement.parameters.forEach((field) => visit(field.type, bound));
          visit(statement.returnType, bound);
          if (statement.body.kind === "Block") visitBlock(statement.body, bound); else visit(statement.body, bound);
          bound.add(statement.name.name);
        }
      }
    };
    visitBlock(block);
    return names;
  }

  private quantityMarker(quantity: Field["quantity"] | Declaration["quantity"]): string {
    return quantity === "many" ? "+" : quantity === "none" ? "-" : quantity === "comptime" ? "~" : "";
  }

  private bindFields(fields: Field[], scope: Scope): void {
    for (const field of fields) if (field.name) scope.set(field.name.name, { kind: "binding", target: field.name.name, span: field.name.span, type: field.type, quantity: field.quantity });
  }

  private inferEqualityType(left: Expression, right: Expression, scope: Scope): string {
    for (const side of [left, right]) {
      if (side.kind === "Identifier") {
        const type = scope.get(side.name)?.type;
        if (type) return this.renderType(type, scope);
      }
      if (side.kind === "NumberExpression") return side.value.endsWith("n") ? "Nat" : side.value.includes(".") ? "F32" : "U32";
      if (side.kind === "StringExpression") return "String";
    }
    return "Type";
  }

  private expressionType(node: Expression, scope: Scope): string | null {
    if (node.kind === "Identifier") {
      const type = scope.get(node.name)?.type;
      return type ? this.renderType(type, scope) : null;
    }
    if (node.kind === "StringExpression") return "String";
    if (node.kind === "NumberExpression") return node.value.endsWith("n") ? "Nat" : node.value.includes(".") ? "F32" : "U32";
    return null;
  }
}

export function lowerFlow(source: string): LoweredFlow {
  return new FlowLowerer(parseFlow(source)).lower();
}

export function originalFlowSpan(lowered: LoweredFlow, generatedOffset: number): Span | null {
  const containing = lowered.mappings
    .filter((mapping) => mapping.generatedStart <= generatedOffset && generatedOffset <= mapping.generatedEnd)
    .sort((left, right) => (left.generatedEnd - left.generatedStart) - (right.generatedEnd - right.generatedStart))[0];
  if (containing) return { start: containing.flowStart, end: containing.flowEnd };
  const nearest = lowered.mappings
    .slice()
    .sort((left, right) => Math.abs(left.generatedStart - generatedOffset) - Math.abs(right.generatedStart - generatedOffset))[0];
  return nearest ? { start: nearest.flowStart, end: nearest.flowEnd } : null;
}
