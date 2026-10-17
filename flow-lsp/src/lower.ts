import type { Block, Declaration, Expression, Field, MatchCase, MatchExpression, Pattern, Program, Quantity, Span, Statement, UnionExpression } from "./ast.js";
import { parseFlow } from "./parser.js";

export type FlowSourceMapping = {
  generatedStart: number;
  generatedEnd: number;
  flowStart: number;
  flowEnd: number;
};

export type LoweredFlow = { bend: string; mappings: FlowSourceMapping[]; program: Program };
type SymbolKind = "type" | "function" | "value" | "constructor" | "binding" | "local";
type Symbol = { kind: SymbolKind; target: string; span: Span; type?: Expression; owner?: string; quantity?: Quantity; fieldTypes?: Expression[] };
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

function escapeRegExp(value: string): string {
  return value.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

export class FlowLowerer {
  private readonly imports: Snippet[] = [];
  private readonly regular: Snippet[] = [];
  private readonly global: Scope = new Map();
  private hasBaseImport = false;
  private nextMatchHelper = 0;
  private readonly expectedTypes: string[] = [];
  private readonly expectedTypeNodes: Expression[] = [];

  constructor(private readonly program: Program) {}

  lower(): LoweredFlow {
    for (const statement of this.program.statements) this.lowerTopStatement(statement);
    const output = new Writer();
    if (this.hasBaseImport) output.line("import Base");
    for (const imported of this.imports) append(output, imported);
    if (this.hasBaseImport || this.imports.length) output.line();
    for (const snippet of this.regular) {
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
    if (statement.kind === "PatternDeclaration") throw new Error("Flow destructuring declarations must be inside a definition");
    const type = this.expressionType(statement.expression, this.global) ?? "Type";
    const writer = new Writer();
    writer.line(`def main() -> ${type}:`, statement.span);
    writer.line("  " + this.renderExpression(statement.expression, this.global), statement.expression.span);
    this.regular.push({ text: writer.text, mappings: writer.mappings });
  }

  private lowerDeclaration(node: Declaration, target: string, outer: Scope, nested: boolean): void {
    const returnsKind = node.returnType.kind === "Identifier" && (node.returnType.name === "Type" || node.returnType.name === "Data")
      || node.returnType.kind === "CallExpression" && node.returnType.callee.kind === "Identifier" && node.returnType.callee.name === "Kind";
    const typeDeclaration = returnsKind && (node.body.kind === "UnionExpression" || node.body.kind === "TupleExpression");
    const kind: SymbolKind = typeDeclaration ? "type" : node.parameters.length ? "function" : "value";
    outer.set(node.name.name, { kind, target, span: node.name.span, type: node.returnType });
    const scope = new Map(outer);
    this.bindFields(node.typeParameters, scope);
    this.bindFields(node.parameters, scope);
    const snippet = typeDeclaration
      ? this.lowerTypeDeclaration(node, target, scope, outer)
      : this.lowerValueDeclaration(node, target, scope);
    this.regular.push(snippet);
  }

  private lowerTypeDeclaration(node: Declaration, target: string, scope: Scope, outer: Scope): Snippet {
    const writer = new Writer();
    const parameters = this.renderTypeParameters(node.typeParameters, scope);
    writer.write("type "); writer.write(target, node.name.span); writer.write(parameters);
    writer.write(" is "); writer.write(this.renderExpression(node.returnType, scope), node.returnType.span); writer.line(":");
    if (node.body.kind === "UnionExpression") {
      for (const variant of node.body.variants) {
        const constructor = target.includes(".") ? `${target}.${variant.name.name}` : variant.name.name;
        const constructorSymbol: Symbol = { kind: "constructor", target: constructor, owner: target, span: variant.name.span, fieldTypes: variant.fields.map((field) => field.type) };
        outer.set(variant.name.name, constructorSymbol);
        scope.set(variant.name.name, constructorSymbol);
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
    const expectedType = this.renderType(node.returnType, scope);
    if (node.body.kind === "Block") {
      const body = this.renderBlock(node.body, scope, target, expectedType, node.returnType);
      writer.write(indent(body.text), node.body.span);
      if (!writer.text.endsWith("\n")) writer.line();
    } else {
      writer.line("  " + this.renderExpected(node.body, scope, expectedType, node.returnType), node.body.span);
    }
    return { text: writer.text, mappings: writer.mappings };
  }

  private renderBlock(block: Block, parent: Scope, owner: string, expectedType?: string, expectedTypeNode?: Expression): Snippet {
    const writer = new Writer();
    const scope = new Map(parent);
    for (const statement of block.statements) {
      if (statement.kind === "ImportStatement") {
        throw new Error("Flow imports must be at the top level");
      } else if (statement.kind === "RawBendDefinition") {
        writer.line(statement.source, statement.span);
      } else if (statement.kind === "ExpressionStatement") {
        const isLast = statement === block.statements.at(-1);
        writer.line(isLast && expectedType
          ? this.renderExpected(statement.expression, scope, expectedType, expectedTypeNode)
          : this.renderExpression(statement.expression, scope), statement.span);
      } else if (statement.kind === "PatternDeclaration") {
        const valueType = this.expressionTypeNode(statement.value, scope);
        const value = this.renderExpression(statement.value, scope);
        const pattern = this.renderPattern(statement.pattern, scope, valueType);
        writer.line(`${pattern} = ${value}`, statement.span);
      } else {
        const needsLift = statement.parameters.length > 0 || statement.body.kind === "UnionExpression" || statement.body.kind === "TupleExpression";
        if (needsLift) {
          const target = `${owner}.${statement.name.name}`;
          this.lowerDeclaration(statement, target, scope, true);
        } else {
          scope.set(statement.name.name, { kind: "local", target: statement.name.name, span: statement.name.span, type: statement.returnType, quantity: statement.quantity });
          writer.write(this.quantityMarker(statement.quantity), statement.quantitySpan); writer.write(statement.name.name, statement.name.span); writer.write(": ");
          writer.write(this.renderType(statement.returnType, scope), statement.returnType.span); writer.write(" = ");
          if (statement.body.kind === "Block") {
            const helper = `${owner}.${statement.name.name}`;
            const free = this.freeBlockNames(statement.body);
            const captures = [...scope.entries()].filter(([name, symbol]) => name !== statement.name.name && free.has(name) && (symbol.kind === "binding" || symbol.kind === "local") && symbol.type);
            const lifted = new Writer();
            lifted.write("def "); lifted.write(helper, statement.name.span); lifted.write("(");
            captures.forEach(([name, symbol], index) => {
              if (index) lifted.write(", ");
              lifted.write(this.quantityMarker(symbol.quantity ?? "lone")); lifted.write(name, symbol.span); lifted.write(": ");
              lifted.write(this.renderType(symbol.type as Expression, scope), symbol.type?.span);
            });
            lifted.write(") -> "); lifted.write(this.renderType(statement.returnType, scope), statement.returnType.span); lifted.line(":");
            const nested = this.renderBlock(statement.body, scope, helper, this.renderType(statement.returnType, scope), statement.returnType);
            lifted.write(indent(nested.text), statement.body.span);
            if (!lifted.text.endsWith("\n")) lifted.line();
            this.regular.push({ text: lifted.text, mappings: lifted.mappings });
            writer.line(`${helper}(${captures.map(([name]) => name).join(", ")})`, statement.body.span);
          } else {
            writer.line(this.renderExpected(statement.body, scope, this.renderType(statement.returnType, scope), statement.returnType), statement.body.span);
          }
        }
      }
    }
    return { text: writer.text, mappings: writer.mappings };
  }

  private renderExpected(node: Expression, scope: Scope, type: string, typeNode?: Expression): string {
    this.expectedTypes.push(type);
    if (typeNode) this.expectedTypeNodes.push(typeNode);
    try { return this.renderExpression(node, scope); } finally {
      this.expectedTypes.pop();
      if (typeNode) this.expectedTypeNodes.pop();
    }
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
      case "QuantExpression": return node.value;
      case "PrefixQuantityExpression": return `${this.quantityMarker(node.quantity)}${this.renderExpression(node.value, scope)}`;
      case "StringExpression": return node.raw;
      case "ListExpression": return `[${node.values.map((value) => this.renderExpression(value, scope)).join(", ")}]`;
      case "ArrayExpression": return `[${this.renderExpression(node.value, scope)} : ${this.renderType(node.type, scope)}${node.mode === "count" ? "*" : "^"}${this.renderExpression(node.size, scope)}]`;
      case "IndexExpression": return `${this.renderExpression(node.target, scope)}[${this.renderExpression(node.index, scope)}]`;
      case "ArraySetExpression": return `${this.renderExpression(node.target, scope)}[${this.renderExpression(node.index, scope)}] <- ${this.renderExpression(node.value, scope)}`;
      case "RewriteExpression": return `%${this.renderExpression(node.proof, scope)} : ${this.renderExpression(node.motive, scope)}; ${this.renderExpression(node.value, scope)}`;
      case "ArrowExpression": {
        if (node.domain.kind === "TupleExpression" && node.domain.fields.length > 0 && node.domain.fields.every((field) => field.name)) {
          const binders = node.domain.fields.map((field) =>
            `@${this.quantityMarker(field.quantity)}${field.name!.name}: ${this.renderType(field.type, scope)} -> `
          ).join("");
          return binders + this.renderExpression(node.codomain, scope);
        }
        return `${this.renderExpression(node.domain, scope)} -> ${this.renderExpression(node.codomain, scope)}`;
      }
      case "EqualityExpression": {
        const type = this.inferEqualityType(node.left, node.right, scope);
        return `{${this.renderExpression(node.left, scope)} == ${this.renderExpression(node.right, scope)} : ${type}}`;
      }
      case "BinaryExpression": return `${this.renderExpression(node.left, scope)} ${node.operator} ${this.renderExpression(node.right, scope)}`;
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
        const symbol = node.scrutinee.kind === "Identifier" ? scope.get(node.scrutinee.name) : undefined;
        if (node.scrutinee.kind === "Identifier" && symbol?.kind === "binding") {
          return this.renderMatch(node, scope);
        }

        // Bend only permits a parameter or constructor field as a match
        // scrutinee. Lift a computed scrutinee into a helper parameter so Flow
        // can accept calls, constructors, annotations, and other expressions.
        const scrutineeType = this.expressionType(node.scrutinee, scope);
        const resultType = this.expectedTypes.at(-1) ?? this.matchResultType(node, scope) ?? null;
        if (!scrutineeType || !resultType) return this.renderMatch(node, scope);

        const id = this.nextMatchHelper++;
        const helper = `__flow_match_${id}`;
        const value = `__flow_match_value_${id}`;
        const free = this.freeMatchNames(node);
        const typeNames = `${scrutineeType} ${resultType}`;
        const captures = [...scope.entries()].filter(([name, item]) =>
          (item.kind === "binding" || item.kind === "local") && item.type
          && (free.has(name) || new RegExp(`\\b${escapeRegExp(name)}\\b`).test(typeNames))
        );
        const helperScope: Scope = new Map([...scope].filter(([, item]) => item.kind !== "binding" && item.kind !== "local"));
        helperScope.set(value, { kind: "binding", target: value, span: node.scrutinee.span });
        for (const [name, item] of captures) helperScope.set(name, item);

        const writer = new Writer();
        writer.write(`def ${helper}(`);
        for (const [name, item] of captures) {
          writer.write(`${this.quantityMarker(item.quantity ?? "lone")}${name}: ${this.renderType(item.type!, scope)}, `);
        }
        writer.write(`${value}: ${scrutineeType}`);
        writer.line(`) -> ${resultType}:`);
        const lifted: MatchExpression = {
          ...node,
          scrutinee: { kind: "Identifier", name: value, span: node.scrutinee.span },
        };
        writer.write(indent(this.renderMatch(lifted, helperScope)), node.span);
        writer.line();
        this.regular.push({ text: writer.text, mappings: writer.mappings });

        const arguments_ = [...captures.map(([, item]) => item.target), this.renderExpression(node.scrutinee, scope)];
        return `${helper}(${arguments_.join(", ")})`;
      }
      case "DoExpression":
        return [`do ${this.renderExpression(node.effect, scope)}:`, ...node.statements.map((statement) => "  " + statement.source)].join("\n");
    }
  }

  private renderMatch(node: MatchExpression, scope: Scope): string {
    const lines = [`match ${this.renderExpression(node.scrutinee, scope)}:`];
    const scrutineeType = this.expressionTypeNode(node.scrutinee, scope);
    for (const item of node.cases) lines.push(...this.renderCase(item, scope, scrutineeType).split("\n").map((line) => "  " + line));
    return lines.join("\n");
  }

  private renderCase(item: MatchCase, parent: Scope, scrutineeType?: Expression): string {
    const scope = new Map(parent);
    const pattern = this.renderPattern(item.pattern, scope, scrutineeType);
    const body = item.body.kind === "Block" ? this.renderBlock(item.body, scope, "case").text : this.renderExpression(item.body, scope);
    return `case ${pattern}:\n${indent(body)}`;
  }

  private renderPattern(node: Pattern, scope: Scope, type?: Expression): string {
    if (node.kind === "NamePattern") {
      if (node.name === "_") return "_";
      const symbol = scope.get(node.name);
      if (symbol?.kind === "constructor") return `${symbol.target}{}`;
      scope.set(node.name, { kind: "binding", target: node.name, span: node.span, type, quantity: node.quantity });
      return `${this.quantityMarker(node.quantity ?? "lone")}${node.name}`;
    }
    if (node.kind === "LiteralPattern") return node.raw;
    if (node.kind === "NatAddPattern") return `${node.amount}+${this.renderPattern(node.rest, scope, type)}`;
    const symbol = scope.get(node.constructor);
    const constructor = symbol?.kind === "constructor" ? symbol.target : node.constructor;
    const fieldTypes = node.constructor === "Tuple" && type?.kind === "BinaryExpression" && type.operator === "&"
      ? [type.left, type.right]
      : symbol?.fieldTypes ?? [];
    return `${constructor}{${node.fields.map((field, index) => this.renderPattern(field, scope, fieldTypes[index])).join(", ")}}`;
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
        case "NumberExpression": case "QuantExpression": case "StringExpression": return;
        case "PrefixQuantityExpression": visit(node.value, bound); return;
        case "ListExpression": node.values.forEach((value) => visit(value, bound)); return;
        case "ArrayExpression": visit(node.value, bound); visit(node.type, bound); visit(node.size, bound); return;
        case "IndexExpression": visit(node.target, bound); visit(node.index, bound); return;
        case "ArraySetExpression": visit(node.target, bound); visit(node.index, bound); visit(node.value, bound); return;
        case "RewriteExpression": visit(node.proof, bound); visit(node.motive, bound); visit(node.value, bound); return;
        case "ArrowExpression": visit(node.domain, bound); visit(node.codomain, bound); return;
        case "EqualityExpression": case "BinaryExpression": visit(node.left, bound); visit(node.right, bound); return;
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
              else if (pattern.kind === "ConstructorPattern") pattern.fields.forEach(bindPattern);
              else if (pattern.kind === "NatAddPattern") bindPattern(pattern.rest);
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
        else if (statement.kind === "PatternDeclaration") {
          visit(statement.value, bound);
          const bind = (pattern: Pattern): void => {
            if (pattern.kind === "NamePattern") { if (pattern.name !== "_") bound.add(pattern.name); }
            else if (pattern.kind === "ConstructorPattern") pattern.fields.forEach(bind);
            else if (pattern.kind === "NatAddPattern") bind(pattern.rest);
          };
          bind(statement.pattern);
        } else if (statement.kind === "Declaration") {
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

  private freeMatchNames(node: MatchExpression): Set<string> {
    const names = new Set<string>();
    const visit = (expression: Expression, bound: Set<string>): void => {
      switch (expression.kind) {
        case "Identifier": if (!bound.has(expression.name)) names.add(expression.name); return;
        case "NumberExpression": case "QuantExpression": case "StringExpression": case "ReflexivityExpression": return;
        case "PrefixQuantityExpression": visit(expression.value, bound); return;
        case "ListExpression": expression.values.forEach((value) => visit(value, bound)); return;
        case "ArrayExpression": visit(expression.value, bound); visit(expression.type, bound); visit(expression.size, bound); return;
        case "IndexExpression": visit(expression.target, bound); visit(expression.index, bound); return;
        case "ArraySetExpression": visit(expression.target, bound); visit(expression.index, bound); visit(expression.value, bound); return;
        case "RewriteExpression": visit(expression.proof, bound); visit(expression.motive, bound); visit(expression.value, bound); return;
        case "ArrowExpression": visit(expression.domain, bound); visit(expression.codomain, bound); return;
        case "EqualityExpression": case "BinaryExpression": visit(expression.left, bound); visit(expression.right, bound); return;
        case "TypedEqualityExpression": visit(expression.left, bound); visit(expression.right, bound); visit(expression.type, bound); return;
        case "AnnotationExpression": visit(expression.value, bound); visit(expression.type, bound); return;
        case "CallExpression": case "TypeApplicationExpression": case "ConstructorExpression":
          visit(expression.callee, bound); expression.arguments.forEach((item) => visit(item, bound)); return;
        case "TupleExpression": expression.fields.forEach((field) => visit(field.type, bound)); return;
        case "UnionExpression": expression.variants.forEach((variant) => variant.fields.forEach((field) => visit(field.type, bound))); return;
        case "MatchExpression":
          visit(expression.scrutinee, bound);
          for (const item of expression.cases) visitCase(item, bound);
          return;
        case "DoExpression":
          visit(expression.effect, bound);
          for (const statement of expression.statements) {
            for (const match of statement.source.matchAll(/[A-Za-z_][A-Za-z0-9_.]*/g)) if (!bound.has(match[0])) names.add(match[0]);
          }
          return;
      }
    };
    const bindPattern = (pattern: Pattern, bound: Set<string>): void => {
      if (pattern.kind === "NamePattern") { if (pattern.name !== "_") bound.add(pattern.name); }
      else if (pattern.kind === "ConstructorPattern") pattern.fields.forEach((field) => bindPattern(field, bound));
      else if (pattern.kind === "NatAddPattern") bindPattern(pattern.rest, bound);
    };
    const visitBlock = (block: Block, inherited: Set<string>): void => {
      const bound = new Set(inherited);
      for (const statement of block.statements) {
        if (statement.kind === "ExpressionStatement") {
          visit(statement.expression, bound);
        } else if (statement.kind === "PatternDeclaration") {
          visit(statement.value, bound);
          bindPattern(statement.pattern, bound);
        } else if (statement.kind === "Declaration") {
          statement.typeParameters.forEach((field) => visit(field.type, bound));
          statement.parameters.forEach((field) => visit(field.type, bound));
          visit(statement.returnType, bound);
          const bodyBound = new Set(bound).add(statement.name.name);
          if (statement.body.kind === "Block") visitBlock(statement.body, bodyBound);
          else visit(statement.body, bodyBound);
          bound.add(statement.name.name);
        }
      }
    };
    const visitCase = (item: MatchCase, inherited: Set<string>): void => {
      const bound = new Set(inherited);
      bindPattern(item.pattern, bound);
      if (item.body.kind === "Block") visitBlock(item.body, bound);
      else visit(item.body, bound);
    };
    for (const item of node.cases) visitCase(item, new Set());
    return names;
  }

  private matchResultType(node: MatchExpression, scope: Scope): string | null {
    for (const item of node.cases) {
      const body = item.body;
      if (body.kind !== "Block") {
        const type = this.expressionType(body, scope);
        if (type) return type;
        continue;
      }
      const last = body.statements.at(-1);
      if (last?.kind === "ExpressionStatement") {
        const type = this.expressionType(last.expression, scope);
        if (type) return type;
      } else if (last?.kind === "Declaration") {
        return this.renderType(last.returnType, scope);
      }
    }
    return null;
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

  private expressionTypeNode(node: Expression, scope: Scope): Expression | undefined {
    if (node.kind === "Identifier") return scope.get(node.name)?.type;
    if (node.kind === "AnnotationExpression") return node.type;
    if (node.kind === "RewriteExpression" || node.kind === "PrefixQuantityExpression") return this.expressionTypeNode(node.value, scope);
    if (node.kind === "CallExpression") {
      let callee = node.callee;
      if (callee.kind === "TypeApplicationExpression") callee = callee.callee;
      if (callee.kind === "Identifier") return scope.get(callee.name)?.type;
    }
    return undefined;
  }

  private expressionType(node: Expression, scope: Scope): string | null {
    if (node.kind === "Identifier") {
      const type = scope.get(node.name)?.type;
      return type ? this.renderType(type, scope) : null;
    }
    if (node.kind === "StringExpression") return "String";
    if (node.kind === "QuantExpression") return "Quant";
    if (node.kind === "PrefixQuantityExpression") return this.expressionType(node.value, scope);
    if (node.kind === "ArrayExpression") return `Array<${this.renderType(node.type, scope)}>`;
    if (node.kind === "IndexExpression") return "U32";
    if (node.kind === "ArraySetExpression") return this.expressionType(node.target, scope);
    if (node.kind === "RewriteExpression") return this.expressionType(node.value, scope);
    if (node.kind === "NumberExpression") return node.value.endsWith("n") ? "Nat" : node.value.includes(".") ? "F32" : "U32";
    if (node.kind === "AnnotationExpression") return this.renderType(node.type, scope);
    if (node.kind === "CallExpression") {
      let callee = node.callee;
      if (callee.kind === "TypeApplicationExpression") callee = callee.callee;
      if (callee.kind === "Identifier") {
        const type = scope.get(callee.name)?.type;
        return type ? this.renderType(type, scope) : null;
      }
      return null;
    }
    if (node.kind === "ConstructorExpression") {
      let callee = node.callee;
      let arguments_: Expression[] = [];
      if (callee.kind === "TypeApplicationExpression") {
        arguments_ = callee.arguments;
        callee = callee.callee;
      }
      if (callee.kind !== "Identifier") return null;
      const owner = scope.get(callee.name)?.owner;
      return owner ? `${owner}${arguments_.length ? `<${arguments_.map((item) => this.renderType(item, scope)).join(", ")}>` : ""}` : null;
    }
    if (node.kind === "MatchExpression") return this.matchResultType(node, scope);
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
