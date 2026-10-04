import type {
  Block,
  Declaration,
  Expression,
  Field,
  MatchCase,
  Pattern,
  Program,
  Span,
  Statement,
  UnionExpression,
} from "./ast.js";
import { parseFlow } from "./parser.js";

export type FlowDefinition = { start: number; end: number };
type SymbolKind = "declaration" | "constructor" | "binding";
type Symbol = { kind: SymbolKind; definition: FlowDefinition };
type Occurrence = Span & { definition: FlowDefinition };
type Scope = Map<string, Symbol>;

function childScope(scope: Scope): Scope {
  return new Map(scope);
}

function definition(span: Span): FlowDefinition {
  return { start: span.start, end: span.end };
}

class NavigationBuilder {
  readonly occurrences: Occurrence[] = [];

  build(program: Program): Occurrence[] {
    this.visitStatements(program.statements, new Map());
    return this.occurrences;
  }

  private bind(scope: Scope, name: string, span: Span, kind: SymbolKind): void {
    const target = definition(span);
    scope.set(name, { kind, definition: target });
    this.occurrences.push({ ...span, definition: target });
  }

  private reference(scope: Scope, name: string, span: Span): void {
    const symbol = scope.get(name);
    if (symbol) this.occurrences.push({ ...span, definition: symbol.definition });
  }

  private visitStatements(statements: Statement[], scope: Scope): void {
    for (const statement of statements) this.visitStatement(statement, scope);
  }

  private visitStatement(statement: Statement, scope: Scope): void {
    switch (statement.kind) {
      case "ImportStatement":
        if (statement.alias) this.bind(scope, statement.alias.name, statement.alias.span, "declaration");
        return;
      case "Declaration": this.visitDeclaration(statement, scope); return;
      case "ExpressionStatement": this.visitExpression(statement.expression, scope); return;
      case "RawBendDefinition": {
        const declaration = /^\s*(?:@unsafe\s+)?(?:def|law|type)\s+([A-Za-z_][A-Za-z0-9_.]*)/m.exec(statement.source);
        if (declaration) {
          const start = statement.span.start + declaration.index + declaration[0].lastIndexOf(declaration[1]);
          this.bind(scope, declaration[1], { start, end: start + declaration[1].length }, "declaration");
        }
      }
    }
  }

  private visitDeclaration(node: Declaration, outer: Scope): void {
    this.bind(outer, node.name.name, node.name.span, "declaration");
    const scope = childScope(outer);
    this.visitFields(node.typeParameters, scope, true);
    this.visitFields(node.parameters, scope, true);
    this.visitExpression(node.returnType, scope);
    this.visitBody(node.body, scope);
    if (node.body.kind === "UnionExpression") {
      for (const variant of node.body.variants) this.bind(outer, variant.name.name, variant.name.span, "constructor");
    }
  }

  private visitFields(fields: Field[], scope: Scope, bindNames: boolean): void {
    for (const field of fields) {
      this.visitExpression(field.type, scope);
      if (bindNames && field.name) this.bind(scope, field.name.name, field.name.span, "binding");
    }
  }

  private visitBody(body: Expression | Block, scope: Scope): void {
    if (body.kind === "Block") this.visitStatements(body.statements, childScope(scope));
    else this.visitExpression(body, scope);
  }

  private visitExpression(node: Expression, scope: Scope): void {
    switch (node.kind) {
      case "Identifier": this.reference(scope, node.name, node.span); return;
      case "NumberExpression": case "StringExpression": return;
      case "ArrowExpression": this.visitExpression(node.domain, scope); this.visitExpression(node.codomain, scope); return;
      case "EqualityExpression": this.visitExpression(node.left, scope); this.visitExpression(node.right, scope); return;
      case "TypedEqualityExpression": this.visitExpression(node.left, scope); this.visitExpression(node.right, scope); this.visitExpression(node.type, scope); return;
      case "AnnotationExpression": this.visitExpression(node.value, scope); this.visitExpression(node.type, scope); return;
      case "ReflexivityExpression": return;
      case "CallExpression":
      case "TypeApplicationExpression":
      case "ConstructorExpression":
        this.visitExpression(node.callee, scope);
        node.arguments.forEach((argument) => this.visitExpression(argument, scope));
        return;
      case "TupleExpression": {
        const tupleScope = childScope(scope);
        this.visitFields(node.fields, tupleScope, true);
        return;
      }
      case "UnionExpression": this.visitUnion(node, scope); return;
      case "MatchExpression":
        this.visitExpression(node.scrutinee, scope);
        node.cases.forEach((item) => this.visitCase(item, scope));
        return;
      case "DoExpression": {
        this.visitExpression(node.effect, scope);
        const doScope = childScope(scope);
        for (const statement of node.statements) {
          const binding = /^([A-Za-z_]\w*)\s*(?::[^<=>]+)?\s*(?:<-|=(?!=))/.exec(statement.source);
          for (const match of statement.source.matchAll(/[A-Za-z_][A-Za-z0-9_.]*/g)) {
            if (binding && match.index === binding.index) continue;
            this.reference(doScope, match[0], { start: statement.span.start + match.index, end: statement.span.start + match.index + match[0].length });
          }
          if (binding) {
            const start = statement.span.start + binding.index;
            this.bind(doScope, binding[1], { start, end: start + binding[1].length }, "binding");
          }
        }
        return;
      }
    }
  }

  private visitUnion(node: UnionExpression, scope: Scope): void {
    for (const variant of node.variants) {
      const fieldScope = childScope(scope);
      this.visitFields(variant.fields, fieldScope, true);
    }
  }

  private visitCase(node: MatchCase, outer: Scope): void {
    const scope = childScope(outer);
    this.visitPattern(node.pattern, scope);
    this.visitBody(node.body, scope);
  }

  private visitPattern(node: Pattern, scope: Scope): void {
    if (node.kind === "ConstructorPattern") {
      this.reference(scope, node.constructor, this.constructorNameSpan(node.span, node.constructor));
      node.typeArguments.forEach((argument) => this.visitExpression(argument, scope));
      node.fields.forEach((field) => this.visitPattern(field, scope));
      return;
    }
    if (node.name === "_") return;
    const existing = scope.get(node.name);
    if (existing?.kind === "constructor") this.reference(scope, node.name, node.span);
    else this.bind(scope, node.name, node.span, "binding");
  }

  private constructorNameSpan(span: Span, name: string): Span {
    return { start: span.start, end: Math.min(span.end, span.start + name.length) };
  }
}

export function flowOccurrences(program: Program): Occurrence[] {
  return new NavigationBuilder().build(program);
}

export function flowDefinitionAt(source: string, offset: number): FlowDefinition | null {
  const occurrences = flowOccurrences(parseFlow(source));
  const found = occurrences
    .filter((item) => item.start <= offset && offset <= item.end)
    .sort((left, right) => (left.end - left.start) - (right.end - right.start))[0];
  return found?.definition ?? null;
}
