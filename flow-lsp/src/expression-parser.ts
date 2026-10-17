import type {
  ConstructorExpression,
  Expression,
  Field,
  Identifier,
  Pattern,
  Quantity,
  Span,
  Variant,
} from "./ast.js";

export class FlowParseError extends Error {
  constructor(message: string, public readonly span: Span) {
    super(message);
    this.name = "FlowParseError";
  }
}

type TokenKind = "name" | "number" | "quantity" | "string" | "symbol" | "eof";
type Token = { kind: TokenKind; text: string; start: number; end: number };

function tokenize(source: string, base: number): Token[] {
  const tokens: Token[] = [];
  let index = 0;
  while (index < source.length) {
    const char = source[index];
    if (/\s/.test(char)) { index++; continue; }
    if (char === "#") {
      while (index < source.length && source[index] !== "\n") index++;
      continue;
    }
    if (/[A-Za-z_]/.test(char)) {
      const match = /^[A-Za-z_][A-Za-z0-9_.]*/.exec(source.slice(index))!;
      tokens.push({ kind: "name", text: match[0], start: base + index, end: base + index + match[0].length });
      index += match[0].length;
      continue;
    }
    if (/[0-9]/.test(char)) {
      const match = /^(?:[0-9]+\.[0-9]+(?:[eE][+-]?[0-9]+)?|[0-9]+n?)/.exec(source.slice(index))!;
      tokens.push({ kind: "number", text: match[0], start: base + index, end: base + index + match[0].length });
      index += match[0].length;
      continue;
    }
    if (char === '"') {
      let end = index + 1;
      while (end < source.length && source[end] !== '"') {
        if (source[end] === "\\") end++;
        end++;
      }
      if (end >= source.length) throw new FlowParseError("Unterminated string literal", { start: base + index, end: base + source.length });
      end++;
      tokens.push({ kind: "string", text: source.slice(index, end), start: base + index, end: base + end });
      index = end;
      continue;
    }
    const triple = source.slice(index, index + 3);
    if (triple === "<&>") {
      tokens.push({ kind: "symbol", text: triple, start: base + index, end: base + index + 3 });
      index += 3;
      continue;
    }
    if (char === "&" && /^[012]$/.test(source[index + 1] ?? "")) {
      tokens.push({ kind: "quantity", text: source.slice(index, index + 2), start: base + index, end: base + index + 2 });
      index += 2;
      continue;
    }
    const pair = source.slice(index, index + 2);
    if (["->", "==", "=>", "<-", "<>"].includes(pair)) {
      tokens.push({ kind: "symbol", text: pair, start: base + index, end: base + index + 2 });
      index += 2;
      continue;
    }
    if ("(){}[]<>,:;|+-~&*^%".includes(char)) {
      tokens.push({ kind: "symbol", text: char, start: base + index, end: base + index + 1 });
      index++;
      continue;
    }
    throw new FlowParseError(`Unexpected character '${char}'`, { start: base + index, end: base + index + 1 });
  }
  tokens.push({ kind: "eof", text: "", start: base + source.length, end: base + source.length });
  return tokens;
}

export class ExpressionParser {
  private readonly tokens: Token[];
  private index = 0;

  constructor(source: string, baseOffset = 0) {
    this.tokens = tokenize(source, baseOffset);
  }

  current(): Token { return this.tokens[this.index]; }
  peek(distance = 1): Token { return this.tokens[Math.min(this.index + distance, this.tokens.length - 1)]; }

  take(text?: string): Token | null {
    const token = this.current();
    if (text !== undefined && token.text !== text) return null;
    this.index++;
    return token;
  }

  expect(text: string): Token {
    const token = this.take(text);
    if (!token) throw new FlowParseError(`Expected '${text}'`, { start: this.current().start, end: this.current().end });
    return token;
  }

  expectEnd(): void {
    if (this.current().kind !== "eof") {
      throw new FlowParseError(`Unexpected '${this.current().text}'`, { start: this.current().start, end: this.current().end });
    }
  }

  parse(): Expression {
    const expression = this.current().text === "|" ? this.parseUnion() : this.parseExpression();
    this.expectEnd();
    return expression;
  }

  parseExpression(minimumBindingPower = 0): Expression {
    let left = this.parsePrimary();
    while (true) {
      if (this.current().text === "[") {
        const start = left.span.start;
        this.index++;
        const index = this.parseExpression();
        const close = this.expect("]");
        if (this.take("<-")) {
          const value = this.parseExpression();
          left = { kind: "ArraySetExpression", target: left, index, value, span: { start, end: value.span.end } };
        } else {
          left = { kind: "IndexExpression", target: left, index, span: { start, end: close.end } };
        }
        continue;
      }
      if (this.current().text === "<") {
        const start = left.span.start;
        const arguments_ = this.parseDelimited("<", ">");
        left = { kind: "TypeApplicationExpression", callee: left, arguments: arguments_, span: { start, end: this.tokens[this.index - 1].end } };
        continue;
      }
      if (this.current().text === "(") {
        const start = left.span.start;
        const arguments_ = this.parseDelimited("(", ")");
        left = { kind: "CallExpression", callee: left, arguments: arguments_, span: { start, end: this.tokens[this.index - 1].end } };
        continue;
      }
      if (this.current().text === "{") {
        const start = left.span.start;
        const arguments_ = this.parseDelimited("{", "}");
        left = { kind: "ConstructorExpression", callee: left, arguments: arguments_, span: { start, end: this.tokens[this.index - 1].end } };
        continue;
      }
      const operator = this.current();
      const bindingPower = operator.text === "->" ? 1
        : operator.text === "&" ? 2
        : operator.text === "==" ? 3
        : operator.text === "<&>" ? 4
        : operator.text === "<>" ? 5
        : operator.text === "+" ? 10
        : -1;
      if (bindingPower < minimumBindingPower) break;
      this.index++;
      const rightAssociative = operator.text === "->" || operator.text === "&" || operator.text === "<&>" || operator.text === "<>";
      const right = this.parseExpression(rightAssociative ? bindingPower : bindingPower + 1);
      left = operator.text === "->"
        ? { kind: "ArrowExpression", domain: left, codomain: right, span: { start: left.span.start, end: right.span.end } }
        : operator.text === "=="
          ? { kind: "EqualityExpression", left, right, span: { start: left.span.start, end: right.span.end } }
          : { kind: "BinaryExpression", operator: operator.text as "&" | "<&>" | "<>" | "+", left, right, span: { start: left.span.start, end: right.span.end } };
    }
    return left;
  }

  parseFields(open: string, close: string): Field[] {
    this.expect(open);
    const fields: Field[] = [];
    while (this.current().text !== close) {
      if (this.current().kind === "eof") throw new FlowParseError(`Expected '${close}'`, { start: this.current().start, end: this.current().end });
      const start = this.current().start;
      const { quantity, span: quantitySpan } = this.parseQuantity();
      let name: Identifier | undefined;
      if (this.current().kind === "name" && this.peek().text === ":") {
        const token = this.take()!;
        name = { kind: "Identifier", name: token.text, span: { start: token.start, end: token.end } };
        this.expect(":");
      }
      const type = this.parseExpression();
      fields.push({ kind: "Field", name, quantity, quantitySpan, type, span: { start, end: type.span.end } });
      if (!this.take(",")) break;
    }
    this.expect(close);
    return fields;
  }

  parseUnion(): Expression {
    const variants: Variant[] = [];
    while (this.take("|")) {
      variants.push(this.parseVariant());
    }
    if (variants.length === 0) throw new FlowParseError("Expected a union variant", { start: this.current().start, end: this.current().end });
    return { kind: "UnionExpression", variants, span: { start: variants[0].span.start, end: variants.at(-1)!.span.end } };
  }

  parseVariant(): Variant {
    const nameToken = this.current();
    if (nameToken.kind !== "name") throw new FlowParseError("Expected a constructor name", { start: nameToken.start, end: nameToken.end });
    this.index++;
    const name: Identifier = { kind: "Identifier", name: nameToken.text, span: { start: nameToken.start, end: nameToken.end } };
    const fields = this.current().text === "{" ? this.parseFields("{", "}") : [];
    return { kind: "Variant", name, fields, span: { start: name.span.start, end: fields.at(-1)?.span.end ?? name.span.end } };
  }

  private parseQuantity(): { quantity: Quantity; span?: Span } {
    const token = this.current();
    const quantity: Quantity | undefined = token.text === "+" ? "many"
      : token.text === "-" ? "none"
      : token.text === "~" ? "comptime"
      : undefined;
    if (!quantity) return { quantity: "lone" };
    this.index++;
    return { quantity, span: { start: token.start, end: token.end } };
  }

  private parsePrimary(): Expression {
    const token = this.current();
    if (["+", "-", "~"].includes(token.text) && this.peek().kind === "name") {
      this.index++;
      const value = this.parsePrimary();
      const quantity: Quantity = token.text === "+" ? "many" : token.text === "-" ? "none" : "comptime";
      return {
        kind: "PrefixQuantityExpression",
        quantity,
        quantitySpan: { start: token.start, end: token.end },
        value,
        span: { start: token.start, end: value.span.end },
      };
    }
    if (token.kind === "name") {
      this.index++;
      return { kind: "Identifier", name: token.text, span: { start: token.start, end: token.end } };
    }
    if (token.kind === "number") {
      this.index++;
      return { kind: "NumberExpression", value: token.text, span: { start: token.start, end: token.end } };
    }
    if (token.kind === "quantity") {
      this.index++;
      return { kind: "QuantExpression", value: token.text as "&0" | "&1" | "&2", span: { start: token.start, end: token.end } };
    }
    if (token.kind === "string") {
      this.index++;
      let value: string;
      try { value = JSON.parse(token.text) as string; } catch { value = token.text.slice(1, -1); }
      return { kind: "StringExpression", value, raw: token.text, span: { start: token.start, end: token.end } };
    }
    if (this.take("%")) {
      const open = token;
      const proof = this.parseExpression();
      this.expect(":");
      const motive = this.parseExpression();
      this.expect(";");
      const value = this.parseExpression();
      return { kind: "RewriteExpression", proof, motive, value, span: { start: open.start, end: value.span.end } };
    }
    if (this.take("[")) {
      const open = token;
      if (this.take("]")) return { kind: "ListExpression", values: [], span: { start: open.start, end: this.tokens[this.index - 1].end } };
      const first = this.parseExpression();
      if (this.take(":")) {
        const type = this.parseExpression();
        const operator = this.current();
        if (!this.take("*") && !this.take("^")) throw new FlowParseError("Expected '*' or '^' in an array literal", { start: operator.start, end: operator.end });
        const size = this.parseExpression();
        const close = this.expect("]");
        return {
          kind: "ArrayExpression",
          value: first,
          type,
          size,
          mode: operator.text === "*" ? "count" : "depth",
          span: { start: open.start, end: close.end },
        };
      }
      const values = [first];
      while (this.take(",")) {
        if (this.current().text === "]") break;
        values.push(this.parseExpression());
      }
      const close = this.expect("]");
      return { kind: "ListExpression", values, span: { start: open.start, end: close.end } };
    }
    if (this.take("{")) {
      const open = token;
      if (this.take("==")) {
        const close = this.expect("}");
        return { kind: "ReflexivityExpression", span: { start: open.start, end: close.end } };
      }
      const value = this.parseExpression();
      this.expect(":");
      const type = this.parseExpression();
      const close = this.expect("}");
      if (value.kind === "EqualityExpression") {
        return { kind: "TypedEqualityExpression", left: value.left, right: value.right, type, span: { start: open.start, end: close.end } };
      }
      return { kind: "AnnotationExpression", value, type, span: { start: open.start, end: close.end } };
    }
    if (this.take("(")) {
      const open = token;
      const fields: Field[] = [];
      while (this.current().text !== ")") {
        const start = this.current().start;
        const { quantity, span: quantitySpan } = this.parseQuantity();
        let name: Identifier | undefined;
        if (this.current().kind === "name" && this.peek().text === ":") {
          const nameToken = this.take()!;
          name = { kind: "Identifier", name: nameToken.text, span: { start: nameToken.start, end: nameToken.end } };
          this.expect(":");
        }
        const type = this.parseExpression();
        fields.push({ kind: "Field", name, quantity, quantitySpan, type, span: { start, end: type.span.end } });
        if (!this.take(",")) break;
      }
      const close = this.expect(")");
      if (fields.length === 1 && !fields[0].name) return fields[0].type;
      return { kind: "TupleExpression", fields, span: { start: open.start, end: close.end } };
    }
    throw new FlowParseError("Expected an expression", { start: token.start, end: token.end });
  }

  private parseDelimited(open: string, close: string): Expression[] {
    this.expect(open);
    const values: Expression[] = [];
    while (this.current().text !== close) {
      values.push(this.parseExpression());
      if (!this.take(",")) break;
    }
    this.expect(close);
    return values;
  }
}

export function expressionToPattern(expression: Expression): Pattern {
  if (expression.kind === "PrefixQuantityExpression") {
    const pattern = expressionToPattern(expression.value);
    if (pattern.kind !== "NamePattern") throw new FlowParseError("A pattern quantity must modify a binder", expression.span);
    return { ...pattern, quantity: expression.quantity, quantitySpan: expression.quantitySpan };
  }
  if (expression.kind === "NumberExpression" || expression.kind === "StringExpression") {
    return { kind: "LiteralPattern", raw: expression.kind === "StringExpression" ? expression.raw : expression.value, span: expression.span };
  }
  if (expression.kind === "BinaryExpression" && expression.operator === "+"
    && expression.left.kind === "NumberExpression" && expression.left.value.endsWith("n")) {
    return {
      kind: "NatAddPattern",
      amount: expression.left.value,
      rest: expressionToPattern(expression.right),
      span: expression.span,
    };
  }
  if (expression.kind === "Identifier") {
    return { kind: "NamePattern", name: expression.name, span: expression.span };
  }
  if (expression.kind === "TupleExpression" && expression.fields.length > 1 && expression.fields.every((field) => !field.name)) {
    const [first, ...rest] = expression.fields;
    const tail = rest.length === 1 ? rest[0].type : {
      kind: "TupleExpression" as const,
      fields: rest,
      span: { start: rest[0].span.start, end: rest.at(-1)!.span.end },
    };
    return {
      kind: "ConstructorPattern",
      constructor: "Tuple",
      typeArguments: [],
      fields: [expressionToPattern(first.type), expressionToPattern(tail)],
      span: expression.span,
    };
  }
  if (expression.kind === "BinaryExpression" && expression.operator === "<>") {
    return {
      kind: "ConstructorPattern",
      constructor: "Con",
      typeArguments: [],
      fields: [expressionToPattern(expression.left), expressionToPattern(expression.right)],
      span: expression.span,
    };
  }
  if (expression.kind === "ConstructorExpression") {
    let callee: Expression = expression.callee;
    let typeArguments: Expression[] = [];
    if (callee.kind === "TypeApplicationExpression") {
      typeArguments = callee.arguments;
      callee = callee.callee;
    }
    if (callee.kind !== "Identifier") throw new FlowParseError("Expected a constructor name in pattern", expression.callee.span);
    return {
      kind: "ConstructorPattern",
      constructor: callee.name,
      typeArguments,
      fields: expression.arguments.map(expressionToPattern),
      span: expression.span,
    };
  }
  throw new FlowParseError("Expected a name or constructor pattern", expression.span);
}

export function constructorToVariant(expression: Expression): Variant {
  if (expression.kind === "Identifier") {
    return { kind: "Variant", name: expression, fields: [], span: expression.span };
  }
  const constructor = expression as ConstructorExpression;
  if (constructor.kind !== "ConstructorExpression" || constructor.callee.kind !== "Identifier") {
    throw new FlowParseError("Expected a constructor declaration", expression.span);
  }
  return {
    kind: "Variant",
    name: constructor.callee,
    fields: constructor.arguments.map((type) => ({ kind: "Field", quantity: "lone", type, span: type.span })),
    span: constructor.span,
  };
}
